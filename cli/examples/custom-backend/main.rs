// Copyright 2022 The Jujutsu Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::any::Any;
use std::fs;
use std::fs::File;
use std::io::Read;
use std::io::Write;
use std::path::Path;
use std::time::SystemTime;

use blake2::Blake2b512;

use async_trait::async_trait;
use blake2::Digest;
use futures::stream;
use futures::stream::BoxStream;
use jj_cli::cli_util::CliRunner;
use jj_cli::cli_util::CommandHelper;
use jj_cli::command_error::CommandError;
use jj_cli::ui::Ui;
use jj_lib::backend::make_root_commit;
use jj_lib::backend::Backend;
use jj_lib::backend::BackendError;
use jj_lib::backend::BackendInitError;
use jj_lib::backend::BackendLoadError;
use jj_lib::backend::BackendResult;
use jj_lib::backend::ChangeId;
use jj_lib::backend::Commit;
use jj_lib::backend::CommitId;
use jj_lib::backend::Conflict;
use jj_lib::backend::ConflictId;
use jj_lib::backend::ConflictTerm;
use jj_lib::backend::CopyRecord;
use jj_lib::backend::FileId;
use jj_lib::backend::MergedTreeId;
use jj_lib::backend::MillisSinceEpoch;
use jj_lib::backend::SecureSig;
use jj_lib::backend::Signature;
use jj_lib::backend::SigningFn;
use jj_lib::backend::SymlinkId;
use jj_lib::backend::Timestamp;
use jj_lib::backend::Tree;
use jj_lib::backend::TreeId;
use jj_lib::backend::TreeValue;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::file_util::persist_content_addressed_temp_file;
use jj_lib::git_backend::GitBackend;
use jj_lib::index::Index;
use jj_lib::local_backend::commit_to_proto;
use jj_lib::merge::MergeBuilder;
use jj_lib::object_id::ObjectId;
use jj_lib::protos::local_store::tree::Entry;
use jj_lib::repo::StoreFactories;
use jj_lib::repo_path::RepoPath;
use jj_lib::repo_path::RepoPathBuf;
use jj_lib::repo_path::RepoPathComponentBuf;
use jj_lib::settings::UserSettings;
use jj_lib::signing::Signer;
use jj_lib::workspace::Workspace;
use jj_lib::workspace::WorkspaceInitError;
use pollster::FutureExt;
use prost::Message;
use std::path::PathBuf;
use tempfile::NamedTempFile;

const COMMIT_ID_LENGTH: usize = 64;
const CHANGE_ID_LENGTH: usize = 16;

fn map_not_found_err(err: std::io::Error, id: &impl ObjectId) -> BackendError {
    if err.kind() == std::io::ErrorKind::NotFound {
        BackendError::ObjectNotFound {
            object_type: id.object_type(),
            hash: id.hex(),
            source: Box::new(err),
        }
    } else {
        BackendError::ReadObject {
            object_type: id.object_type(),
            hash: id.hex(),
            source: Box::new(err),
        }
    }
}

#[derive(clap::Parser, Clone, Debug)]
enum CustomCommand {
    /// Initialize a workspace using the Custom backend
    InitCustom,
    Push,
}
fn to_other_err(err: impl Into<Box<dyn std::error::Error + Send + Sync>>) -> BackendError {
    BackendError::Other(err.into())
}

fn conflict_term_to_proto(part: &ConflictTerm) -> jj_lib::protos::local_store::conflict::Term {
    jj_lib::protos::local_store::conflict::Term {
        content: Some(tree_value_to_proto(&part.value)),
    }
}
fn conflict_to_proto(conflict: &Conflict) -> jj_lib::protos::local_store::Conflict {
    let mut proto = jj_lib::protos::local_store::Conflict::default();
    for term in &conflict.removes {
        proto.removes.push(conflict_term_to_proto(term));
    }
    for term in &conflict.adds {
        proto.adds.push(conflict_term_to_proto(term));
    }
    proto
}

fn tree_value_to_proto(value: &TreeValue) -> jj_lib::protos::local_store::TreeValue {
    let mut proto = jj_lib::protos::local_store::TreeValue::default();
    match value {
        TreeValue::File { id, executable } => {
            proto.value = Some(jj_lib::protos::local_store::tree_value::Value::File(
                jj_lib::protos::local_store::tree_value::File {
                    id: id.to_bytes(),
                    executable: *executable,
                },
            ));
        }
        TreeValue::Symlink(id) => {
            proto.value = Some(jj_lib::protos::local_store::tree_value::Value::SymlinkId(
                id.to_bytes(),
            ));
        }
        TreeValue::GitSubmodule(_id) => {
            panic!("cannot store git submodules");
        }
        TreeValue::Tree(id) => {
            proto.value = Some(jj_lib::protos::local_store::tree_value::Value::TreeId(
                id.to_bytes(),
            ));
        }
        TreeValue::Conflict(id) => {
            proto.value = Some(jj_lib::protos::local_store::tree_value::Value::ConflictId(
                id.to_bytes(),
            ));
        }
    }
    proto
}

fn tree_from_proto(proto: jj_lib::protos::local_store::Tree) -> Tree {
    let mut tree = Tree::default();
    for proto_entry in proto.entries {
        let value = tree_value_from_proto(proto_entry.value.unwrap());
        tree.set(RepoPathComponentBuf::from(proto_entry.name), value);
    }
    tree
}

fn tree_to_proto(tree: &Tree) -> jj_lib::protos::local_store::Tree {
    let mut proto = jj_lib::protos::local_store::Tree::default();
    for entry in tree.entries() {
        proto.entries.push(Entry {
            name: entry.name().as_internal_str().to_owned(),
            value: Some(tree_value_to_proto(entry.value())),
        });
    }
    proto
}

fn signature_from_proto(proto: jj_lib::protos::local_store::commit::Signature) -> Signature {
    let timestamp = proto.timestamp.unwrap_or_default();
    Signature {
        name: proto.name,
        email: proto.email,
        timestamp: Timestamp {
            timestamp: MillisSinceEpoch(timestamp.millis_since_epoch),
            tz_offset: timestamp.tz_offset,
        },
    }
}
fn commit_from_proto(mut proto: jj_lib::protos::local_store::Commit) -> Commit {
    // Note how .take() sets the secure_sig field to None before we encode the data.
    // Needs to be done first since proto is partially moved a bunch below
    let secure_sig = proto.secure_sig.take().map(|sig| SecureSig {
        data: proto.encode_to_vec(),
        sig,
    });

    let parents = proto.parents.into_iter().map(CommitId::new).collect();
    let predecessors = proto.predecessors.into_iter().map(CommitId::new).collect();
    let root_tree = if proto.uses_tree_conflict_format {
        let merge_builder: MergeBuilder<_> = proto.root_tree.into_iter().map(TreeId::new).collect();
        MergedTreeId::Merge(merge_builder.build())
    } else {
        assert_eq!(proto.root_tree.len(), 1);
        MergedTreeId::Legacy(TreeId::new(proto.root_tree[0].clone()))
    };
    let change_id = ChangeId::new(proto.change_id);
    Commit {
        parents,
        predecessors,
        root_tree,
        change_id,
        description: proto.description,
        author: signature_from_proto(proto.author.unwrap_or_default()),
        committer: signature_from_proto(proto.committer.unwrap_or_default()),
        secure_sig,
    }
}

fn run_custom_command(
    ui: &mut Ui,
    command_helper: &CommandHelper,
    command: CustomCommand,
) -> Result<(), CommandError> {
    match command {
        CustomCommand::InitCustom => {
            let wc_path = command_helper.cwd();
            // Initialize a workspace with the custom backend
            Workspace::init_with_backend(
                command_helper.settings(),
                wc_path,
                &|_settings, store_path| {
                    println!("{:#?}", store_path);
                    return Ok(Box::new(CustomBackend::init(store_path)));
                },
                Signer::from_settings(command_helper.settings())
                    .map_err(WorkspaceInitError::SignInit)?,
            )?;
            Ok(())
        }
        CustomCommand::Push => {
            let mut workspace_command = command_helper.workspace_helper(ui)?;
            let store_path = workspace_command.repo_path().join("store");
            println!("I'm pushing! {:#?}", store_path);
            let backend = CustomBackend::load(store_path.as_path());
            println!("backend: {:#?}", backend);
            Ok(())
        }
    }
}
fn create_store_factories() -> StoreFactories {
    let mut store_factories = StoreFactories::empty();
    // Register the backend so it can be loaded when the repo is loaded. The name
    // must match `Backend::name()`.
    store_factories.add_backend(
        "custom",
        Box::new(|_settings, store_path| Ok(Box::new(CustomBackend::load(store_path)))),
    );
    store_factories
}

fn main() -> std::process::ExitCode {
    // tracing_subscriber::fmt::init();
    CliRunner::init()
        .add_store_factories(create_store_factories())
        .add_subcommand(run_custom_command)
        .run()
}

/// A commit backend that's extremely similar to the Git backend
#[derive(Debug)]
struct CustomBackend {
    path: PathBuf,
    root_commit_id: CommitId,
    root_change_id: ChangeId,
    empty_tree_id: TreeId,
}
fn tree_value_from_proto(proto: jj_lib::protos::local_store::TreeValue) -> TreeValue {
    match proto.value.unwrap() {
        jj_lib::protos::local_store::tree_value::Value::TreeId(id) => {
            TreeValue::Tree(TreeId::new(id))
        }
        jj_lib::protos::local_store::tree_value::Value::File(
            jj_lib::protos::local_store::tree_value::File { id, executable, .. },
        ) => TreeValue::File {
            id: FileId::new(id),
            executable,
        },
        jj_lib::protos::local_store::tree_value::Value::SymlinkId(id) => {
            TreeValue::Symlink(SymlinkId::new(id))
        }
        jj_lib::protos::local_store::tree_value::Value::ConflictId(id) => {
            TreeValue::Conflict(ConflictId::new(id))
        }
    }
}

fn conflict_term_from_proto(proto: jj_lib::protos::local_store::conflict::Term) -> ConflictTerm {
    ConflictTerm {
        value: tree_value_from_proto(proto.content.unwrap()),
    }
}

fn conflict_from_proto(proto: jj_lib::protos::local_store::Conflict) -> Conflict {
    let mut conflict = Conflict::default();
    for term in proto.removes {
        conflict.removes.push(conflict_term_from_proto(term));
    }
    for term in proto.adds {
        conflict.adds.push(conflict_term_from_proto(term));
    }
    conflict
}

impl CustomBackend {
    pub fn name() -> &'static str {
        "custom"
    }
    pub fn load(store_path: &Path) -> Self {
        println!("loading {:#?}", store_path);
        let root_commit_id = CommitId::from_bytes(&[0; COMMIT_ID_LENGTH]);
        let root_change_id = ChangeId::from_bytes(&[0; CHANGE_ID_LENGTH]);
        let empty_tree_id = TreeId::from_hex(
            "482ae5a29fbe856c7272f2071b8b0f0359ee2d89ff392b8a900643fbd0836eccd067b8bf41909e206c90d45d6e7d8b6686b93ecaee5fe1a9060d87b672101310",
        );
        CustomBackend {
            path: store_path.to_path_buf(),
            root_commit_id,
            root_change_id,
            empty_tree_id,
        }
    }

    fn file_path(&self, id: &FileId) -> PathBuf {
        self.path.join("files").join(id.hex())
    }

    fn symlink_path(&self, id: &SymlinkId) -> PathBuf {
        self.path.join("symlinks").join(id.hex())
    }

    fn tree_path(&self, id: &TreeId) -> PathBuf {
        self.path.join("trees").join(id.hex())
    }

    fn commit_path(&self, id: &CommitId) -> PathBuf {
        self.path.join("commits").join(id.hex())
    }

    fn conflict_path(&self, id: &ConflictId) -> PathBuf {
        self.path.join("conflicts").join(id.hex())
    }

    fn init(store_path: &Path) -> Self {
        fs::create_dir(store_path.join("commits")).unwrap();
        fs::create_dir(store_path.join("trees")).unwrap();
        fs::create_dir(store_path.join("files")).unwrap();
        fs::create_dir(store_path.join("symlinks")).unwrap();
        fs::create_dir(store_path.join("conflicts")).unwrap();
        let backend = Self::load(store_path);
        let empty_tree_id = backend
            .write_tree(RepoPath::root(), &Tree::default())
            .block_on()
            .unwrap();
        assert_eq!(empty_tree_id, backend.empty_tree_id);
        backend
    }

    // pub fn load(store_path: &Path) -> Self {
    //     let root_commit_id = CommitId::from_bytes(&[0; COMMIT_ID_LENGTH]);
    //     let root_change_id = ChangeId::from_bytes(&[0; CHANGE_ID_LENGTH]);
    //     let empty_tree_id = TreeId::from_hex(
    //         "482ae5a29fbe856c7272f2071b8b0f0359ee2d89ff392b8a900643fbd0836eccd067b8bf41909e206c90d45d6e7d8b6686b93ecaee5fe1a9060d87b672101310",
    //     );
    //     LocalBackend {
    //         path: store_path.to_path_buf(),
    //         root_commit_id,
    //         root_change_id,
    //         empty_tree_id,
    //     }
    // }
}

#[async_trait]
impl Backend for CustomBackend {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn name(&self) -> &str {
        Self::name()
    }

    fn commit_id_length(&self) -> usize {
        COMMIT_ID_LENGTH
    }

    fn change_id_length(&self) -> usize {
        CHANGE_ID_LENGTH
    }

    fn root_commit_id(&self) -> &CommitId {
        &self.root_commit_id
    }

    fn root_change_id(&self) -> &ChangeId {
        &self.root_change_id
    }

    fn empty_tree_id(&self) -> &TreeId {
        &self.empty_tree_id
    }

    fn concurrency(&self) -> usize {
        1
    }

    async fn read_file(&self, _path: &RepoPath, id: &FileId) -> BackendResult<Box<dyn Read>> {
        println!("reading file {:#?}", id);
        let path = self.file_path(id);
        let file = File::open(path).map_err(|err| map_not_found_err(err, id))?;
        Ok(Box::new(zstd::Decoder::new(file).map_err(to_other_err)?))
    }

    async fn write_file(
        &self,
        _path: &RepoPath,
        contents: &mut (dyn Read + Send),
    ) -> BackendResult<FileId> {
        let temp_file = NamedTempFile::new_in(&self.path).map_err(to_other_err)?;
        let mut encoder = zstd::Encoder::new(temp_file.as_file(), 0).map_err(to_other_err)?;
        let mut hasher = Blake2b512::new();
        let mut buff: Vec<u8> = vec![0; 1 << 14];
        loop {
            let bytes_read = contents.read(&mut buff).map_err(to_other_err)?;
            if bytes_read == 0 {
                break;
            }
            let bytes = &buff[..bytes_read];
            encoder.write_all(bytes).map_err(to_other_err)?;
            hasher.update(bytes);
        }
        encoder.finish().map_err(to_other_err)?;
        let id = FileId::new(hasher.finalize().to_vec());

        persist_content_addressed_temp_file(temp_file, self.file_path(&id))
            .map_err(to_other_err)?;
        Ok(id)
    }

    async fn read_symlink(&self, _path: &RepoPath, id: &SymlinkId) -> BackendResult<String> {
        let path = self.symlink_path(id);
        let target = fs::read_to_string(path).map_err(|err| map_not_found_err(err, id))?;
        Ok(target)
    }

    async fn write_symlink(&self, _path: &RepoPath, target: &str) -> BackendResult<SymlinkId> {
        let mut temp_file = NamedTempFile::new_in(&self.path).map_err(to_other_err)?;
        temp_file
            .write_all(target.as_bytes())
            .map_err(to_other_err)?;
        let mut hasher = Blake2b512::new();
        hasher.update(target.as_bytes());
        let id = SymlinkId::new(hasher.finalize().to_vec());

        persist_content_addressed_temp_file(temp_file, self.symlink_path(&id))
            .map_err(to_other_err)?;
        Ok(id)
    }

    async fn read_tree(&self, _path: &RepoPath, id: &TreeId) -> BackendResult<Tree> {
        let path = self.tree_path(id);
        let buf = fs::read(path).map_err(|err| map_not_found_err(err, id))?;

        let proto = jj_lib::protos::local_store::Tree::decode(&*buf).map_err(to_other_err)?;
        Ok(tree_from_proto(proto))
    }

    async fn write_tree(&self, _path: &RepoPath, tree: &Tree) -> BackendResult<TreeId> {
        let temp_file = NamedTempFile::new_in(&self.path).map_err(to_other_err)?;

        let proto = tree_to_proto(tree);
        temp_file
            .as_file()
            .write_all(&proto.encode_to_vec())
            .map_err(to_other_err)?;

        let id = TreeId::new(blake2b_hash(tree).to_vec());

        persist_content_addressed_temp_file(temp_file, self.tree_path(&id))
            .map_err(to_other_err)?;
        Ok(id)
    }

    fn read_conflict(&self, _path: &RepoPath, id: &ConflictId) -> BackendResult<Conflict> {
        let path = self.conflict_path(id);
        let buf = fs::read(path).map_err(|err| map_not_found_err(err, id))?;

        let proto = jj_lib::protos::local_store::Conflict::decode(&*buf).map_err(to_other_err)?;
        Ok(conflict_from_proto(proto))
    }

    fn write_conflict(&self, _path: &RepoPath, conflict: &Conflict) -> BackendResult<ConflictId> {
        let temp_file = NamedTempFile::new_in(&self.path).map_err(to_other_err)?;

        let proto = conflict_to_proto(conflict);
        temp_file
            .as_file()
            .write_all(&proto.encode_to_vec())
            .map_err(to_other_err)?;

        let id = ConflictId::new(blake2b_hash(conflict).to_vec());

        persist_content_addressed_temp_file(temp_file, self.conflict_path(&id))
            .map_err(to_other_err)?;
        Ok(id)
    }

    async fn read_commit(&self, id: &CommitId) -> BackendResult<Commit> {
        println!("reading commit {:#?}", id);
        if *id == self.root_commit_id {
            return Ok(make_root_commit(
                self.root_change_id().clone(),
                self.empty_tree_id.clone(),
            ));
        }

        let path = self.commit_path(id);
        let buf = fs::read(path).map_err(|err| map_not_found_err(err, id))?;

        let proto = jj_lib::protos::local_store::Commit::decode(&*buf).map_err(to_other_err)?;
        Ok(commit_from_proto(proto))
    }

    async fn write_commit(
        &self,
        mut commit: Commit,
        sign_with: Option<&mut SigningFn>,
    ) -> BackendResult<(CommitId, Commit)> {
        assert!(commit.secure_sig.is_none(), "commit.secure_sig was set");

        if commit.parents.is_empty() {
            return Err(BackendError::Other(
                "Cannot write a commit with no parents".into(),
            ));
        }
        let temp_file = NamedTempFile::new_in(&self.path).map_err(to_other_err)?;

        let mut proto = commit_to_proto(&commit);
        if let Some(sign) = sign_with {
            let data = proto.encode_to_vec();
            let sig = sign(&data).map_err(to_other_err)?;
            proto.secure_sig = Some(sig.clone());
            commit.secure_sig = Some(SecureSig { data, sig });
        }

        temp_file
            .as_file()
            .write_all(&proto.encode_to_vec())
            .map_err(to_other_err)?;

        let id = CommitId::new(blake2b_hash(&commit).to_vec());

        persist_content_addressed_temp_file(temp_file, self.commit_path(&id))
            .map_err(to_other_err)?;
        Ok((id, commit))
    }

    fn get_copy_records(
        &self,
        _paths: Option<&[RepoPathBuf]>,
        _root: &CommitId,
        _head: &CommitId,
    ) -> BackendResult<BoxStream<BackendResult<CopyRecord>>> {
        Ok(Box::pin(stream::empty()))
    }

    fn gc(&self, _index: &dyn Index, _keep_newer: SystemTime) -> BackendResult<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;
    use pollster::FutureExt;

    use super::*;

    /// Test that parents get written correctly
    #[test]
    fn write_commit_parents() {
        let temp_dir = testutils::new_temp_dir();
        let store_path = temp_dir.path();

        let backend = CustomBackend::init(store_path);
        let mut commit = Commit {
            parents: vec![],
            predecessors: vec![],
            root_tree: MergedTreeId::resolved(backend.empty_tree_id().clone()),
            change_id: ChangeId::from_hex("abc123"),
            description: "".to_string(),
            author: create_signature(),
            committer: create_signature(),
            secure_sig: None,
        };

        let write_commit = |commit: Commit| -> BackendResult<(CommitId, Commit)> {
            backend.write_commit(commit, None).block_on()
        };

        // No parents
        commit.parents = vec![];
        assert_matches!(
            write_commit(commit.clone()),
            Err(BackendError::Other(err)) if err.to_string().contains("no parents")
        );

        // Only root commit as parent
        commit.parents = vec![backend.root_commit_id().clone()];
        let first_id = write_commit(commit.clone()).unwrap().0;
        let first_commit = backend.read_commit(&first_id).block_on().unwrap();
        assert_eq!(first_commit, commit);

        // Only non-root commit as parent
        commit.parents = vec![first_id.clone()];
        let second_id = write_commit(commit.clone()).unwrap().0;
        let second_commit = backend.read_commit(&second_id).block_on().unwrap();
        assert_eq!(second_commit, commit);

        // Merge commit
        commit.parents = vec![first_id.clone(), second_id.clone()];
        let merge_id = write_commit(commit.clone()).unwrap().0;
        let merge_commit = backend.read_commit(&merge_id).block_on().unwrap();
        assert_eq!(merge_commit, commit);

        // Merge commit with root as one parent
        commit.parents = vec![first_id, backend.root_commit_id().clone()];
        let root_merge_id = write_commit(commit.clone()).unwrap().0;
        let root_merge_commit = backend.read_commit(&root_merge_id).block_on().unwrap();
        assert_eq!(root_merge_commit, commit);
    }

    fn create_signature() -> Signature {
        Signature {
            name: "Someone".to_string(),
            email: "someone@example.com".to_string(),
            timestamp: Timestamp {
                timestamp: MillisSinceEpoch(0),
                tz_offset: 0,
            },
        }
    }
}
