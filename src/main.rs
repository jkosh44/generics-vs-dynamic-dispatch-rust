use std::any::Any;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::ops::Add;
use std::sync::Mutex;
use std::time::Instant;

fn main() {}

// Generic database examples.

trait FileSystem {
    /// Overwrite the contents of the file identified by `file_id` with `contents`.
    fn write(&mut self, file_id: u64, contents: Vec<u8>);
    /// Read the contents of the file identified by `file_id`.
    fn read(&self, file_id: u64) -> Option<&[u8]>;
    /// Return the name of the file system.
    fn name(&self) -> &'static str;
    // Not dyn-compatible.
    // fn name() -> &'static str;
}

/// A file system that stores files in memory.
struct InMemoryFileSystem {
    files: HashMap<u64, Vec<u8>>,
}

impl InMemoryFileSystem {
    fn new() -> Self {
        Self {
            files: HashMap::new(),
        }
    }
}

impl FileSystem for InMemoryFileSystem {
    fn write(&mut self, file_id: u64, contents: Vec<u8>) {
        self.files.insert(file_id, contents);
    }

    fn read(&self, file_id: u64) -> Option<&[u8]> {
        self.files.get(&file_id).map(|v| v.as_slice())
    }

    fn name(&self) -> &'static str {
        "In Memory FileSystem"
    }
}

/// An implementation of the Ext2 file system.
struct Ext2 {
    /// Use your imagination and pretend that this is a real
    /// implementation instead of wrapping the in-memory
    /// implementation.
    fs: InMemoryFileSystem,
}

impl Ext2 {
    fn new() -> Self {
        Self {
            fs: InMemoryFileSystem::new(),
        }
    }
}

impl FileSystem for Ext2 {
    fn write(&mut self, file_id: u64, contents: Vec<u8>) {
        self.fs.write(file_id, contents);
    }

    fn read(&self, file_id: u64) -> Option<&[u8]> {
        self.fs.read(file_id)
    }

    fn name(&self) -> &'static str {
        "Ext2"
    }
}

struct GenericDatabase<T: FileSystem> {
    fs: T,
    next_id: u64,
    /// The value of each key is stored in its own file ... maybe not
    /// the most efficient.
    key_map: HashMap<Vec<u8>, u64>,
}

impl<T: FileSystem> GenericDatabase<T> {
    fn welcome(&self) -> String {
        format!(
            "Welcome the a blazingly fast database using the {} file system",
            self.fs.name()
        )
    }

    fn new(fs: T) -> Self {
        Self {
            fs,
            next_id: 0,
            key_map: HashMap::new(),
        }
    }

    fn set(&mut self, key: Vec<u8>, value: Vec<u8>) {
        let id = self.key_map.entry(key).or_insert_with(|| {
            let id = self.next_id;
            self.next_id += 1;
            id
        });
        self.fs.write(*id, value);
    }

    fn get(&self, key: &[u8]) -> Option<&[u8]> {
        let id = self.key_map.get(key)?;
        self.fs.read(*id)
    }
}

#[test]
fn test_generic_database() {
    let mut db: GenericDatabase<InMemoryFileSystem> =
        GenericDatabase::new(InMemoryFileSystem::new());
    db.set(b"ny".to_vec(), b"albany".to_vec());
    assert_eq!(db.get(b"ny"), Some(b"albany".as_slice()));

    let mut db: GenericDatabase<Ext2> = GenericDatabase::new(Ext2::new());
    db.set(b"maryland".to_vec(), b"annapolis".to_vec());
    assert_eq!(db.get(b"maryland"), Some(b"annapolis".as_slice()));
}

#[test]
fn test_generic_database_welcome() {
    let db: GenericDatabase<InMemoryFileSystem> = GenericDatabase::new(InMemoryFileSystem::new());
    db.welcome();

    let db: GenericDatabase<Ext2> = GenericDatabase::new(Ext2::new());
    db.welcome();
}

struct InMemoryDatabase {
    fs: InMemoryFileSystem,
    next_id: u64,
    /// The value of each key is stored in its own file ... maybe not
    /// the most efficient.
    key_map: HashMap<Vec<u8>, u64>,
}

impl InMemoryDatabase {
    fn new(fs: InMemoryFileSystem) -> Self {
        Self {
            fs,
            next_id: 0,
            key_map: HashMap::new(),
        }
    }

    fn set(&mut self, key: Vec<u8>, value: Vec<u8>) {
        let id = self.key_map.entry(key).or_insert_with(|| {
            let id = self.next_id;
            self.next_id += 1;
            id
        });
        self.fs.write(*id, value);
    }

    fn get(&self, key: &[u8]) -> Option<&[u8]> {
        let id = self.key_map.get(key)?;
        self.fs.read(*id)
    }
}

struct Ext2Database {
    fs: Ext2,
    next_id: u64,
    /// The value of each key is stored in its own file ... maybe not
    /// the most efficient.
    key_map: HashMap<Vec<u8>, u64>,
}

impl Ext2Database {
    fn new(fs: Ext2) -> Self {
        Self {
            fs,
            next_id: 0,
            key_map: HashMap::new(),
        }
    }

    fn set(&mut self, key: Vec<u8>, value: Vec<u8>) {
        let id = self.key_map.entry(key).or_insert_with(|| {
            let id = self.next_id;
            self.next_id += 1;
            id
        });
        self.fs.write(*id, value);
    }

    fn get(&self, key: &[u8]) -> Option<&[u8]> {
        let id = self.key_map.get(key)?;
        self.fs.read(*id)
    }
}

#[test]
fn test_concrete_generic_database() {
    let mut db: InMemoryDatabase = InMemoryDatabase::new(InMemoryFileSystem::new());
    db.set(b"ny".to_vec(), b"albany".to_vec());
    assert_eq!(db.get(b"ny"), Some(b"albany".as_slice()));

    let mut db: Ext2Database = Ext2Database::new(Ext2::new());
    db.set(b"maryland".to_vec(), b"annapolis".to_vec());
    assert_eq!(db.get(b"maryland"), Some(b"annapolis".as_slice()));
}

// Generic function example.

fn generic_add<T>(t1: T, t2: T)
where
    T: Add,
    <T as Add>::Output: Debug,
{
    let sum = t1 + t2;
    println!("{sum:?}")
}

#[test]
fn test_generic_add() {
    generic_add(42_i64, 42_i64);
    generic_add(42_u64, 42_u64);
}

fn i64_generic_add(t1: i64, t2: i64) {
    let sum = t1 + t2;
    println!("{sum:?}")
}

fn u64_generic_add(t1: u64, t2: u64) {
    let sum = t1 + t2;
    println!("{sum:?}")
}

#[test]
fn test_concrete_generic_add() {
    i64_generic_add(42_i64, 42_i64);
    u64_generic_add(42_u64, 42_u64);
}

// Dynamic dispatch database example.

struct DynamicDatabase {
    fs: Box<dyn FileSystem>,
    next_id: u64,
    /// The value of each key is stored in its own file ... maybe not
    /// the most efficient.
    key_map: HashMap<Vec<u8>, u64>,
}

impl DynamicDatabase {
    fn welcome(&self) -> String {
        format!(
            "Welcome the a blazingly fast database using the {} file system",
            self.fs.name()
        )
    }

    fn new(fs: Box<dyn FileSystem>) -> Self {
        Self {
            fs,
            next_id: 0,
            key_map: HashMap::new(),
        }
    }

    fn set(&mut self, key: Vec<u8>, value: Vec<u8>) {
        let id = self.key_map.entry(key).or_insert_with(|| {
            let id = self.next_id;
            self.next_id += 1;
            id
        });
        self.fs.write(*id, value);
    }

    fn get(&self, key: &[u8]) -> Option<&[u8]> {
        let id = self.key_map.get(key)?;
        self.fs.read(*id)
    }
}

#[test]
fn test_dynamic_database() {
    let mut db: DynamicDatabase = DynamicDatabase::new(Box::new(InMemoryFileSystem::new()));
    db.set(b"ny".to_vec(), b"albany".to_vec());
    assert_eq!(db.get(b"ny"), Some(b"albany".as_slice()));

    let mut db: DynamicDatabase = DynamicDatabase::new(Box::new(Ext2::new()));
    db.set(b"maryland".to_vec(), b"annapolis".to_vec());
    assert_eq!(db.get(b"maryland"), Some(b"annapolis".as_slice()));
}

#[test]
fn test_dynamic_database_welcome() {
    let db: DynamicDatabase = DynamicDatabase::new(Box::new(InMemoryFileSystem::new()));
    db.welcome();

    let db: DynamicDatabase = DynamicDatabase::new(Box::new(Ext2::new()));
    db.welcome();
}

// Dynamic dispatch function example.

fn dynamic_println(t: &dyn Display) {
    println!("{t}");
}

#[test]
fn test_dynamic_println() {
    dynamic_println(&42_i64);
    dynamic_println(&42_u64);
}

// Dynamic dispatch pointer examples.

#[allow(unused)]
#[derive(Debug)]
struct UnsizedType {
    t: dyn Debug,
}

// Does not compile.
// fn use_unsized_type(ut: UnsizedType) {
//     println!("{ut:?}");
// }

// Generic vs dynamic dispatch performance comparison.

trait AddOne {
    fn add_one(&mut self);
}

impl AddOne for i8 {
    fn add_one(&mut self) {
        *self += 1;
    }
}

struct GenericVec<T: AddOne> {
    v: [T; 1_000],
}

#[test]
fn test_generic_vec() {
    let v = [42_i8; 1_000];
    let gv = GenericVec { v };
    let start = Instant::now();
    for mut e in gv.v {
        e.add_one()
    }
    let dur = start.elapsed();
    println!("took {dur:?}");
}

struct DynamicVec {
    v: [Box<dyn AddOne>; 1_000],
}

#[test]
fn test_dynamic_vec() {
    let v: [Box<dyn AddOne>; 1_000] = std::array::from_fn(|_| Box::new(42_i8) as Box<dyn AddOne>);
    let gv = DynamicVec { v };
    let start = Instant::now();
    for mut e in gv.v {
        e.add_one();
    }
    let dur = start.elapsed();
    println!("took {dur:?}");
}

// Generic wrappers.

#[allow(unused)]
struct GenericDatabaseWrapper<T: FileSystem> {
    db: GenericDatabase<T>,
}

#[allow(unused)]
struct GenericDatabaseWrapperWrapper<T: FileSystem> {
    dbw: GenericDatabaseWrapper<T>,
}

// Dynamic dispatch wrappers.

#[allow(unused)]
struct DynamicDatabaseWrapper {
    db: DynamicDatabase,
}

#[allow(unused)]
struct DynamicDatabaseWrapperWrapper {
    dbw: DynamicDatabaseWrapper,
}

struct GenericDisplayVec<T: Display> {
    v: [T; 1_000],
}

impl<T: Add<Output = T> + Copy + Display> GenericDisplayVec<T> {
    fn sum(&self, other: &Self) -> Self {
        let v: [T; 1_000] = std::array::from_fn(|idx| self.v[idx] + other.v[idx]);
        GenericDisplayVec { v }
    }
}

#[test]
fn test_generic_vec_sum() {
    let iv1 = [42_i8; 1_000];
    let iv2 = [42_i8; 1_000];
    let igv1 = GenericDisplayVec { v: iv1 };
    let igv2 = GenericDisplayVec { v: iv2 };
    let igv3 = igv1.sum(&igv2);
    assert_eq!(igv3.v, [84_i8; 1_000]);

    let sv1 = ["hello"; 1_000];
    let sv2 = ["world"; 1_000];
    let _sgv1 = GenericDisplayVec { v: sv1 };
    let _sgv2 = GenericDisplayVec { v: sv2 };
    // Does not compile because the `sum` method does not exist for `GenericDisplayVec<&str>`.
    // let _sgv3 = _sgv1.sum(&_sgv2);
}

trait SessionPermissions {}
struct ReadWrite {}
impl SessionPermissions for ReadWrite {}
struct ReadOnly {}
impl SessionPermissions for ReadOnly {}

struct Session<T: SessionPermissions> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T: SessionPermissions> Session<T> {
    fn read(&self) {
        println!("I AM READING");
    }
}

impl Session<ReadWrite> {
    fn new_writer() -> Session<ReadWrite> {
        Session {
            _phantom: Default::default(),
        }
    }

    fn into_reader(self) -> Session<ReadOnly> {
        Session {
            _phantom: Default::default(),
        }
    }

    fn write(&mut self) {
        println!("I AM WRITING");
    }
}

impl Session<ReadOnly> {
    fn new_reader() -> Session<ReadOnly> {
        Session {
            _phantom: Default::default(),
        }
    }

    fn into_writer(self) -> Session<ReadWrite> {
        Session {
            _phantom: Default::default(),
        }
    }
}

#[test]
fn conditional_type_safety() {
    let mut session = Session::new_writer();
    session.read();
    session.write();

    let session = Session::new_reader();
    session.read();
    // Does not compile because this method does not exist.
    // session.write();
}

#[test]
fn converting_sessions() {
    let mut session = Session::new_writer();
    session.read();
    session.write();

    let session = session.into_reader();
    session.read();
    // Does not compile because this method does not exist anymore.
    // session.write();

    let mut session = session.into_writer();
    session.read();
    session.write();
}

#[test]
fn dynamic_mix_and_match() {
    let mut v: Vec<Box<dyn Any>> = Vec::new();
    v.push(Box::new(42));
    v.push(Box::new("hello"));
    v.push(Box::new(Vec::<bool>::new()));
    v.push(Box::new(false));
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Debug)]
enum IntOrStrOrBoolVecOrBool {
    I64(i64),
    Str(&'static str),
    BoolVec(Vec<bool>),
    Bool(bool),
}

#[test]
fn generic_mix_and_match() {
    let mut v = Vec::new();
    v.push(IntOrStrOrBoolVecOrBool::I64(42));
    v.push(IntOrStrOrBoolVecOrBool::Str("hello"));
    v.push(IntOrStrOrBoolVecOrBool::BoolVec(Vec::new()));
    v.push(IntOrStrOrBoolVecOrBool::Bool(false));

    assert_eq!(v[0], IntOrStrOrBoolVecOrBool::I64(42));
    assert_eq!(v[1], IntOrStrOrBoolVecOrBool::Str("hello"));
    assert_eq!(v[2], IntOrStrOrBoolVecOrBool::BoolVec(Vec::new()));
    assert_eq!(v[3], IntOrStrOrBoolVecOrBool::Bool(false));
}

fn dynamic_cast(t: &dyn Display) {
    println!("{t}");
}

#[test]
fn test_dynamic_cast() {
    let i = 42;
    dynamic_cast(&i);

    let _t = Mutex::new(42);
    // Fails to compile because `Mutex` does not implement `Display`.
    // dynamic_cast(&t);
}

trait AnyDisplay: Display + Any {}
impl<T: Display + Any> AnyDisplay for T {}

struct DynamicProcessor {
    inner: Box<dyn AnyDisplay>,
}

impl DynamicProcessor {
    fn process(&mut self) {
        println!("{}", self.inner);
    }

    fn into_inner(self) -> Box<dyn AnyDisplay> {
        self.inner
    }
}

#[test]
fn test_dynamic_processor() {
    let t1 = Box::new(42);
    let mut processor = DynamicProcessor { inner: t1 };
    processor.process();

    let t2: Box<dyn Any> = processor.into_inner();

    // Causes a panic because `t2` is not a char.
    // let t2: Box<char> = t2.downcast().unwrap();

    // Does not compile because `dyn Any` does not implement `Add`.
    // println!("{}", *t2 + 1);

    let t2: Box<i32> = t2.downcast().unwrap();
    println!("{}", *t2 + 1);
}

struct GenericProcessor<T: Display> {
    inner: T,
}

impl<T: Display> GenericProcessor<T> {
    fn process(&mut self) {
        println!("{}", self.inner);
    }

    fn into_inner(self) -> T {
        self.inner
    }
}

#[test]
fn test_generic_processor() {
    let t1: i32 = 42;
    let mut processor = GenericProcessor { inner: t1 };
    processor.process();
    // No cast needed, we know `t2` is an `i32`.
    let t2 = processor.into_inner();
    println!("{}", t2 + 1);
}

enum FileSystemEnum {
    InMemory(InMemoryFileSystem),
    Ext2(Ext2),
}

impl FileSystemEnum {
    fn write(&mut self, file_id: u64, contents: Vec<u8>) {
        match self {
            FileSystemEnum::InMemory(fs) => fs.write(file_id, contents),
            FileSystemEnum::Ext2(fs) => fs.write(file_id, contents),
        }
    }

    fn read(&self, file_id: u64) -> Option<&[u8]> {
        match self {
            FileSystemEnum::InMemory(fs) => fs.read(file_id),
            FileSystemEnum::Ext2(fs) => fs.read(file_id),
        }
    }

    fn name(&self) -> &'static str {
        match self {
            FileSystemEnum::InMemory(fs) => fs.name(),
            FileSystemEnum::Ext2(fs) => fs.name(),
        }
    }
}

struct EnumDatabase {
    fs: FileSystemEnum,
    next_id: u64,
    /// The value of each key is stored in its own file ... maybe not
    /// the most efficient.
    key_map: HashMap<Vec<u8>, u64>,
}

impl EnumDatabase {
    fn welcome(&self) -> String {
        format!(
            "Welcome the a blazingly fast database using the {} file system",
            self.fs.name()
        )
    }

    fn new(fs: FileSystemEnum) -> Self {
        Self {
            fs,
            next_id: 0,
            key_map: HashMap::new(),
        }
    }

    fn set(&mut self, key: Vec<u8>, value: Vec<u8>) {
        let id = self.key_map.entry(key).or_insert_with(|| {
            let id = self.next_id;
            self.next_id += 1;
            id
        });
        self.fs.write(*id, value);
    }

    fn get(&self, key: &[u8]) -> Option<&[u8]> {
        let id = self.key_map.get(key)?;
        self.fs.read(*id)
    }
}

#[test]
fn test_enum_database() {
    let mut db = EnumDatabase::new(FileSystemEnum::InMemory(InMemoryFileSystem::new()));
    db.set(b"ny".to_vec(), b"albany".to_vec());
    assert_eq!(db.get(b"ny"), Some(b"albany".as_slice()));
    db.welcome();

    let mut db = EnumDatabase::new(FileSystemEnum::Ext2(Ext2::new()));
    db.set(b"maryland".to_vec(), b"annapolis".to_vec());
    assert_eq!(db.get(b"maryland"), Some(b"annapolis".as_slice()));
    db.welcome();
}
