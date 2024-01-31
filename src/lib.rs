#![no_std]

extern crate alloc;
use core::iter::ExactSizeIterator;

/// An implementation and associated things related to [`scale_info::PortableRegistry`].
#[cfg(feature = "scale-info")]
pub mod portable_registry;

pub trait TypeResolver {
    type TypeId: TypeId;
    type Error: core::fmt::Debug + core::fmt::Display;

    fn resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId=Self::TypeId>>(&'this self, type_id: &Self::TypeId, visitor: V) -> Result<V::Value, Self::Error>;
}

pub trait ResolvedTypeVisitor<'resolver>: Sized {
    type TypeId: TypeId + 'resolver;
    type Value;

    fn visit_unhandled(self, kind: UnhandledKind) -> Self::Value;
    fn visit_not_found(self) -> Self::Value {
        self.visit_unhandled(UnhandledKind::NotFound)
    }
    fn visit_composite<Fields>(self, _fields: Fields) -> Self::Value
        where Fields: FieldIter<'resolver, Self::TypeId>
    {
        self.visit_unhandled(UnhandledKind::Composite)
    }
    fn visit_variant<Fields: 'resolver, Var>(self, _variants: Var) -> Self::Value
        where
            Fields: FieldIter<'resolver, Self::TypeId>,
            Var: VariantIter<'resolver, Fields>
    {
        self.visit_unhandled(UnhandledKind::Variant)
    }
    fn visit_sequence(self, _type_id: &'resolver Self::TypeId) -> Self::Value {
        self.visit_unhandled(UnhandledKind::Sequence)
    }
    fn visit_array(self, _type_id: &'resolver Self::TypeId, _len: usize) -> Self::Value {
        self.visit_unhandled(UnhandledKind::Array)
    }
    fn visit_tuple<TypeIds>(self, _type_ids: TypeIds) -> Self::Value
        where TypeIds: ExactSizeIterator<Item=&'resolver Self::TypeId>
    {
        self.visit_unhandled(UnhandledKind::Tuple)
    }
    fn visit_primitive(self, _primitive: Primitive) -> Self::Value {
        self.visit_unhandled(UnhandledKind::Primitive)
    }
    fn visit_compact(self, _type_id: &'resolver Self::TypeId) -> Self::Value {
        self.visit_unhandled(UnhandledKind::Compact)
    }
    fn visit_bit_sequence(self, _store_format: BitsStoreFormat, _order_format: BitsOrderFormat) -> Self::Value {
        self.visit_unhandled(UnhandledKind::BitSequence)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnhandledKind {
    NotFound,
    Composite,
    Variant,
    Sequence,
    Array,
    Tuple,
    Primitive,
    Compact,
    BitSequence
}

pub trait TypeId: Clone + core::fmt::Debug + core::default::Default {}
impl <T: Clone + core::fmt::Debug + core::default::Default> TypeId for T {}

/// Information about a composite field.
#[derive(Clone, Debug)]
pub struct Field<'info, TypeId: 'info> {
    pub name: Option<&'info str>,
    pub id: &'info TypeId
}

impl<'info, TypeId> Field<'info, TypeId> {
    /// Construct a new field with an ID and optional name.
    pub fn new(id: &'info TypeId, name: Option<&'info str>) -> Self {
        Field { id, name }
    }
    /// Create a new unnamed field.
    pub fn unnamed(id: &'info TypeId) -> Self {
        Field { name: None, id }
    }
    /// Create a new named field.
    pub fn named(id: &'info TypeId, name: &'info str) -> Self {
        Field { name: Some(name), id }
    }
}

/// Information about a specific variant type.
#[derive(Clone, Debug)]
pub struct Variant<'info, Fields: 'info> {
    pub index: u8,
    pub name: &'info str,
    pub fields: Fields,
}

/// An iterator over a set of fields.
pub trait FieldIter<'info, TypeId: 'info>: ExactSizeIterator<Item = Field<'info, TypeId>> {}
impl<'info, TypeId: 'info, T> FieldIter<'info, TypeId> for T where T: ExactSizeIterator<Item = Field<'info, TypeId>> {}

/// An iterator over a set of variants.
pub trait VariantIter<'info, Fields: 'info>: ExactSizeIterator<Item = Variant<'info, Fields>> {}
impl<'info, Fields: 'info, T> VariantIter<'info, Fields> for T where T: ExactSizeIterator<Item = Variant<'info, Fields>> {}

/// This states the primitive type that we expect.
#[derive(Clone,Copy,PartialEq,Eq,Debug)]
pub enum Primitive {
    Bool,
    Char,
    Str,
    U8,
    U16,
    U32,
    U64,
    U128,
    U256,
    I8,
    I16,
    I32,
    I64,
    I128,
    I256,
}

/// This is a runtime representation of the order that bits will be written
/// to the specified [`BitsStoreFormat`].
///
/// - [`BitsOrderFormat::Lsb0`] means that we write to the least significant bit first
///   and then work our way up to the most significant bit as we push new bits.
/// - [`BitsOrderFormat::Msb0`] means that we write to the most significant bit first
///   and then work our way down to the least significant bit as we push new bits.
///
/// These are equivalent to `bitvec`'s `order::Lsb0` and `order::Msb0`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BitsOrderFormat {
	/// Least significant bit first.
	Lsb0,
	/// Most significant bit first.
	Msb0,
}

/// This is a runtime representation of the store type that we're targeting. These
/// are equivalent to the `bitvec` store types `u8`, `u16` and so on.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BitsStoreFormat {
	/// Equivalent to [`u8`].
	U8,
	/// Equivalent to [`u16`].
	U16,
	/// Equivalent to [`u32`].
	U32,
	/// Equivalent to [`u64`].
	U64,
}