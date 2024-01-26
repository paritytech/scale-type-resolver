#![no_std]

extern crate alloc;
use core::iter::ExactSizeIterator;

/// An implementation and associated things related to [`scale_info::PortableRegistry`].
#[cfg(feature = "scale-info")]
pub mod portable_registry;

pub trait TypeResolver {
    type TypeId: Clone;
    type Error;

    fn resolve_type<'a, V: ResolvedTypeVisitor<TypeId=Self::TypeId>>(&'a self, type_id: Self::TypeId, visitor: V) -> Result<V::Value<'a>, Self::Error>;
}

pub trait ResolvedTypeVisitor: Sized {
    type TypeId: Clone;
    type Value<'a>;

    fn visit_not_found<'a>(self, type_id: Self::TypeId) -> Self::Value<'a>;
    fn visit_composite<'a, Fields>(self, type_id: Self::TypeId, _fields: Fields) -> Self::Value<'a>
        where
            Fields: FieldIter<'a, Self::TypeId>;
    fn visit_variant<'a, Fields, Var>(self, type_id: Self::TypeId, _variants: Var) -> Self::Value<'a>
        where
            Fields: FieldIter<'a, Self::TypeId>,
            Var: VariantIter<'a, Fields>;
    fn visit_sequence<'a>(self, type_id: Self::TypeId) -> Self::Value<'a>;
    fn visit_array<'a>(self, type_id: Self::TypeId, len: usize) -> Self::Value<'a>;
    fn visit_tuple<'a, TypeIds>(self, type_id: Self::TypeId, type_ids: TypeIds) -> Self::Value<'a>
        where
            TypeIds: ExactSizeIterator<Item=Self::TypeId>;
    fn visit_primitive<'a>(self, type_id: Self::TypeId, _primitive: Primitive) -> Self::Value<'a>;
    fn visit_compact<'a>(self, type_id: Self::TypeId) -> Self::Value<'a>;
    fn visit_bit_sequence<'a>(self, type_id: Self::TypeId, _store_format: BitsStoreFormat, _order_format: BitsOrderFormat) -> Self::Value<'a>;
}

/// Information about a composite field.
pub struct Field<'a, TypeId> {
    pub name: Option<&'a str>,
    pub id: TypeId
}

impl<'a, TypeId> Field<'a, TypeId> {
    /// Construct a new field with an ID and optional name.
    pub fn new(id: TypeId, name: Option<&'a str>) -> Self {
        Field { id, name }
    }
    /// Create a new unnamed field.
    pub fn unnamed(id: TypeId) -> Self {
        Field { name: None, id }
    }
    /// Create a new named field.
    pub fn named(id: TypeId, name: &'a str) -> Self {
        Field { name: Some(name), id }
    }
}

/// Information about a specific variant type.
pub struct Variant<'a, Fields> {
    pub index: u8,
    pub name: &'a str,
    pub fields: Fields,
}

/// An iterator over a set of fields.
pub trait FieldIter<'a, TypeId>: ExactSizeIterator<Item = Field<'a, TypeId>> {}
impl<'a, TypeId, T> FieldIter<'a, TypeId> for T where T: ExactSizeIterator<Item = Field<'a, TypeId>> {}

/// An iterator over a set of variants.
pub trait VariantIter<'a, Fields>: ExactSizeIterator<Item = Variant<'a, Fields>> {}
impl<'a, Fields, T> VariantIter<'a, Fields> for T where T: ExactSizeIterator<Item = Variant<'a, Fields>> {}

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