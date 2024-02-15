// Copyright (C) 2024 Parity Technologies (UK) Ltd. (admin@parity.io)
// This file is a part of the scale-decode crate.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//         http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! `scale-type-resolver` provides a generic [`TypeResolver`] trait which can be implemented for
//! any type that is capable of being given a type ID and resolving that into information about
//! how the type is SCALE encoded. This allows libraries like `scale-decode` to be able to decode
//! SCALE encoded bytes using either a modern type resolver like [`scale_info::PortableRegistry`],
//! or using entirely custom type resolvers (which we would need in order decode blocks from pre-V14
//! metadata).
//!
//! It's unlikely that you'd depend on this library directly; more likely you'd depend on a library
//! like `scale-decode` which uses and re-exports the [`TypeResolver`] trait itself.
//!
//! This crate is `no_std` by default and doesn't require `alloc` except for tests.
#![no_std]
#![deny(missing_docs)]

use core::iter::ExactSizeIterator;

/// An implementation and associated things related to [`scale_info::PortableRegistry`].
#[cfg(feature = "scale-info")]
pub mod portable_registry;

/// A concrete [`ResolvedTypeVisitor`] implementation that allows you to provide closures to
/// configure it. Using this is often a lot easier than implementing [`ResolvedTypeVisitor`] yourself,
/// but does require an additional dependency and may be a touch less performant.
#[cfg(feature = "visitor")]
pub mod visitor;

/// This trait can be implemented for any type that is capable of describing how some type (identified
/// by a [`TypeResolver::TypeId`]) is represented in terms of SCALE encoded bytes.
///
/// The naive way of implementing a trait like this would be to have a function that takes in a type ID
/// and returns an enum which represents how the type is SCALE encoded. However, building such an enum
/// to describe more complex types would likely involve allocating, which we'd rather avoid where possible.
/// Instead, the approach taken here is to provide a set of callbacks to the [`TypeResolver::resolve_type()`]
/// via a [`ResolvedTypeVisitor`] implementation. Exactly one of these callbacks is fired (and provided the
/// necessary information) depending on the outcome of resolving a given type. This allows us to be far more
/// flexible about how we hand back the required information, which avoids allocations.
///
/// For an example implementation, see the code in the [`portable_registry`] module.
pub trait TypeResolver {
    /// An identifier which points to some type that we'd like information on.
    type TypeId: TypeId;
    /// An error that can be handed back in the process of trying to resolve a type.
    type Error: core::fmt::Debug + core::fmt::Display;

    /// Given a type ID, this calls a method on the provided [`ResolvedTypeVisitor`] describing the
    /// outcome of resolving the SCALE encoding information.
    fn resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId = Self::TypeId>>(
        &'this self,
        type_id: &Self::TypeId,
        visitor: V,
    ) -> Result<V::Value, Self::Error>;
}

/// A glorified set of callbacks, exactly one of which will fire depending on the outcome of calling
/// [`TypeResolver::resolve_type()`]. These don't typically need to be implemented by the user, and
/// instead are implemented internally in eg `scale-decode` to drive the decoding of types.
///
/// The lifetime held by this trait is the lifetime of the type resolver. Various inputs to the callbacks
/// are thus bound by this lifetime, and it's possible to return values which contain this lifetime.
pub trait ResolvedTypeVisitor<'resolver>: Sized {
    /// The type ID type that the [`TypeResolver`] is using.
    type TypeId: TypeId + 'resolver;
    /// Some value that can be returned from the called method.
    type Value;

    /// Called when the actual method to be called was not implemented.
    fn visit_unhandled(self, kind: UnhandledKind) -> Self::Value;

    /// Called when the type ID passed to [`TypeResolver::resolve_type()`] was not found.
    fn visit_not_found(self) -> Self::Value {
        self.visit_unhandled(UnhandledKind::NotFound)
    }

    /// Called when the type ID corresponds to a composite type. This is provided an iterator
    /// over each of the fields and their type IDs that the composite type contains.
    fn visit_composite<Fields>(self, _fields: Fields) -> Self::Value
    where
        Fields: FieldIter<'resolver, Self::TypeId>,
    {
        self.visit_unhandled(UnhandledKind::Composite)
    }

    /// Called when the type ID corresponds to a variant type. This is provided the list of
    /// variants (and for each variant, the fields within it) that the type could be encoded as.
    fn visit_variant<Fields: 'resolver, Var>(self, _variants: Var) -> Self::Value
    where
        Fields: FieldIter<'resolver, Self::TypeId>,
        Var: VariantIter<'resolver, Fields>,
    {
        self.visit_unhandled(UnhandledKind::Variant)
    }

    /// Called when the type ID corresponds to a sequence of values of some type ID (which is
    /// provided as an argument here). The length of the sequence is compact encoded first.
    fn visit_sequence(self, _type_id: &'resolver Self::TypeId) -> Self::Value {
        self.visit_unhandled(UnhandledKind::Sequence)
    }

    /// Called when the type ID corresponds to an array of values of some type ID (which is
    /// provided as an argument here). The length of the array is known at compile time and
    /// is also provided.
    fn visit_array(self, _type_id: &'resolver Self::TypeId, _len: usize) -> Self::Value {
        self.visit_unhandled(UnhandledKind::Array)
    }

    /// Called when the type ID corresponds to a tuple of values whose type IDs are provided here.
    fn visit_tuple<TypeIds>(self, _type_ids: TypeIds) -> Self::Value
    where
        TypeIds: ExactSizeIterator<Item = &'resolver Self::TypeId>,
    {
        self.visit_unhandled(UnhandledKind::Tuple)
    }

    /// Called when the type ID corresponds to some primitive type. The exact primitive type is
    /// provided in th form of an enum.
    fn visit_primitive(self, _primitive: Primitive) -> Self::Value {
        self.visit_unhandled(UnhandledKind::Primitive)
    }

    /// Called when the type ID corresponds to a compact encoded type. The type ID of the inner type
    /// is provided.
    fn visit_compact(self, _type_id: &'resolver Self::TypeId) -> Self::Value {
        self.visit_unhandled(UnhandledKind::Compact)
    }

    /// Called when the type ID corresponds to a bit sequence, whose store and order types are given.
    fn visit_bit_sequence(
        self,
        _store_format: BitsStoreFormat,
        _order_format: BitsOrderFormat,
    ) -> Self::Value {
        self.visit_unhandled(UnhandledKind::BitSequence)
    }
}

/// If any of the [`ResolvedTypeVisitor`] methods are not implemented, then
/// [`ResolvedTypeVisitor::visit_unhandled()`] is called, and given an instance of this enum to
/// denote which method was unhandled.
#[allow(missing_docs)]
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
    BitSequence,
}

/// A trait representing a type ID.
pub trait TypeId: core::fmt::Debug + core::default::Default {}
impl<T: core::fmt::Debug + core::default::Default> TypeId for T {}

/// Information about a composite field.
#[derive(Debug)]
pub struct Field<'resolver, TypeId: 'resolver> {
    /// The name of the field, or `None` if the field is unnamed.
    pub name: Option<&'resolver str>,
    /// The type ID corresponding to the value for this field.
    pub id: &'resolver TypeId,
}

impl<'resolver, TypeId: 'resolver> Copy for Field<'resolver, TypeId> {}
impl<'resolver, TypeId: 'resolver> Clone for Field<'resolver, TypeId> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'resolver, TypeId> Field<'resolver, TypeId> {
    /// Construct a new field with an ID and optional name.
    pub fn new(id: &'resolver TypeId, name: Option<&'resolver str>) -> Self {
        Field { id, name }
    }
    /// Create a new unnamed field.
    pub fn unnamed(id: &'resolver TypeId) -> Self {
        Field { name: None, id }
    }
    /// Create a new named field.
    pub fn named(id: &'resolver TypeId, name: &'resolver str) -> Self {
        Field {
            name: Some(name),
            id,
        }
    }
}

/// Information about a specific variant type.
#[derive(Clone, Debug)]
pub struct Variant<'resolver, Fields: 'resolver> {
    /// The variant index.
    pub index: u8,
    /// The variant name.
    pub name: &'resolver str,
    /// The fields contained within this variant.
    pub fields: Fields,
}

/// An iterator over a set of fields.
pub trait FieldIter<'resolver, TypeId: 'resolver>:
    ExactSizeIterator<Item = Field<'resolver, TypeId>>
{
}
impl<'resolver, TypeId: 'resolver, T> FieldIter<'resolver, TypeId> for T where
    T: ExactSizeIterator<Item = Field<'resolver, TypeId>>
{
}

/// An iterator over a set of variants.
pub trait VariantIter<'resolver, Fields: 'resolver>:
    ExactSizeIterator<Item = Variant<'resolver, Fields>>
{
}
impl<'resolver, Fields: 'resolver, T> VariantIter<'resolver, Fields> for T where
    T: ExactSizeIterator<Item = Variant<'resolver, Fields>>
{
}

/// This is handed to [`ResolvedTypeVisitor::visit_primitive()`], and
/// denotes the exact shape of the primitive type that we have resolved.
#[allow(missing_docs)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
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
