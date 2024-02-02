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

use crate::{
    BitsOrderFormat, BitsStoreFormat, Field, Primitive, ResolvedTypeVisitor, TypeResolver, Variant,
};
use core::iter::ExactSizeIterator;
use scale_info::{form::PortableForm, PortableRegistry};

/// An error that can occur when we try to encode or decode to a SCALE bit sequence type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// The registry did not contain the bit order type listed.
    OrderFormatNotFound(u32),
    /// The registry did not contain the bit store type listed.
    StoreFormatNotFound(u32),
    /// The bit order type did not have a valid identifier/name.
    NoBitOrderIdent,
    /// The bit store type that we found was not what we expected (a primitive u8/u16/u32/u64).
    UnsupportedBitStoreFormatEncountered,
    /// The bit order type name that we found was not what we expected ("Lsb0" or "Msb0").
    UnsupportedBitOrderFormatEncountered,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::OrderFormatNotFound(n) => {
                write!(f, "Bit order type {n} not found in registry")
            }
            Error::StoreFormatNotFound(n) => {
                write!(f, "Bit store type {n} not found in registry")
            }
            Error::NoBitOrderIdent => {
                write!(f, "Bit order cannot be identified")
            }
            Error::UnsupportedBitStoreFormatEncountered => {
                write!(f, "Unsupported bit store format encountered")
            }
            Error::UnsupportedBitOrderFormatEncountered => {
                write!(f, "Unsupported bit order format encountered")
            }
        }
    }
}

impl TypeResolver for PortableRegistry {
    type TypeId = u32;
    type Error = Error;

    fn resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId = Self::TypeId>>(
        &'this self,
        type_id: &Self::TypeId,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        let type_id = *type_id;
        let Some(ty) = self.resolve(type_id) else {
            return Ok(visitor.visit_not_found());
        };

        let val = match &ty.type_def {
            scale_info::TypeDef::Composite(composite) => {
                visitor.visit_composite(iter_fields(&composite.fields))
            }
            scale_info::TypeDef::Variant(variant) => {
                visitor.visit_variant(iter_variants(&variant.variants))
            }
            scale_info::TypeDef::Sequence(seq) => visitor.visit_sequence(&seq.type_param.id),
            scale_info::TypeDef::Array(arr) => {
                visitor.visit_array(&arr.type_param.id, arr.len as usize)
            }
            scale_info::TypeDef::Tuple(tuple) => {
                let ids = tuple.fields.iter().map(|f| &f.id);
                visitor.visit_tuple(ids)
            }
            scale_info::TypeDef::Primitive(prim) => {
                let primitive = into_primitive(prim);
                visitor.visit_primitive(primitive)
            }
            scale_info::TypeDef::Compact(compact) => visitor.visit_compact(&compact.type_param.id),
            scale_info::TypeDef::BitSequence(ty) => {
                let (order, store) = bits_from_metadata(ty, self)?;
                visitor.visit_bit_sequence(store, order)
            }
        };

        Ok(val)
    }
}

fn into_primitive(primitive: &scale_info::TypeDefPrimitive) -> Primitive {
    match primitive {
        scale_info::TypeDefPrimitive::Bool => Primitive::Bool,
        scale_info::TypeDefPrimitive::Char => Primitive::Char,
        scale_info::TypeDefPrimitive::Str => Primitive::Str,
        scale_info::TypeDefPrimitive::U8 => Primitive::U8,
        scale_info::TypeDefPrimitive::U16 => Primitive::U16,
        scale_info::TypeDefPrimitive::U32 => Primitive::U32,
        scale_info::TypeDefPrimitive::U64 => Primitive::U64,
        scale_info::TypeDefPrimitive::U128 => Primitive::U128,
        scale_info::TypeDefPrimitive::U256 => Primitive::U256,
        scale_info::TypeDefPrimitive::I8 => Primitive::I8,
        scale_info::TypeDefPrimitive::I16 => Primitive::I16,
        scale_info::TypeDefPrimitive::I32 => Primitive::I32,
        scale_info::TypeDefPrimitive::I64 => Primitive::I64,
        scale_info::TypeDefPrimitive::I128 => Primitive::I128,
        scale_info::TypeDefPrimitive::I256 => Primitive::I256,
    }
}

fn iter_variants(
    variants: &'_ [scale_info::Variant<PortableForm>],
) -> impl ExactSizeIterator<Item = Variant<'_, impl ExactSizeIterator<Item = Field<'_, u32>>>> {
    variants.iter().map(|v| Variant {
        index: v.index,
        name: &v.name,
        fields: iter_fields(&v.fields),
    })
}

fn iter_fields(
    fields: &'_ [scale_info::Field<PortableForm>],
) -> impl ExactSizeIterator<Item = Field<'_, u32>> {
    fields.iter().map(|f| Field {
        name: f.name.as_deref(),
        id: &f.ty.id,
    })
}

/// Given some type information in the form of a [`scale_info::PortableRegistry`],
/// and a [`scale_info::TypeDefBitSequence`], this returns information about the
/// order and store format of the bit sequence.
pub fn bits_from_metadata(
    ty: &scale_info::TypeDefBitSequence<scale_info::form::PortableForm>,
    types: &scale_info::PortableRegistry,
) -> Result<(BitsOrderFormat, BitsStoreFormat), Error> {
    let bit_store_ty = ty.bit_store_type.id;
    let bit_order_ty = ty.bit_order_type.id;

    // What is the backing store type expected?
    let bit_store_def = &types
        .resolve(bit_store_ty)
        .ok_or(Error::StoreFormatNotFound(bit_store_ty))?
        .type_def;

    // What is the bit order type expected?
    let bit_order_def = types
        .resolve(bit_order_ty)
        .ok_or(Error::OrderFormatNotFound(bit_order_ty))?
        .path
        .ident()
        .ok_or(Error::NoBitOrderIdent)?;

    use scale_info::{TypeDef, TypeDefPrimitive};
    let bit_store_out = match bit_store_def {
        TypeDef::Primitive(TypeDefPrimitive::U8) => Some(BitsStoreFormat::U8),
        TypeDef::Primitive(TypeDefPrimitive::U16) => Some(BitsStoreFormat::U16),
        TypeDef::Primitive(TypeDefPrimitive::U32) => Some(BitsStoreFormat::U32),
        TypeDef::Primitive(TypeDefPrimitive::U64) => Some(BitsStoreFormat::U64),
        _ => None,
    }
    .ok_or(Error::UnsupportedBitStoreFormatEncountered)?;

    let bit_order_out = match &*bit_order_def {
        "Lsb0" => Some(BitsOrderFormat::Lsb0),
        "Msb0" => Some(BitsOrderFormat::Msb0),
        _ => None,
    }
    .ok_or(Error::UnsupportedBitOrderFormatEncountered)?;

    Ok((bit_order_out, bit_store_out))
}

#[cfg(test)]
mod test {
    extern crate alloc;

    use super::*;
    use alloc::{borrow::ToOwned, boxed::Box, string::String, vec, vec::Vec};

    fn make_type<T: scale_info::TypeInfo + 'static>() -> (u32, scale_info::PortableRegistry) {
        let m = scale_info::MetaType::new::<T>();
        let mut types = scale_info::Registry::new();
        let id = types.register_type(&m);
        let portable_registry: scale_info::PortableRegistry = types.into();

        (id.id, portable_registry)
    }

    fn assert_type<T: scale_info::TypeInfo + 'static>(info: ResolvedTypeInfo) {
        let (id, types) = make_type::<T>();
        let resolved_info = to_resolved_info(&id, &types);
        assert_eq!(info, resolved_info);
    }

    fn to_resolved_info(type_id: &u32, types: &PortableRegistry) -> ResolvedTypeInfo {
        match types.resolve_type(type_id, TestResolveVisitor(types)) {
            Err(e) => ResolvedTypeInfo::Err(e),
            Ok(info) => info,
        }
    }

    /// A test resolve visitor which just reifies the type information
    /// into [`ResolvedTypeInfo`] for easy testing.
    #[derive(Copy, Clone)]
    struct TestResolveVisitor<'resolver>(&'resolver PortableRegistry);

    #[allow(clippy::type_complexity)]
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum ResolvedTypeInfo {
        Err(Error),
        NotFound,
        CompositeOf(Vec<(Option<String>, ResolvedTypeInfo)>),
        VariantOf(Vec<(String, Vec<(Option<String>, ResolvedTypeInfo)>)>),
        SequenceOf(Box<ResolvedTypeInfo>),
        ArrayOf(Box<ResolvedTypeInfo>, usize),
        TupleOf(Vec<ResolvedTypeInfo>),
        Primitive(Primitive),
        Compact(Box<ResolvedTypeInfo>),
        BitSequence(BitsStoreFormat, BitsOrderFormat),
    }

    impl<'resolver> ResolvedTypeVisitor<'resolver> for TestResolveVisitor<'resolver> {
        type TypeId = u32;
        type Value = ResolvedTypeInfo;

        fn visit_unhandled(self, _kind: crate::UnhandledKind) -> Self::Value {
            panic!("all methods implemented")
        }
        fn visit_not_found(self) -> Self::Value {
            ResolvedTypeInfo::NotFound
        }
        fn visit_composite<Fields>(self, fields: Fields) -> Self::Value
        where
            Fields: crate::FieldIter<'resolver, Self::TypeId>,
        {
            let fs = fields
                .map(|f| {
                    let inner_ty = to_resolved_info(f.id, self.0);
                    (f.name.map(|n| n.to_owned()), inner_ty)
                })
                .collect();
            ResolvedTypeInfo::CompositeOf(fs)
        }
        fn visit_variant<Fields: 'resolver, Var>(self, variants: Var) -> Self::Value
        where
            Fields: crate::FieldIter<'resolver, Self::TypeId>,
            Var: crate::VariantIter<'resolver, Fields>,
        {
            let vs = variants
                .map(|v| {
                    let fs: Vec<_> = v
                        .fields
                        .map(|f| {
                            let inner_ty = to_resolved_info(f.id, self.0);
                            (f.name.map(|n| n.to_owned()), inner_ty)
                        })
                        .collect();
                    (v.name.to_owned(), fs)
                })
                .collect();
            ResolvedTypeInfo::VariantOf(vs)
        }
        fn visit_sequence(self, type_id: &'resolver Self::TypeId) -> Self::Value {
            ResolvedTypeInfo::SequenceOf(Box::new(to_resolved_info(type_id, self.0)))
        }
        fn visit_array(self, type_id: &'resolver Self::TypeId, len: usize) -> Self::Value {
            ResolvedTypeInfo::ArrayOf(Box::new(to_resolved_info(type_id, self.0)), len)
        }
        fn visit_tuple<TypeIds>(self, type_ids: TypeIds) -> Self::Value
        where
            TypeIds: ExactSizeIterator<Item = &'resolver Self::TypeId>,
        {
            let ids = type_ids.map(|id| to_resolved_info(id, self.0)).collect();
            ResolvedTypeInfo::TupleOf(ids)
        }
        fn visit_primitive(self, primitive: Primitive) -> Self::Value {
            ResolvedTypeInfo::Primitive(primitive)
        }
        fn visit_compact(self, type_id: &'resolver Self::TypeId) -> Self::Value {
            ResolvedTypeInfo::Compact(Box::new(to_resolved_info(type_id, self.0)))
        }
        fn visit_bit_sequence(
            self,
            store_format: BitsStoreFormat,
            order_format: BitsOrderFormat,
        ) -> Self::Value {
            ResolvedTypeInfo::BitSequence(store_format, order_format)
        }
    }

    #[test]
    fn resolve_primitives() {
        assert_type::<u8>(ResolvedTypeInfo::Primitive(Primitive::U8));
        assert_type::<u16>(ResolvedTypeInfo::Primitive(Primitive::U16));
        assert_type::<u32>(ResolvedTypeInfo::Primitive(Primitive::U32));
        assert_type::<u64>(ResolvedTypeInfo::Primitive(Primitive::U64));
        assert_type::<u128>(ResolvedTypeInfo::Primitive(Primitive::U128));
        assert_type::<i8>(ResolvedTypeInfo::Primitive(Primitive::I8));
        assert_type::<i16>(ResolvedTypeInfo::Primitive(Primitive::I16));
        assert_type::<i32>(ResolvedTypeInfo::Primitive(Primitive::I32));
        assert_type::<i64>(ResolvedTypeInfo::Primitive(Primitive::I64));
        assert_type::<i128>(ResolvedTypeInfo::Primitive(Primitive::I128));
        assert_type::<String>(ResolvedTypeInfo::Primitive(Primitive::Str));
        assert_type::<&str>(ResolvedTypeInfo::Primitive(Primitive::Str));
        assert_type::<bool>(ResolvedTypeInfo::Primitive(Primitive::Bool));
        assert_type::<char>(ResolvedTypeInfo::Primitive(Primitive::Char));
    }

    #[test]
    fn resolve_composites() {
        assert_type::<(u8, bool, String)>(ResolvedTypeInfo::TupleOf(vec![
            ResolvedTypeInfo::Primitive(Primitive::U8),
            ResolvedTypeInfo::Primitive(Primitive::Bool),
            ResolvedTypeInfo::Primitive(Primitive::Str),
        ]));

        #[derive(scale_info::TypeInfo)]
        struct Unnamed(bool, u8);

        assert_type::<Unnamed>(ResolvedTypeInfo::CompositeOf(vec![
            (None, ResolvedTypeInfo::Primitive(Primitive::Bool)),
            (None, ResolvedTypeInfo::Primitive(Primitive::U8)),
        ]));

        #[derive(scale_info::TypeInfo)]
        #[allow(dead_code)]
        struct Named {
            b: bool,
            u: u8,
        }

        assert_type::<Named>(ResolvedTypeInfo::CompositeOf(vec![
            (
                Some("b".to_owned()),
                ResolvedTypeInfo::Primitive(Primitive::Bool),
            ),
            (
                Some("u".to_owned()),
                ResolvedTypeInfo::Primitive(Primitive::U8),
            ),
        ]));
    }

    #[test]
    fn resolve_enums() {
        #[derive(scale_info::TypeInfo)]
        #[allow(dead_code)]
        enum SomeEnum {
            A,
            B(u8, bool),
            C { hello: String },
        }

        assert_type::<SomeEnum>(ResolvedTypeInfo::VariantOf(vec![
            ("A".to_owned(), vec![]),
            (
                "B".to_owned(),
                vec![
                    (None, ResolvedTypeInfo::Primitive(Primitive::U8)),
                    (None, ResolvedTypeInfo::Primitive(Primitive::Bool)),
                ],
            ),
            (
                "C".to_owned(),
                vec![(
                    Some("hello".to_owned()),
                    ResolvedTypeInfo::Primitive(Primitive::Str),
                )],
            ),
        ]));
    }

    #[test]
    fn resolve_sequences() {
        assert_type::<Vec<u8>>(ResolvedTypeInfo::SequenceOf(Box::new(
            ResolvedTypeInfo::Primitive(Primitive::U8),
        )));
        assert_type::<&[u8]>(ResolvedTypeInfo::SequenceOf(Box::new(
            ResolvedTypeInfo::Primitive(Primitive::U8),
        )));
        assert_type::<[bool; 16]>(ResolvedTypeInfo::ArrayOf(
            Box::new(ResolvedTypeInfo::Primitive(Primitive::Bool)),
            16,
        ));
    }

    // This also indirectly tests that bits_from_metadata works as expected.
    #[test]
    fn resolve_bitvecs() {
        use bitvec::{
            order::{Lsb0, Msb0},
            vec::BitVec,
        };

        assert_type::<BitVec<u8, Msb0>>(ResolvedTypeInfo::BitSequence(
            BitsStoreFormat::U8,
            BitsOrderFormat::Msb0,
        ));
        assert_type::<BitVec<u16, Msb0>>(ResolvedTypeInfo::BitSequence(
            BitsStoreFormat::U16,
            BitsOrderFormat::Msb0,
        ));
        assert_type::<BitVec<u32, Msb0>>(ResolvedTypeInfo::BitSequence(
            BitsStoreFormat::U32,
            BitsOrderFormat::Msb0,
        ));
        assert_type::<BitVec<u64, Msb0>>(ResolvedTypeInfo::BitSequence(
            BitsStoreFormat::U64,
            BitsOrderFormat::Msb0,
        ));
        assert_type::<BitVec<u8, Lsb0>>(ResolvedTypeInfo::BitSequence(
            BitsStoreFormat::U8,
            BitsOrderFormat::Lsb0,
        ));
        assert_type::<BitVec<u16, Lsb0>>(ResolvedTypeInfo::BitSequence(
            BitsStoreFormat::U16,
            BitsOrderFormat::Lsb0,
        ));
        assert_type::<BitVec<u32, Lsb0>>(ResolvedTypeInfo::BitSequence(
            BitsStoreFormat::U32,
            BitsOrderFormat::Lsb0,
        ));
        assert_type::<BitVec<u64, Lsb0>>(ResolvedTypeInfo::BitSequence(
            BitsStoreFormat::U64,
            BitsOrderFormat::Lsb0,
        ));
    }
}
