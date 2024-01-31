use alloc::string::{ String, ToString };
use core::iter::ExactSizeIterator;
use crate::{ TypeResolver, ResolvedTypeVisitor, Field, Variant, Primitive, BitsOrderFormat, BitsStoreFormat };
use scale_info::{ PortableRegistry, form::PortableForm };

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
	StoreFormatNotSupported(String),
	/// The bit order type name that we found was not what we expected ("Lsb0" or "Msb0").
	OrderFormatNotSupported(String),
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
			Error::StoreFormatNotSupported(s) => {
				write!(f, "Bit store type '{s}' is not supported")
			}
			Error::OrderFormatNotSupported(s) => {
				write!(f, "Bit order type '{s}' is not supported")
			}
		}
	}
}

impl TypeResolver for PortableRegistry {
    type TypeId = u32;
    type Error = Error;

    fn resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId=Self::TypeId>>(&'this self, type_id: &Self::TypeId, visitor: V) -> Result<V::Value, Self::Error> {
        let type_id = *type_id;
        let Some(ty) = self.resolve(type_id) else {
            return Ok(visitor.visit_not_found())
        };

        let val = match &ty.type_def {
            scale_info::TypeDef::Composite(composite) => {
                visitor.visit_composite(iter_fields(&composite.fields))
            },
            scale_info::TypeDef::Variant(variant) => {
                visitor.visit_variant(iter_variants(&variant.variants))
            },
            scale_info::TypeDef::Sequence(seq) => {
                visitor.visit_sequence(&seq.type_param.id)
            },
            scale_info::TypeDef::Array(arr) => {
                visitor.visit_array(&arr.type_param.id, arr.len as usize)
            },
            scale_info::TypeDef::Tuple(tuple) => {
                let ids = tuple.fields.iter().map(|f| &f.id);
                visitor.visit_tuple(ids)
            },
            scale_info::TypeDef::Primitive(prim) => {
                let primitive = into_primitive(prim);
                visitor.visit_primitive(primitive)
            },
            scale_info::TypeDef::Compact(compact) => {
                visitor.visit_compact(&compact.type_param.id)
            },
            scale_info::TypeDef::BitSequence(ty) => {
                let (order, store) = bits_from_metadata(ty, self)?;
                visitor.visit_bit_sequence(store, order)
            },
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

fn iter_variants<'a>(variants: &'a [scale_info::Variant<PortableForm>]) -> impl ExactSizeIterator<Item=Variant<'a, impl ExactSizeIterator<Item=Field<'a, u32>>>> {
    variants
        .iter()
        .map(|v| Variant {
            index: v.index,
            name: &v.name,
            fields: iter_fields(&v.fields)
        })
}

fn iter_fields<'a>(fields: &'a [scale_info::Field<PortableForm>]) -> impl ExactSizeIterator<Item=Field<'a, u32>> {
    fields
        .into_iter()
        .map(|f| Field {
            name: f.name.as_deref(),
            id: &f.ty.id
        })
}

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
    .ok_or_else(|| {
        Error::StoreFormatNotSupported(alloc::format!("{bit_store_def:?}"))
    })?;

    let bit_order_out = match &*bit_order_def {
        "Lsb0" => Some(BitsOrderFormat::Lsb0),
        "Msb0" => Some(BitsOrderFormat::Msb0),
        _ => None,
    }
    .ok_or(Error::OrderFormatNotSupported(bit_order_def.to_string()))?;

    Ok((bit_order_out, bit_store_out))
}

#[cfg(test)]
mod test {
	use super::*;

	fn make_type<T: scale_info::TypeInfo + 'static>() -> (u32, scale_info::PortableRegistry) {
		let m = scale_info::MetaType::new::<T>();
		let mut types = scale_info::Registry::new();
		let id = types.register_type(&m);
		let portable_registry: scale_info::PortableRegistry = types.into();

		(id.id, portable_registry)
	}

	fn assert_bits_from_metadata<T: scale_info::TypeInfo + 'static>(store: BitsStoreFormat, order: BitsOrderFormat) {
		// Encode to metadata:
		let (id, types) = make_type::<T>();

		// Pull out said type info:
		let ty = match &types.resolve(id).unwrap().type_def {
			scale_info::TypeDef::BitSequence(b) => b,
			_ => panic!("expected type to look like a bit sequence"),
		};

		// We should be able to obtain a valid Format from it:
		let actual_format = bits_from_metadata(ty, &types).expect("can obtain BitSeq Format from type");

		// The format should match the one we expect:
		assert_eq!((order, store), actual_format);
	}

	#[test]
	fn assert_bits_from_metadata_extracts_correct_details() {
		use bitvec::{
			order::{Lsb0, Msb0},
			vec::BitVec,
		};

		assert_bits_from_metadata::<BitVec<u8, Lsb0>>(BitsStoreFormat::U8, BitsOrderFormat::Lsb0);
		assert_bits_from_metadata::<BitVec<u16, Lsb0>>(BitsStoreFormat::U16, BitsOrderFormat::Lsb0);
		assert_bits_from_metadata::<BitVec<u32, Lsb0>>(BitsStoreFormat::U32, BitsOrderFormat::Lsb0);
		assert_bits_from_metadata::<BitVec<u64, Lsb0>>(BitsStoreFormat::U64, BitsOrderFormat::Lsb0);
		assert_bits_from_metadata::<BitVec<u8, Msb0>>(BitsStoreFormat::U8, BitsOrderFormat::Msb0);
		assert_bits_from_metadata::<BitVec<u16, Msb0>>(BitsStoreFormat::U16, BitsOrderFormat::Msb0);
		assert_bits_from_metadata::<BitVec<u32, Msb0>>(BitsStoreFormat::U32, BitsOrderFormat::Msb0);
		assert_bits_from_metadata::<BitVec<u64, Msb0>>(BitsStoreFormat::U64, BitsOrderFormat::Msb0);
	}
}