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
#![allow(clippy::type_complexity)]

use crate::{
    BitsOrderFormat, BitsStoreFormat, Field, FieldIter, Primitive, ResolvedTypeVisitor,
    UnhandledKind, Variant, VariantIter,
};
use smallvec::SmallVec;

/// A concrete iterator over struct or variant fields information.
pub struct ConcreteFieldIter<'resolver, TypeId> {
    fields: SmallVec<[Field<'resolver, TypeId>; 16]>,
    idx: usize,
}

impl<'resolver, TypeId> Iterator for ConcreteFieldIter<'resolver, TypeId> {
    type Item = Field<'resolver, TypeId>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.fields.get(self.idx) {
            Some(field) => {
                self.idx += 1;
                Some(*field)
            }
            None => None,
        }
    }
}

impl<'resolver, TypeId> ExactSizeIterator for ConcreteFieldIter<'resolver, TypeId> {
    fn len(&self) -> usize {
        self.fields.len()
    }
}

/// This is a concrete visitor which implements [`ResolvedTypeVisitor`]. It's instantiated by
/// calling the **standalone** [`new`] function; see the docs there for more information.
pub struct ConcreteResolvedTypeVisitor<
    'resolver,
    Context,
    TypeId,
    Output,
    UnhandledFn,
    NotFoundFn,
    CompositeFn,
    VariantFn,
    SequenceFn,
    ArrayFn,
    TupleFn,
    PrimitiveFn,
    CompactFn,
    BitSequenceFn,
> {
    _marker: core::marker::PhantomData<(TypeId, Output, &'resolver ())>,
    context: Context,
    visit_unhandled: UnhandledFn,
    visit_not_found: NotFoundFn,
    visit_composite: CompositeFn,
    visit_variant: VariantFn,
    visit_sequence: SequenceFn,
    visit_array: ArrayFn,
    visit_tuple: TupleFn,
    visit_primitive: PrimitiveFn,
    visit_compact: CompactFn,
    visit_bit_sequence: BitSequenceFn,
}

/// Instantiate a new [`ConcreteResolvedTypeVisitor`] by providing a closure which is
/// called by default if we don't add any explicit handler for a given SCALE type.
///
/// It's expected that you'll attach handlers for any types you're interested in getting
/// more details about like so:
///
/// ```rust
/// use scale_type_resolver::{ TypeResolver, ResolvedTypeVisitor };
///
/// // Some dummy type that we're saying can resolve types:
/// struct MyTypeResolver;
/// impl TypeResolver for MyTypeResolver {
///     type TypeId = u32;
///     type Error = u8;
///     fn resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId = Self::TypeId>>(
///         &'this self,
///         type_id: &Self::TypeId,
///         visitor: V,
///     ) -> Result<V::Value, Self::Error> {
///         Ok(visitor.visit_not_found())
///     }
/// }
///
/// // Now, we can create a visitor using this `visitor::new` function.
/// // This has specific handling for composite and variant types, falling
/// // back to returning `1u64` if some other type was found.
/// let context = ();
/// let visitor = scale_type_resolver::visitor::new(context, |_context, _unhandled_kind| 1u64)
///     .visit_composite(|_context, _composite_fields| 2)
///     .visit_primitive(|_context, _primitive_type| 3);
///
/// // By providing the visitor to a type resolver, the TypeId type can be
/// // inferred (else it can be given on the `visitor::new` function).
/// MyTypeResolver.resolve_type(&123, visitor);
/// ```
///
/// The `visit_*` methods provided each take closures which have a similar type signature to the
/// underlying trait methods on [`ResolvedTypeVisitor`], with small differences where necessary to
/// avoid type and ownership issues. The first argument to every function is some arbitrary context
/// which is provided as the first argument to [`scale_type_resolver::visitor::new()`].
///
/// Using this concrete visitor is expected to be almost as optimal as implementing the
/// [`ResolvedTypeVisitor`] trait manually. One area where it makes a small sacrifice to this is in
/// the [`ConcreteResolvedTypeVisitor::visit_variant()`] method, which must collect the variant
/// fields into a [`smallvec::SmallVec`] to avoid ownership issues. This will only allocate if more
/// than 16 variant fields exist. The default "unhandled" function here must also implement `Clone`,
/// which isn't necessary in a raw trait implementation, since it will, by default, be called in all
/// of the other impls if no methods are provided.
pub fn new<'resolver, Context, TypeId, Output, NewUnhandledFn>(
    context: Context,
    unhandled_fn: NewUnhandledFn,
) -> ConcreteResolvedTypeVisitor<
    'resolver,
    Context,
    TypeId,
    Output,
    NewUnhandledFn,
    impl FnOnce(Context) -> Output,
    impl for<'a> FnOnce(Context, &'a mut dyn FieldIter<'resolver, TypeId>) -> Output,
    impl for<'a> FnOnce(
        Context,
        &'a mut dyn VariantIter<'resolver, ConcreteFieldIter<'resolver, TypeId>>,
    ) -> Output,
    impl FnOnce(Context, &'resolver TypeId) -> Output,
    impl FnOnce(Context, &'resolver TypeId, usize) -> Output,
    impl for<'a> FnOnce(Context, &'a mut dyn ExactSizeIterator<Item = &'resolver TypeId>) -> Output,
    impl FnOnce(Context, Primitive) -> Output,
    impl FnOnce(Context, &'resolver TypeId) -> Output,
    impl FnOnce(Context, BitsStoreFormat, BitsOrderFormat) -> Output,
>
where
    NewUnhandledFn: FnOnce(Context, UnhandledKind) -> Output + Clone,
{
    let visit_unhandled = unhandled_fn.clone();

    // We explicitly define all of the other impls here so that the full concrete
    // type of ConcreteResolvedTypeVisitor is known immediately. If we used `Option`s
    // here instead, we'd struggle to resolve the concrete `T` in each `Option<T>`.
    let visit_not_found = {
        let u = unhandled_fn.clone();
        move |ctx| u(ctx, UnhandledKind::NotFound)
    };
    let visit_composite = {
        let u = unhandled_fn.clone();
        move |ctx, _: &mut dyn FieldIter<'resolver, TypeId>| u(ctx, UnhandledKind::Composite)
    };
    let visit_variant = {
        let u = unhandled_fn.clone();
        move |ctx, _: &mut dyn VariantIter<'resolver, ConcreteFieldIter<'resolver, TypeId>>| {
            u(ctx, UnhandledKind::Variant)
        }
    };
    let visit_sequence = {
        let u = unhandled_fn.clone();
        move |ctx, _| u(ctx, UnhandledKind::Sequence)
    };
    let visit_array = {
        let u = unhandled_fn.clone();
        move |ctx, _, _| u(ctx, UnhandledKind::Array)
    };
    let visit_tuple = {
        let u = unhandled_fn.clone();
        move |ctx, _: &mut dyn ExactSizeIterator<Item = &'resolver TypeId>| {
            u(ctx, UnhandledKind::Tuple)
        }
    };
    let visit_primitive = {
        let u = unhandled_fn.clone();
        move |ctx, _| u(ctx, UnhandledKind::Primitive)
    };
    let visit_compact = {
        let u = unhandled_fn.clone();
        move |ctx, _| u(ctx, UnhandledKind::Compact)
    };
    let visit_bit_sequence = {
        let u = unhandled_fn.clone();
        move |ctx, _, _| u(ctx, UnhandledKind::BitSequence)
    };

    ConcreteResolvedTypeVisitor {
        _marker: core::marker::PhantomData,
        context,
        visit_unhandled,
        visit_not_found,
        visit_composite,
        visit_variant,
        visit_sequence,
        visit_array,
        visit_tuple,
        visit_primitive,
        visit_compact,
        visit_bit_sequence,
    }
}

impl<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NotFoundFn,
        CompositeFn,
        VariantFn,
        SequenceFn,
        ArrayFn,
        TupleFn,
        PrimitiveFn,
        CompactFn,
        BitSequenceFn,
    >
    ConcreteResolvedTypeVisitor<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NotFoundFn,
        CompositeFn,
        VariantFn,
        SequenceFn,
        ArrayFn,
        TupleFn,
        PrimitiveFn,
        CompactFn,
        BitSequenceFn,
    >
{
    /// Provide a closure that's called when [`ResolvedTypeVisitor::visit_not_found()`] is.
    pub fn visit_not_found<NewNotFoundFn>(
        self,
        new_not_found_fn: NewNotFoundFn,
    ) -> ConcreteResolvedTypeVisitor<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NewNotFoundFn,
        CompositeFn,
        VariantFn,
        SequenceFn,
        ArrayFn,
        TupleFn,
        PrimitiveFn,
        CompactFn,
        BitSequenceFn,
    >
    where
        NewNotFoundFn: FnOnce(Context) -> Output,
    {
        ConcreteResolvedTypeVisitor {
            _marker: core::marker::PhantomData,
            context: self.context,
            visit_unhandled: self.visit_unhandled,
            visit_not_found: new_not_found_fn,
            visit_composite: self.visit_composite,
            visit_variant: self.visit_variant,
            visit_sequence: self.visit_sequence,
            visit_array: self.visit_array,
            visit_tuple: self.visit_tuple,
            visit_primitive: self.visit_primitive,
            visit_compact: self.visit_compact,
            visit_bit_sequence: self.visit_bit_sequence,
        }
    }

    /// Provide a closure that's called when [`ResolvedTypeVisitor::visit_composite()`] is.
    pub fn visit_composite<NewCompositeFn>(
        self,
        new_composite_fn: NewCompositeFn,
    ) -> ConcreteResolvedTypeVisitor<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NotFoundFn,
        NewCompositeFn,
        VariantFn,
        SequenceFn,
        ArrayFn,
        TupleFn,
        PrimitiveFn,
        CompactFn,
        BitSequenceFn,
    >
    where
        NewCompositeFn: FnOnce(Context, &mut dyn FieldIter<'resolver, TypeId>) -> Output,
    {
        ConcreteResolvedTypeVisitor {
            _marker: core::marker::PhantomData,
            context: self.context,
            visit_unhandled: self.visit_unhandled,
            visit_not_found: self.visit_not_found,
            visit_composite: new_composite_fn,
            visit_variant: self.visit_variant,
            visit_sequence: self.visit_sequence,
            visit_array: self.visit_array,
            visit_tuple: self.visit_tuple,
            visit_primitive: self.visit_primitive,
            visit_compact: self.visit_compact,
            visit_bit_sequence: self.visit_bit_sequence,
        }
    }

    /// Provide a closure that's called when [`ResolvedTypeVisitor::visit_variant()`] is.
    pub fn visit_variant<NewVariantFn>(
        self,
        new_variant_fn: NewVariantFn,
    ) -> ConcreteResolvedTypeVisitor<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NotFoundFn,
        CompositeFn,
        NewVariantFn,
        SequenceFn,
        ArrayFn,
        TupleFn,
        PrimitiveFn,
        CompactFn,
        BitSequenceFn,
    >
    where
        NewVariantFn: FnOnce(
            Context,
            &mut dyn VariantIter<'resolver, ConcreteFieldIter<'resolver, TypeId>>,
        ) -> Output,
    {
        ConcreteResolvedTypeVisitor {
            _marker: core::marker::PhantomData,
            context: self.context,
            visit_unhandled: self.visit_unhandled,
            visit_not_found: self.visit_not_found,
            visit_composite: self.visit_composite,
            visit_variant: new_variant_fn,
            visit_sequence: self.visit_sequence,
            visit_array: self.visit_array,
            visit_tuple: self.visit_tuple,
            visit_primitive: self.visit_primitive,
            visit_compact: self.visit_compact,
            visit_bit_sequence: self.visit_bit_sequence,
        }
    }

    /// Provide a closure that's called when [`ResolvedTypeVisitor::visit_sequence()`] is.
    pub fn visit_sequence<NewSequenceFn>(
        self,
        new_sequence_fn: NewSequenceFn,
    ) -> ConcreteResolvedTypeVisitor<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NotFoundFn,
        CompositeFn,
        VariantFn,
        NewSequenceFn,
        ArrayFn,
        TupleFn,
        PrimitiveFn,
        CompactFn,
        BitSequenceFn,
    >
    where
        NewSequenceFn: FnOnce(Context, &'resolver TypeId) -> Output,
        TypeId: 'resolver,
    {
        ConcreteResolvedTypeVisitor {
            _marker: core::marker::PhantomData,
            context: self.context,
            visit_unhandled: self.visit_unhandled,
            visit_not_found: self.visit_not_found,
            visit_composite: self.visit_composite,
            visit_variant: self.visit_variant,
            visit_sequence: new_sequence_fn,
            visit_array: self.visit_array,
            visit_tuple: self.visit_tuple,
            visit_primitive: self.visit_primitive,
            visit_compact: self.visit_compact,
            visit_bit_sequence: self.visit_bit_sequence,
        }
    }

    /// Provide a closure that's called when [`ResolvedTypeVisitor::visit_array()`] is.
    pub fn visit_array<NewArrayFn>(
        self,
        new_array_fn: NewArrayFn,
    ) -> ConcreteResolvedTypeVisitor<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NotFoundFn,
        CompositeFn,
        VariantFn,
        SequenceFn,
        NewArrayFn,
        TupleFn,
        PrimitiveFn,
        CompactFn,
        BitSequenceFn,
    >
    where
        NewArrayFn: FnOnce(Context, &'resolver TypeId, usize) -> Output,
        TypeId: 'resolver,
    {
        ConcreteResolvedTypeVisitor {
            _marker: core::marker::PhantomData,
            context: self.context,
            visit_unhandled: self.visit_unhandled,
            visit_not_found: self.visit_not_found,
            visit_composite: self.visit_composite,
            visit_variant: self.visit_variant,
            visit_sequence: self.visit_sequence,
            visit_array: new_array_fn,
            visit_tuple: self.visit_tuple,
            visit_primitive: self.visit_primitive,
            visit_compact: self.visit_compact,
            visit_bit_sequence: self.visit_bit_sequence,
        }
    }

    /// Provide a closure that's called when [`ResolvedTypeVisitor::visit_tuple()`] is.
    pub fn visit_tuple<NewTupleFn>(
        self,
        new_tuple_fn: NewTupleFn,
    ) -> ConcreteResolvedTypeVisitor<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NotFoundFn,
        CompositeFn,
        VariantFn,
        SequenceFn,
        ArrayFn,
        NewTupleFn,
        PrimitiveFn,
        CompactFn,
        BitSequenceFn,
    >
    where
        NewTupleFn: FnOnce(Context, &mut dyn ExactSizeIterator<Item = &'resolver TypeId>) -> Output,
    {
        ConcreteResolvedTypeVisitor {
            _marker: core::marker::PhantomData,
            context: self.context,
            visit_unhandled: self.visit_unhandled,
            visit_not_found: self.visit_not_found,
            visit_composite: self.visit_composite,
            visit_variant: self.visit_variant,
            visit_sequence: self.visit_sequence,
            visit_array: self.visit_array,
            visit_tuple: new_tuple_fn,
            visit_primitive: self.visit_primitive,
            visit_compact: self.visit_compact,
            visit_bit_sequence: self.visit_bit_sequence,
        }
    }

    /// Provide a closure that's called when [`ResolvedTypeVisitor::visit_primitive()`] is.
    pub fn visit_primitive<NewPrimitiveFn>(
        self,
        new_primitive_fn: NewPrimitiveFn,
    ) -> ConcreteResolvedTypeVisitor<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NotFoundFn,
        CompositeFn,
        VariantFn,
        SequenceFn,
        ArrayFn,
        TupleFn,
        NewPrimitiveFn,
        CompactFn,
        BitSequenceFn,
    >
    where
        NewPrimitiveFn: FnOnce(Context, Primitive) -> Output,
    {
        ConcreteResolvedTypeVisitor {
            _marker: core::marker::PhantomData,
            context: self.context,
            visit_unhandled: self.visit_unhandled,
            visit_not_found: self.visit_not_found,
            visit_composite: self.visit_composite,
            visit_variant: self.visit_variant,
            visit_sequence: self.visit_sequence,
            visit_array: self.visit_array,
            visit_tuple: self.visit_tuple,
            visit_primitive: new_primitive_fn,
            visit_compact: self.visit_compact,
            visit_bit_sequence: self.visit_bit_sequence,
        }
    }

    /// Provide a closure that's called when [`ResolvedTypeVisitor::visit_compact()`] is.
    pub fn visit_compact<NewCompactFn>(
        self,
        new_compact_fn: NewCompactFn,
    ) -> ConcreteResolvedTypeVisitor<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NotFoundFn,
        CompositeFn,
        VariantFn,
        SequenceFn,
        ArrayFn,
        TupleFn,
        PrimitiveFn,
        NewCompactFn,
        BitSequenceFn,
    >
    where
        NewCompactFn: FnOnce(Context, &'resolver TypeId) -> Output,
        TypeId: 'resolver,
    {
        ConcreteResolvedTypeVisitor {
            _marker: core::marker::PhantomData,
            context: self.context,
            visit_unhandled: self.visit_unhandled,
            visit_not_found: self.visit_not_found,
            visit_composite: self.visit_composite,
            visit_variant: self.visit_variant,
            visit_sequence: self.visit_sequence,
            visit_array: self.visit_array,
            visit_tuple: self.visit_tuple,
            visit_primitive: self.visit_primitive,
            visit_compact: new_compact_fn,
            visit_bit_sequence: self.visit_bit_sequence,
        }
    }

    /// Provide a closure that's called when [`ResolvedTypeVisitor::visit_bit_sequence()`] is.
    pub fn visit_bit_sequence<NewBitSequenceFn>(
        self,
        new_bit_sequence_fn: NewBitSequenceFn,
    ) -> ConcreteResolvedTypeVisitor<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NotFoundFn,
        CompositeFn,
        VariantFn,
        SequenceFn,
        ArrayFn,
        TupleFn,
        PrimitiveFn,
        CompactFn,
        NewBitSequenceFn,
    >
    where
        NewBitSequenceFn: FnOnce(Context, BitsStoreFormat, BitsOrderFormat) -> Output,
    {
        ConcreteResolvedTypeVisitor {
            _marker: core::marker::PhantomData,
            context: self.context,
            visit_unhandled: self.visit_unhandled,
            visit_not_found: self.visit_not_found,
            visit_composite: self.visit_composite,
            visit_variant: self.visit_variant,
            visit_sequence: self.visit_sequence,
            visit_array: self.visit_array,
            visit_tuple: self.visit_tuple,
            visit_primitive: self.visit_primitive,
            visit_compact: self.visit_compact,
            visit_bit_sequence: new_bit_sequence_fn,
        }
    }
}

// our actual implementation of `ResolvedTypeVisitor` just delegates to the provided callbacks.
impl<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NotFoundFn,
        CompositeFn,
        VariantFn,
        SequenceFn,
        ArrayFn,
        TupleFn,
        PrimitiveFn,
        CompactFn,
        BitSequenceFn,
    > ResolvedTypeVisitor<'resolver>
    for ConcreteResolvedTypeVisitor<
        'resolver,
        Context,
        TypeId,
        Output,
        UnhandledFn,
        NotFoundFn,
        CompositeFn,
        VariantFn,
        SequenceFn,
        ArrayFn,
        TupleFn,
        PrimitiveFn,
        CompactFn,
        BitSequenceFn,
    >
where
    TypeId: Default + core::fmt::Debug + 'resolver,
    UnhandledFn: FnOnce(Context, UnhandledKind) -> Output,
    NotFoundFn: FnOnce(Context) -> Output,
    CompositeFn: FnOnce(Context, &mut dyn FieldIter<'resolver, TypeId>) -> Output,
    VariantFn: FnOnce(
        Context,
        &mut dyn VariantIter<'resolver, ConcreteFieldIter<'resolver, TypeId>>,
    ) -> Output,
    SequenceFn: FnOnce(Context, &'resolver TypeId) -> Output,
    ArrayFn: FnOnce(Context, &'resolver TypeId, usize) -> Output,
    TupleFn: FnOnce(Context, &mut dyn ExactSizeIterator<Item = &'resolver TypeId>) -> Output,
    PrimitiveFn: FnOnce(Context, Primitive) -> Output,
    CompactFn: FnOnce(Context, &'resolver TypeId) -> Output,
    BitSequenceFn: FnOnce(Context, BitsStoreFormat, BitsOrderFormat) -> Output,
{
    type TypeId = TypeId;
    type Value = Output;

    fn visit_unhandled(self, kind: UnhandledKind) -> Self::Value {
        (self.visit_unhandled)(self.context, kind)
    }

    fn visit_not_found(self) -> Self::Value {
        (self.visit_not_found)(self.context)
    }

    fn visit_composite<Fields>(self, mut fields: Fields) -> Self::Value
    where
        Fields: FieldIter<'resolver, Self::TypeId>,
    {
        (self.visit_composite)(
            self.context,
            &mut fields as &mut dyn FieldIter<'resolver, Self::TypeId>,
        )
    }

    fn visit_variant<Fields: 'resolver, Var>(self, variants: Var) -> Self::Value
    where
        Fields: FieldIter<'resolver, Self::TypeId>,
        Var: VariantIter<'resolver, Fields>,
    {
        // We need to collect the fields of each variant into a
        // concrete type because the Var iterator owns them. We use
        // smallvec to avoid allocating except in exceptional cases.
        let mut var_iter = variants.map(|v| Variant {
            index: v.index,
            name: v.name,
            fields: ConcreteFieldIter {
                fields: v.fields.collect(),
                idx: 0,
            },
        });

        (self.visit_variant)(self.context, &mut var_iter)
    }

    fn visit_sequence(self, type_id: &'resolver Self::TypeId) -> Self::Value {
        (self.visit_sequence)(self.context, type_id)
    }

    fn visit_array(self, type_id: &'resolver Self::TypeId, len: usize) -> Self::Value {
        (self.visit_array)(self.context, type_id, len)
    }

    fn visit_tuple<TypeIds>(self, mut type_ids: TypeIds) -> Self::Value
    where
        TypeIds: ExactSizeIterator<Item = &'resolver Self::TypeId>,
    {
        (self.visit_tuple)(
            self.context,
            &mut type_ids as &mut dyn ExactSizeIterator<Item = &'resolver Self::TypeId>,
        )
    }

    fn visit_primitive(self, primitive: Primitive) -> Self::Value {
        (self.visit_primitive)(self.context, primitive)
    }

    fn visit_compact(self, type_id: &'resolver Self::TypeId) -> Self::Value {
        (self.visit_compact)(self.context, type_id)
    }

    fn visit_bit_sequence(
        self,
        store_format: BitsStoreFormat,
        order_format: BitsOrderFormat,
    ) -> Self::Value {
        (self.visit_bit_sequence)(self.context, store_format, order_format)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TypeResolver;

    // This is mainly just to check that we can instantiate a visitor
    // without needing to provide lots of explicit types.
    #[test]
    fn check_type_inference() {
        let visitor = new((), |_, _| 1u64)
            .visit_array(|_, _, _| 2)
            .visit_composite(|_, _| 3)
            .visit_bit_sequence(|_, _, _| 4)
            .visit_compact(|_, _| 5)
            .visit_not_found(|_| 6)
            .visit_tuple(|_, _| 8)
            .visit_variant(|_, _| 9);
        // We deliberately don't implement all methods to prove that
        // type inference works regardless:
        // .visit_primitive(|_,_| 7)
        // .visit_sequence(|_,_| 10);

        struct Foo;
        impl crate::TypeResolver for Foo {
            type TypeId = u32;
            type Error = u8;

            fn resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId = Self::TypeId>>(
                &'this self,
                _type_id: &Self::TypeId,
                visitor: V,
            ) -> Result<V::Value, Self::Error> {
                Ok(visitor.visit_not_found())
            }
        }

        assert_eq!(Foo.resolve_type(&123, visitor).unwrap(), 6);
    }
}
