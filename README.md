# scale-type-resolver

`scale-type-resolver` provides a generic `TypeResolver` trait which can be implemented for
any type that is capable of being given a type ID and resolving that into information about
how the type is SCALE encoded. This allows libraries like `scale-decode` to be able to decode
SCALE encoded bytes using either a modern type resolver like `scale_info::PortableRegistry`,
or using entirely custom type resolvers (which we would need in order decode blocks from pre-V14
metadata).

It's unlikely that you'd depend on this library directly; more likely you'd depend on a library
like `scale-decode` which uses and re-exports the `TypeResolver` trait itself.