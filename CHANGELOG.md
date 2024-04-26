# 0.2.0

- Provide a `path` iterator to composite, variant and sequence callbacks in `ResolveTypeVisitor`, so that people can access the path/name of these types. The path is also exposed in the concrete visitor implementation.
- Make `TypeId` be passed by value and not lifetime. This is done because:
  1. `scale-info` uses a `TypeId = u32`, so it does not matter either way, and
  2. `scale-info-legacy` uses `TypeId = TypeName`, and needs to modify the `TypeName`s provided back in some cases, making pass-by-reference impossible.

# 0.1.1

Just a patch release to make a small addition and no API changes:

- Add a `scale_type_resolver::visitor::new()` function which allows you to construct a closure based implementation of `ResolveTypeVisitor`. This is much easier to use than implementing the trait yourself in most cases, since the closures provided can capture state etc from the environment.

# 0.1.0

Initial release.