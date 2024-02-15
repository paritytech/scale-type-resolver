# 0.1.1

Just a patch release to make a small addition and no API changes:

- Add a `scale_type_resolver::visitor::new()` function which allows you to construct a closure based implementation of `ResolveTypeVisitor`. This is much easier to use than implementing the trait yourself in most cases, since the closures provided can capture state etc from the environment.

# 0.1.0

Initial release.