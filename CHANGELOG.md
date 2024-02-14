# 0.2.0

- Add a `scale_type_resolver::visitor::new()` function which allows you to construct a closure based implementation of `ResolveTypeVisitor`. This is much easier to use than implementing the trait yourselv in most cases, since the closures provided can capture state etc from the environment.

# 0.1.0

Initial release.