Support for the dune build system
=================================

**NOTE:** in case of problem with the dune build, you can ask @lepigre or
@Blaisorblade for help.

The library can be built using dune by running `dune build`. Note that `dune`
needs to be installed separately with `opam install dune`, as it is currently
not part of the dependencies of the project.

Useful links:
- [dune documentation](https://dune.readthedocs.io)
- [coq zulip channel](https://coq.zulipchat.com/#narrow/stream/240550-Dune-devs-.26-users)


Editor support
--------------

Good dune support in editors is lacking at the moment, but there are tricks you
can play to make it work.

One option is to configure your editor to invoke the `dune coq top` command
instead of `coqtop`, but that is not easy to configure.

Another option is to change the `_CoqProject` file to something like:
```
-Q stdpp stdpp
-Q _build/default/stdpp stdpp
-Q stdpp_bitvector stdpp.bitvector
-Q _build/default/stdpp_bitvector stdpp.bitvector
-Q stdpp_unstable stdpp.unstable
-Q _build/default/stdpp_unstable stdpp.unstable
```
Note that this includes two bindings for each logical path: a binding to a
folder in the source tree (where editors will find the `.v` files), and a
binding to the same folder under `_build/default` (where editors will find
the corresponding `.vo` files). The binding for a source folder must come
before the binding for the corresponding build folder, so that editors know
to jump to source files in the source tree (and not their read-only copy in
the build folder).

If you do this, you still need to invoke `dune` manually to make sure that the
dependencies of the file you are stepping through are up-to-date. To build a
single file, you can do, e.g., `dune build stdpp/options.vo`. To build only
the `stdpp` folder, you can do `dune build stdpp`.
