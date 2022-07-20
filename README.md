# coq-actema

## Build

For some reason, the `dune` build of the `Loader.v` cannot load dynamically
dependencies of `atdgen`. So for now, we stick to using `coq_makefile` for
building the plugin.

Also, we want to have `dune` files to get correct LSP services in VSCode. But
`dune` will complain that the files generated by `make` conflict with its own
targets.

This is a bit dirty, but it entails three manual build scenarios:

1. when building for the first time, run:
    ```
    dune build
    make; make clean; make
    ```
2. when rebuilding *without* changing the project structure, run:
    ```
    make
    ```
3. when rebuilding *after* changing the project structure, run:
    ```
    make cleanall
    dune build
    make; make clean; make
    ```

## Update API

When updating the API in `src/logic.atd`, one needs to export it to `actema-desktop`:

```
make update-api
```