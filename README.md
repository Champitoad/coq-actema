# coq-actema

This repository contains the source code for 3 different components:

- `/`: the coq-actema plugin for the [Coq proof assistant](https://coq.inria.fr/). It exposes a new tactic `actema` that sends Coq goals to a graphical interface called Actema, and compiles the actions performed by the user in Actema back to Coq tactics;
- `/actema-desktop/`: the frontend of Actema written in [Vue](https://vuejs.org/guide/introduction.html) and packaged as a desktop application with [Electron](https://www.electronjs.org/). It defines in `src/server.js` the HTTP protocol used to communicate with the plugin, by implementing directly an HTTP server with [Node.js](https://nodejs.org/en);
- `/actema-desktop/prover/`: the backend of Actema written in [OCaml](https://ocaml.org/). It is transpiled to JavaScript with [js_of_ocaml](http://ocsigen.org/js_of_ocaml/latest/manual/overview), so that it can be run in the browser engine of Electron. It also defines in `libs/api/` the API used to exchange data in HTTP messages. The data schemas are described in a language-agnostic format called [ATD](https://atd.readthedocs.io/en/latest/atd-project.html) (files ending in `.atd`), which is then used to auto-generate (de)serialization helpers in OCaml that are reused in the plugin. Some domain-specific helpers to manipulate this data in OCaml are also provided.

## Setting up the environment

The recommended way to setup your development environment (which will avoid a _lot_ of headaches) is to use the [nix package manager](https://zero-to-nix.com/). It is important to have the _flake_ feature of nix enabled, but this will be the case by default if you followed installation instructions from [Zero to Nix's quickstart guide](https://zero-to-nix.com/start/install). Then you just need to follow these steps:

1. Get in the directory of the component you want to develop, e.g. for the backend:
```bash
cd actema-desktop/prover
```
2. Install dependencies and set environment variables in your shell with nix:
```bash
nix develop
```
3. (Optional) Launch your IDE of choice from the correctly-configured shell in order to get LSP services in OCaml. Currently for this to work you need to be in the root directory. For instance if you use VSCode:
```bash
code .
```

Otherwise you will need to perform the delicate work of `nix develop` (step 2) manually. Since this process is quite platform-dependent and error-prone, we only suggest steps to follow, and probably miss some of them.

### Actema backend

TODO

### Actema frontend

TODO

### Coq plugin

The environment variable APIDIR should be set to the build directory of dune
for the backend of Actema:
```bash
export APIDIR=actema-desktop/prover/_build/default/libs/api
```

## Building and running (development)

In this section we assume that you are in a correctly-configured shell, typically the one provided by `nix develop`.

### Coq plugin

Building is as simple as:
```bash
make
```
Then you can step through some example Coq files in the `/theories/` folder, e.g. `Tautos.v`. Note that for the `actema` tactic to work, you need to have Actema already launched separately (see [next section](#actema-frontend-1)).

### Actema frontend

Make sure you are in the correct directory:

```bash
cd actema-desktop # from the root
```

To both build and run the electron app:
```bash
npm run electron:serve
```
Note that hot reload is enabled: you do not need to restart the app every time you change some file in `src/`. This also applies to the embedded backend `public/prover.js`, meaning that if you want to update the backend after compiling it (see [next section](#actema-backend-1)) you just need to run:
```bash
npm run build-prover
```

### Actema backend

Make sure you are in the correct directory:

```bash
cd actema-desktop/prover # from the root
```

If you use nix and do not intend to modify the source code of the backend, then there is no need to compile it yourself: nix will take care of it when building the plugin (see the [Coq plugin section](#coq-plugin-1)).

Otherwise you will need to rebuild it manually:
```bash
make
```

## Building and running (production)

TODO

## Making the LSP work when developing the plugin

For some reason, the `dune` build of the `Loader.v` cannot load dynamically dependencies of `atdgen`. So for now, we stick to using `coq_makefile` for building the plugin.

Also, we want to have `dune` files to get correct LSP services in `<insert-your-favorite-IDE>`. But `dune` will complain that the files generated by `make` conflict with its own targets.

This is a bit dirty, but it entails three manual build scenarios:

1. when building for the first time, run:
    ```
    make api
    dune build
    make
    ```
2. when rebuilding *without* changing the project structure, run:
    ```
    make
    ```
3. when rebuilding *after* changing the project structure, run:
    ```
    make clean
    dune build
    make
    ```