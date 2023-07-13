with import <nixpkgs> {};

mkShell {
    nativeBuildInputs = [
        nodejs_18
        (yarn.override { nodejs = nodejs_18; })
        electron
    ];

    ELECTRON_OVERRIDE_DIST_PATH = "${electron}/bin";
    NODE_OPTIONS = "--openssl-legacy-provider";
}