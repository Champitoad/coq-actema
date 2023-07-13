with import <nixpkgs> {};

mkShell {
    nativeBuildInputs = [
        nodejs-16_x
        (yarn.override { nodejs = nodejs-16_x; })
        electron
    ];

    ELECTRON_OVERRIDE_DIST_PATH = "${electron}/bin";
    NODE_OPTIONS = "--openssl-legacy-provider";
}