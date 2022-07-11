with import <nixpkgs> {};

mkShell {
    nativeBuildInputs = [
        nodejs
        yarn
        electron
    ];

    ELECTRON_OVERRIDE_DIST_PATH = "${electron}/bin";
}