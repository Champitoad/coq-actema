{
  inputs = {
    nixpkgs.url = "nixpkgs";
    old.url = "nixpkgs/nixos-23.05";
  };
  outputs = { self, nixpkgs, old }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      oldpkgs = import old {
        system = "x86_64-linux";
	config = {
          permittedInsecurePackages = [
	    "nodejs-14.21.3"
	    "nodejs-16.20.2"
	    "openssl-1.1.1w"
          ];
        };
      };
    in {
    devShell.x86_64-linux = pkgs.mkShell {
      packages = [
        oldpkgs.nodejs_16
      ];
    };
  };
}
