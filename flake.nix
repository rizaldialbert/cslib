{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
  };

  outputs =
    inputs@{ self, nixpkgs, ... }:
    let
      system = "x86_64-linux";
      lib = nixpkgs.lib;
      pkgs = import nixpkgs { inherit system; };
    in
    {
      packages.${system}.default = pkgs.leanPackages.buildLakePackage {
        pname = "cslib";
        version = "0.1.0";
        src = ./.;
        leanDeps = with pkgs.leanPackages; [ ];
        lakeHash = lib.fakeHash; # all deps nix-managed; set to lib.fakeHash for Lake-managed deps
      };

      devShells.${system}.default = pkgs.mkShell {
        inputsFrom = [ self.packages.${system}.default ];
        packages = [pkgs.elan];
      };
    };
}
