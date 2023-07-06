{
  description = "Experiments with graph automorphisms in Haskell";

  nixConfig = {
    extra-experimental-features = "nix-command flakes";
  };

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    nix-filter.url = "github:numtide/nix-filter";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = inputs: inputs.flake-utils.lib.eachDefaultSystem (system:
    with builtins;
    let
      inherit (inputs.nixpkgs) lib;
      pkgs = import inputs.nixpkgs { inherit system; };
      haskellPackages = pkgs.haskellPackages;

      haskellPackagesOverride = ps:
        ps.override
          {
            overrides = self: super: {
              graph-symmetries =
                (self.callCabal2nix "graph-symmetries" ./. { });
            };
          };

    in
    {
      devShells.default =
        let
          ps = haskellPackagesOverride haskellPackages;
        in
        ps.shellFor {
          packages = ps: with ps; [
            graph-symmetries
          ];
          withHoogle = true;
          nativeBuildInputs = with pkgs; with ps; [
            # Building and testing
            cabal-install
            haskell-language-server
            # Formatters
            fourmolu
            cabal-fmt
            nixpkgs-fmt
          ];
        };
      # The formatter to use for .nix files (but not .hs files)
      # Allows us to run `nix fmt` to reformat nix files.
      formatter = pkgs.nixpkgs-fmt;
    }
  );
}
