{
  description = "GHC 9.10 with HLS and cabal";
  inputs.nixpkgs.url = "nixpkgs/haskell-updates";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.simpleFlake {
      inherit self nixpkgs;
      name = "ghc910-dev-flake";
      shell = { pkgs, ... }: pkgs.mkShell {
        buildInputs = with pkgs; [
          haskell.compiler.ghc910
          haskell.packages.ghc910.haskell-language-server
        ];
      };
    };
}
