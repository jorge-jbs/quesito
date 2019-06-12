{ pkgs ? import <nixpkgs> {} }:

with pkgs;

mkShell {
  buildInputs = [
    cabal-install ghc llvm_7
    #(callPackage <nixpkgs/pkgs/development/compilers/llvm/7/llvm.nix> {})
    #llvm_7.override { enableTargets = ["arm"]; }
  ];
}
