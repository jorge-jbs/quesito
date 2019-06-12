nix-shell --run "cabal new-run -v0 < src/test-world.q | cat - src/printInt.ll | opt -S -O3 | llc -O3 | gcc -x assembler - && ./a.out"
