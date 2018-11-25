id : Bytes 1 -> Bytes 1;
id = \x -> x;

fst : Bytes 4 -> Bytes 3 -> Bytes 4;
fst = \x -> \y -> x;

snd : Bytes 128 -> Bytes 128 -> Bytes 128;
snd = \x -> \y -> y;

main : Bytes 4;
main = fst 126 128;
