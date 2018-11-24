id : Bytes 1 -> Bytes 1;
id = \x -> x;

fst : Bytes 1 -> Bytes 1 -> Bytes 1;
fst = \x -> \y -> x;

snd : Bytes 1 -> Bytes 1 -> Bytes 1;
snd = \x -> \y -> y;

main2 : Bytes 1;
main2 = fst (id 255) 231;
