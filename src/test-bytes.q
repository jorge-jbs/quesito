id : Bytes 1 -> Bytes 1;
id = \x -> x;

fst : Bytes 16 -> Bytes 16 -> Bytes 16;
fst = \x -> \y -> x;

snd : Bytes 128 -> Bytes 128 -> Bytes 128;
snd = \x -> \y -> y;
