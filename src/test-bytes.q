id : Bytes 1 -> Bytes 1;
id = \x -> x;

data Bool : Type where {
  True : Bytes 4 -> Bool;
  False : Bool;
}

fst : Bytes 4 -> Bytes 3 -> Bytes 4;
fst = \x -> \y -> x;

snd : Bytes 128 -> Bytes 128 -> Bytes 128;
snd = \x -> \y -> y;

main : Bytes 4;
main = fst 126 128;

main2 : Bool;
main2 = False;
