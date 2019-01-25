id : Bytes 1 -> Bytes 1;
id = \x -> x;

data Bool : Type where {
  False : Bool;
  True : Bool;
}

fst : Bytes 4 -> Bytes 3 -> Bytes 4;
fst = \x -> \y -> x;


stupid : Bytes 4 -> Bytes 4 -> Bytes 4;

stupid 8 3 = 2;

x : Bytes 4 .
stupid x 3 = x;

x : Bytes 4 , y : Bytes 4 .
stupid x y = stupid y x;


fib : Bytes 4 -> Bytes 4;
fib 0 = 0;
fib 1 = 1;
n : Bytes 4 .
fib n = add (fib (sub n 1)) (fib (sub n 2));

main : Bytes 4;
main = stupid 3 4;


snd : Bytes 128 -> Bytes 128 -> Bytes 128;
snd = \x -> \y -> y;

main2 : Bool;
main2 = False;
