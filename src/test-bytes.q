id : Bytes 1 -> Bytes 1;
id x = x;

data Bool : Type where {
  False : Bool;
  True : Bool;
}

fst : Bytes 4 -> Bytes 3 -> Bytes 4;
fst x y = x;

snd : Bytes 128 -> Bytes 128 -> Bytes 128;
snd x y = y;

stupid : Bytes 4 -> Bytes 4 -> Bytes 4;
stupid 8 3 = 2;
stupid x 3 = x;
stupid x y = stupid y x;

fib : Bytes 4 -> Bytes 4;
fib 0 = 0;
fib 1 = 1;
fib n = add (fib (sub n 1)) (fib (sub n 2));

fib2 : Bytes 4 -> Bytes 4 -> Bytes 4 -> Bytes 4;
fib2 0 x y = x;
fib2 n x y = fib2 (sub n 1) y (add x y);

main : Bytes 4;
main = fib2 13 0 1;

main2 : Bool;
main2 = False;
