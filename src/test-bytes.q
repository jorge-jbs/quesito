data Either : Type where {
  Left : Bytes 4 -> Either;
  Right : Bytes 4 -> Either;
}

data Pair : Type where {
  MkPair : Bytes 4 -> Bytes 4 -> Pair;
}

either : Either -> Bytes 4;
either (Left x) = x;
either (Right x) = x;

comp : Either -> Either;
comp (Left x) = Left (add x x);
comp (Right x) = Left (mul x x);

sum : Pair -> Bytes 4;
sum (MkPair x y) = add y x;

main : Bytes 4;
main = either (comp (Right 3));
