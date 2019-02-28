data Either : Type where {
  Left : Bytes 4 -> Either;
  Right : Bytes 4 -> Either;
}

data Bool : Type where {
  False : Bool;
  True : Bool;
}

notB : Bool -> Bool;
notB True = False;
notB False = True;

data BoxedBool : Type where {
  BoxBool : Bool -> BoxedBool;
}

data Pair : Type where {
  MkPair : Bytes 4 -> Bytes 4 -> Pair;
}

unbox : BoxedBool -> Bool;
unbox (BoxBool b) = b;

either : Either -> Bytes 4;
either (Left x) = x;
either (Right x) = x;

comp : Either -> Either;
comp (Left x) = Left (add x x);
comp (Right x) = Right (mul x x);

sum : Pair -> Bytes 4;
sum (MkPair x y) = add y x;

main : Bool;
main = notB (unbox (BoxBool False));
