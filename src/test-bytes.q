data Bool : Type where {
  False : Bool;
  True : Bool;
}

data BoxedBool : Type where {
  BoxBool : Bool -> BoxedBool;
}

data Boxed : Type -> Type where {
  Box : (a : Type) -> a -> Boxed a;
}

unbox : (a : Type) -> Boxed a -> a;
unbox a (Box a x) = x;

unboxBool : BoxedBool -> Bool;
unboxBool (BoxBool x) = x;

data Pair : Type -> Type -> Type where {
  MkPair : (a : Type) -> (b : Type) -> a -> b -> Pair a b;
}

data BoolPair : Type where {
  PairBool : Bool -> Bool -> BoolPair;
}

fst : (a : Type) -> (b : Type) -> Pair a b -> a;
fst a b (MkPair a b x y) = x;

snd : (a : Type) -> (b : Type) -> Pair a b -> b;
snd a b (MkPair a b x y) = y;

fstBool : BoolPair -> Bool;
fstBool (PairBool x y) = x;

sndBool : BoolPair -> Bool;
sndBool (PairBool x y) = y;

bool->int : Bool -> Bytes 4;
bool->int False = 0;
bool->int True = 1;

not : Bool -> Bool;
not False = True;
not True = False;

and : Bool -> Bool -> Bool;
and True True = True;
and a b = False;

fib : Bytes 4 -> Bytes 4;
fib 0 = 1;
fib 1 = 1;
fib n = add (fib (sub n 1)) (fib (sub n 2));

main : Bytes 4;
main = fib 11;
