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

data Pair : Type -> Type -> Type where {
  MkPair : (a : Type) -> (b : Type) -> a -> b -> Pair a b;
}

unbox : (a : Type) -> Boxed a -> a;
unbox a (Box a x) = x;

unboxBool : BoxedBool -> Bool;
unboxBool (BoxBool x) = x;

fst : (a : Type) -> (b : Type) -> Pair a b -> a;
fst a b (MkPair a b x y) = x;

snd : (a : Type) -> (b : Type) -> Pair a b -> b;
snd a b (MkPair a b x y) = y;

bool->int : Bool -> Bytes 4;
bool->int False = 0;
bool->int True = 1;

sndBool : (a : Type) -> Pair a Bool -> Bool;
sndBool a (MkPair a Bool x y) = y;

not : Bool -> Bool;
not False = True;
not True = False;

main : Bytes 4;
main = bool->int (not (unboxBool (BoxBool False)));
