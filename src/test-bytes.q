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

main : BoxedBool;
main = BoxBool True;
