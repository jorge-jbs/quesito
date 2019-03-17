data Bool : Type where {
  False : Bytes 4 -> Bool;
  True : Bool;
}

data BoxedBool : Type where {
  BoxBool : Bool -> BoxedBool;
}

data Boxed : Type -> Type where {
  Box : (a : Type) -> a -> Boxed a;
}

data Nat : Type where {
  Succ : Nat -> Nat;
  Zero : Nat;
}

data Vect : Nat -> Type -> Type where {
  Nil : (a : Type) -> Vect Zero a;
  Cons : (a : Type) -> (n : Nat) -> a -> Vect n a -> Vect (Succ n) a;
}

unbox : (a : Type) -> Boxed a -> a;
unbox a (Box a x) = x;

unboxBool : BoxedBool -> Bool;
unboxBool (BoxBool x) = x;

main : BoxedBool;
main = BoxBool True;
