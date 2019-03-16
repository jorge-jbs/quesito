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
  Zero : Nat;
  Succ : Nat -> Nat;
}

data Vect : Nat -> Type -> Type where {
  Nil : (a : Type) -> Vect Zero a;
  Cons : (a : Type) -> (n : Nat) -> a -> Vect n a -> Vect (Succ n) a;
}

main : BoxedBool;
main = BoxBool True;
