data Eq : (a : Type 0) -> (x : a) -> (y : a) -> Type 0 where {
  Refl : (a : Type 0) -> (x : a) -> Eq a x x;
}

data Nat : Type 0 where {
  Zero : Nat;
  Succ : (x : Nat) -> Nat;
}

zero-eq-zero : Eq Nat Zero Zero;
zero-eq-zero = Refl Nat Zero;

one-eq-one : Eq Nat (Succ Zero) (Succ Zero);
one-eq-one = Refl Nat (Succ Zero);
