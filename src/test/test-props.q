data Nat : Set where {
  Zero : Nat;
  Succ : Nat -> Nat;
}

data Has : Set -> Prop where {
  has : (a : Set) -> a -> Has a;
}

data Vec : Type -> Nat -> Set where {
  Nil : (A : Type) -> Vec A Zero;
  Cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Succ n);
}

data EffVec : Type -> Has Nat -> Type 0 where {
  EffNil : (A : Type) -> EffVec A (has Zero);
  EffCons : (A : Type) -> (n : Nat) -> A -> EffVec A (has n) -> EffVec A (has (Succ n));
}

main : Nat;
main = Zero;
