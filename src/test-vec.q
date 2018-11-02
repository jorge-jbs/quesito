data Nat : Type where {
  Zero : Nat;
  Succ : Nat -> Nat;
}

data Vec : Type -> Nat -> Type where {
  VNil : (a : Type) -> Vec a Zero;
  VCons
     : (a : Type)
    -> (k : Nat)
    -> a
    -> Vec a k
    -> Vec a (Succ k);
}

plus : Nat -> Nat -> Nat;
m : Nat . plus Zero m =
  m;
n : Nat , m : Nat . plus (Succ n) m =
  Succ (plus n m);

append
  : (a : Type)
 -> (n : Nat) -> Vec a n
 -> (m : Nat) -> Vec a m
 -> Vec a (plus n m);
a : Type 0 , m : Nat , v2 : Vec a m . append a Zero (VNil a) m v2 =
  v2;
a : Type 0 , x : a , n : Nat , v1 : Vec a n , m : Nat , v2 : Vec a m . append a (Succ n) (VCons a n x v1) m v2 =
  VCons a (plus n m) x (append a n v1 m v2);

main : Nat;
main = plus (Succ (Succ Zero)) (Succ Zero);

main' : Vec Nat (Succ Zero);
main' = append Nat (Succ Zero) (VCons Nat Zero Zero (VNil Nat)) Zero (VNil Nat);
