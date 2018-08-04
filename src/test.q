data Nat : Type 0 where {
  Zero : Nat;
  Succ : (x : Nat) -> Nat;
}

data List : (a : Type 0) -> Type 0 where {
  Nil : (a : Type 0) -> List a;
  Cons : (a : Type 0) -> (x : a) -> (l : List a) -> List a;
}

data Vect : (k : Nat) -> (a : Type 0) -> Type 0 where {
  VNil : (a : Type 0) -> Vect Zero a;
  VCons
     : (a : Type 0)
    -> (x : a)
    -> (k : Nat)
    -> (l : Vect k a)
    -> Vect (Succ k) a;
}

id : (a : Type 0) -> (x : a) -> a;
id = \a -> \x -> x;

main1 : Int;
main1 = 1 + 2 + id Int 2;

main2 : Nat;
main2 = Succ (Succ Zero);

main3 : List Nat;
main3 = Cons Nat Zero (Cons Nat (Succ Zero) (Nil Nat));

main4 : Vect (Succ Zero) Nat;
main4 = VCons Nat Zero Zero (VNil Nat);
