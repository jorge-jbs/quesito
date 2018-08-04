data Nat : Type 0 where {
  Zero : Nat;
  Succ : (x : Nat) -> Nat;
}

data List : (a : Type 0) -> Type 0 where {
  Nil : (a : Type 0) -> List a;
  Cons : (a : Type 0) -> (x : a) -> (l : List a) -> List a;
}

id : (a : Type 0) -> (x : a) -> a;
id = \a -> \x -> x;

main1 : Int;
main1 = 1 + 2 + id Int 2;

main2 : Nat;
main2 = Succ (Succ Zero);

main3 : List Nat;
main3 = Cons Nat Zero (Cons Nat (Succ Zero) (Nil Nat));
