data Nat : Type 0 where {
  Zero : Nat;
  Succ : (x : Nat) -> Nat;
}

id : (a : Type 0) -> (x : a) -> a;
id = \a -> \x -> x;

main1 : Int;
main1 = 1 + 2 + id Int 2;

main2 : Nat;
main2 = Succ (Succ Zero);
