data Bool : Type 0 where {
  True : Bool;
  False : Bool;
}

data Nat : Type 0 where {
  Zero : Nat;
  Succ : Nat -> Nat;
}

data List : (a : Type 0) -> Type 0 where {
  Nil : (a : Type 0) -> List a;
  Cons : (a : Type 0) -> a -> List a -> List a;
}

plus : Nat -> Nat -> Nat;
m : Nat . plus Zero m =
  m;
n : Nat , m : Nat . plus (Succ n) m =
  Succ (plus n m);

data Parity : Nat -> Type 0 where {
  Even : (m : Nat) -> Parity (plus m m);
  Odd : (m : Nat) -> Parity (Succ (plus m m));
}

main : Parity (Succ (Succ Zero));
main = Even (Succ Zero);

data Eq : (a : Type 0) -> a -> a -> Type 0 where {
  Refl : (a : Type 0) -> (x : a) -> Eq a x x;
}

plus-two : (n : Nat) -> Eq Nat (plus (Succ n) (Succ n)) (Succ (Succ (plus n n)));
plus-two Zero =
  Refl Nat (Succ (Succ Zero));
n' : Nat . plus-two (Succ n') =
  Refl Nat (Succ (Succ (plus n' (Succ (Succ n')))));

parity' : (n : Nat) -> Parity n -> Parity (Succ (Succ n));
j : Nat . parity' (plus j j) (Even j) =
  Even (Succ j);

parity : (n : Nat) -> Parity n;
parity Zero =
  Even Zero;
n'' : Nat . parity (Succ (Succ n'')) =
  parity n'';

zero-parity : Parity Zero;
zero-parity = Even Zero;

one-parity : Parity (Succ Zero);
one-parity = Odd Zero;

two-parity : Parity (Succ (Succ Zero));
two-parity = Even (Succ Zero);

two-parity' : Parity (Succ (Succ Zero));
two-parity' = parity' (Succ (Succ Zero));
