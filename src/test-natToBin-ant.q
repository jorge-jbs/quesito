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

parity : (n : Nat) -> Parity n;
parity Zero =
  Even Zero;
parity (Succ (Succ n')) =
  parity n'


parity : (n : Nat) -> Parity n;
parity = \n ->
  Nat-cases
    (\n -> Parity n)
    (Even Zero)
    (\n' ->
      Parity-cases
        (\nn -> \par -> Parity (Succ nn))
        (\j' -> Odd j')
        (\j' -> Even (Succ (Succ j')))
        n'
        (parity n')
    )
    n;

parity' : (n : Nat) -> Parity n;
parity' = \n ->
  Nat-cases
    (\n -> Parity n)
    (Even Zero)
    (\n' ->
      Parity-cases
        (\nn -> \par -> Parity (Succ nn))
        (\j' -> Odd j')
        (\j' -> Odd (Succ j'))
        n'
        (parity n')
    )
    n;

hue : Parity (Succ (Succ (Succ Zero)));
hue = parity (Succ (Succ (Succ Zero)));

main : Nat -> Nat;
main = \n -> plus (Succ n) (Succ n);

zero-parity : Parity Zero;
zero-parity = Even Zero;

one-parity : Parity (Succ Zero);
one-parity = Odd Zero;

two-parity : Parity (Succ (Succ Zero));
two-parity = Even (Succ Zero);

two-parity' : Parity (Succ (Succ Zero));
two-parity' = parity' (Succ (Succ Zero));
