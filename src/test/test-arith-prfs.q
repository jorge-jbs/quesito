data Nat : Type 0 where {
  Zero : Nat;
  Succ : Nat -> Nat;
}

data Eq : (a : Type 0) -> a -> a -> Type 0 where {
  Refl : (a : Type 0) -> (x : a) -> Eq a x x;
}

plus : Nat -> Nat -> Nat;
plus =
  fix
    (Nat -> Nat -> Nat)
    (\rec -> \n -> \m ->
      Nat-cases (\_ -> Nat)
        m
        (\n' ->
          Succ (rec n' m)
        )
        n
    );


plus-Zero-eq-n : (n : Nat) -> Eq Nat (plus Zero n) n;
plus-Zero-eq-n = \n -> Refl Nat n;

doubled : Nat;
doubled = Zero --double (Succ Zero)
;

double : Nat -> Nat;
double = \n -> plus (Succ n) n;
