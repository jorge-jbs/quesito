data Nat : Type 0 where {
  Zero : Nat;
  Succ : Nat -> Nat;
}

data Bool : Type 0 where {
  True : Bool;
  False : Bool;
}

data Eq : (a : Type 0) -> a -> a -> Type 0 where {
  Refl : (a : Type 0) -> (x : a) -> Eq a x x;
}

zero? : Nat -> Bool;
zero? =
  Nat-cases
    (\y -> Bool)
    True
    (\z -> False);

zero?-zero : Bool;
zero?-zero = zero? Zero;

zero?-one : Bool;
zero?-one = zero? (Succ Zero);

zero-is-zero : Eq Bool zero?-zero True;
zero-is-zero = Refl Bool True;

zero-is-not-one : Eq Bool zero?-one False;
zero-is-not-one = Refl Bool False;

baia : Eq Bool True False;
baia = baia;

plus : Nat -> Nat -> Nat;
plus = \n -> \m ->
  Nat-cases
    (\_ -> Nat)
    m
    (\n' ->
      Succ (plus n' m)
    )
    n;

fib : Nat -> Nat;
fib = \n ->
  Nat-cases
    (\_ -> Nat)
    (Succ Zero)
    (\n' ->
      Nat-cases (\_ -> Nat)
        (Succ Zero)
        (\n'' ->
          plus (fib n'') (fib n')
        )
        n'
    )
    n;

main : Nat;
main = plus (Succ (Succ (Succ Zero))) (Succ (Succ Zero));

main' : Nat;
main' = fib (Succ (Succ (Succ (Succ (Succ Zero)))));
