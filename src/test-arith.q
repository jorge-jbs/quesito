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
zero? = \x ->
  Nat-cases
    (\y -> Bool)
    True
    (\z -> False)
    x;

zero?-zero : Bool;
zero?-zero = zero? Zero;

zero?-one : Bool;
zero?-one = zero? (Succ Zero);

zero-is-zero : Eq Bool zero?-zero True;
zero-is-zero = Refl Bool True;

zero-is-not-one : Eq Bool zero?-one False;
zero-is-not-one = Refl Bool False;
