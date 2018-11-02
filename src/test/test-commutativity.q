data Nat : Type where {
  Zero : Nat;
  Succ : Nat -> Nat;
}

data Eq : (a : Type) -> a -> a -> Prop where {
  Refl : (a : Type) -> (x : a) -> Eq a x x;
}

plus : Nat -> Nat -> Nat;
m : Nat . plus Zero m =
  m;
n : Nat , m : Nat . plus (Succ n) m =
  Succ (plus n m);

replace : (a : Type) -> (P : a -> Prop) -> (x : a) -> (y : a) -> Eq a x y -> P x -> P y;
a : Type , P : a -> Prop , x : a , Px : P x . replace a P x x (Refl a x) Px = Px;

eq-trans : (a : Type) -> (x : a) -> (y : a) -> Eq a x y -> Eq a y x;
a : Type , x : a . eq-trans a x x (Refl a x) =
  Refl a x;

n-plus-zero : (n : Nat) -> Eq Nat n (plus n Zero);
n-plus-zero Zero =
  Refl Nat Zero;
n' : Nat . n-plus-zero (Succ n') =
  replace
    Nat
    (\x -> Eq Nat (Succ x) (Succ (plus n' Zero)))
    (plus n' Zero)
    n'
    (eq-trans Nat n' (plus n' Zero) (n-plus-zero n'))
    (Refl Nat (Succ (plus n' Zero)));

take-out-succ : (n : Nat) -> (m : Nat) -> Eq Nat (plus n (Succ m)) (Succ (plus n m));
m : Nat . take-out-succ Zero m =
  Refl Nat (Succ m);
n' : Nat , m : Nat . take-out-succ (Succ n') m =
  replace
    Nat
    (\x -> Eq Nat (Succ x) (Succ (Succ (plus n' m))))
    (Succ (plus n' m))
    (plus n' (Succ m))
    (eq-trans
      Nat
      (plus n' (Succ m))
      (Succ (plus n' m))
      (take-out-succ n' m))
    (Refl Nat (Succ (Succ (plus n' m))));

n-plus-succ : (n : Nat) -> (m : Nat) -> Eq Nat (Succ (plus n m)) (plus n (Succ m));
m : Nat . n-plus-succ Zero m =
  Refl Nat (Succ m);
n' : Nat , m : Nat . n-plus-succ (Succ n') m =
  replace
    Nat
    (\x -> Eq Nat (Succ x) (Succ (plus n' (Succ m))))
    (plus n' (Succ m))
    (Succ (plus n' m))
    (take-out-succ n' m)
    (Refl Nat (Succ (plus n' (Succ m))));

plus-commutes : (n : Nat) -> (m : Nat) -> Eq Nat (plus n m) (plus m n);
m : Nat . plus-commutes Zero m =
  n-plus-zero m;
n' : Nat , m : Nat . plus-commutes (Succ n') m =
  replace
    Nat
    (\x -> Eq Nat (Succ (plus n' m)) x)
    (Succ (plus m n'))
    (plus m (Succ n'))
    (n-plus-succ m n')
    (replace
      Nat
      (\x -> Eq Nat (Succ (plus n' m)) (Succ x))
      (plus n' m)
      (plus m n')
      (plus-commutes n' m)
      (Refl Nat (Succ (plus n' m)))
    );

zero+one-eq-one+zero : Eq Nat (plus Zero (Succ Zero)) (plus (Succ Zero) Zero);
zero+one-eq-one+zero = plus-commutes Zero (Succ Zero);
