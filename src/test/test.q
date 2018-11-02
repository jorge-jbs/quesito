data Bool : Type 0 where {
  True : Bool;
  False : Bool;
}

data Nat : Type 0 where {
  Zero : Nat;
  Succ : Nat -> Nat;
}

data Maybe : Type 0 -> Type 0 where {
  Nothing : (a : Type 0) -> Maybe a;
  Just : (a : Type 0) -> a -> Maybe a;
}

data List : (a : Type 0) -> Type 0 where {
  Nil : (a : Type 0) -> List a;
  Cons : (a : Type 0) -> a -> List a -> List a;
}

data Vect : (k : Nat) -> (a : Type 0) -> Type 0 where {
  VNil : (a : Type 0) -> Vect Zero a;
  VCons
     : (a : Type 0)
    -> a
    -> (k : Nat)
    -> Vect k a
    -> Vect (Succ k) a;
}

id : (a : Type 0) -> a -> a;
id = \a -> \x -> x;

main2 : Nat;
main2 = Succ (Succ Zero);

main3 : List Nat;
main3 = Cons Nat Zero (Cons Nat (Succ Zero) (Nil Nat));

main4 : Vect (Succ Zero) Nat;
main4 = VCons Nat Zero Zero (VNil Nat);

nil? : (a : Type 0) -> List a -> Bool;
a : Type 0 . nil? a (Nil a) =
  True;
a : Type 0 , x : a , l : List a . nil? a (Cons a x l) =
  False;

head : (a : Type 0) -> List a -> Maybe a;
a : Type 0 . head a (Nil a) =
  Nothing a;
a : Type 0 , x : a , l : List a . head a (Cons a x l) =
  Just a x;

main5 : Bool;
main5 = nil? Nat (Cons Nat Zero (Nil Nat));

main6 : Maybe Nat;
main6 = head Nat (Cons Nat (Succ Zero) (Cons Nat Zero (Nil Nat)));
