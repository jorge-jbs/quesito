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

null : (a : Type 0) -> List a -> Bool;
null = \a -> \l ->
  List-cases
    (\_ -> \_ -> Bool)
    (\_ -> True)
    (\_ -> \_ -> \_ -> False)
    a
    l;

head : (a : Type 0) -> List a -> Maybe a;
head = \a -> \l ->
  List-cases
    (\a -> \_ -> Maybe a)
    (\a -> Nothing a)
    (\a -> \x -> \l' -> Just a x)
    a
    l;

main5 : Bool;
main5 = null Nat (Cons Nat Zero (Nil Nat));

main6 : Maybe Nat;
main6 = head Nat (Cons Nat (Succ Zero) (Nil Nat));
