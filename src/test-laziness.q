data Nat : Type 0 where {
  Zero : Nat;
  Succ : (x : Nat) -> Nat;
}

data List : (a : Type 0) -> Type 0 where {
  Nil : (a : Type 0) -> List a;
  Cons : (a : Type 0) -> (x : a) -> (l : List a) -> List a;
}

data Vec : Type 0 -> Nat -> Type 0 where {
  VNil : (a : Type 0) -> Vec a Zero;
  VCons
     : (a : Type 0)
    -> (k : Nat)
    -> (x : a)
    -> (l : Vec a k)
    -> Vec a (Succ k);
}

repeat : Nat -> List Nat;
repeat = 
  fix
    (Nat -> List Nat)
    (\rec -> \x ->
      Cons Nat x (rec x)
    );

take : (a : Type 0) -> Nat -> List a -> List a;
take =
  fix
    ((a : Type 0) -> Nat -> List a -> List a)
    (\rec -> \a -> \n -> \l ->
      Nat-cases
        (\_ -> List a)
        (Nil a)
        (\n' ->
          List-cases
            (\b -> \_ -> List b)
            (\b -> Nil b)
            (\b -> \x -> \l' ->
              Cons b x (rec b n' l')
            )
            a
            l
        )
        n
    );

zeros : List Nat;
zeros = repeat Zero;

five-zeros : List Nat;
five-zeros = Cons Nat Zero (Cons Nat Zero (Cons Nat Zero (Cons Nat Zero (Cons Nat Zero (Nil Nat)))));

zero : Nat;
zero = Zero;

data Bool : Type 0 where {
  True : Bool;
  False : Bool;
}

null : (a : Type 0) -> List a -> Bool;
null = \a -> \l ->
  List-cases
    (\_ -> \_ -> Bool)
    (\_ -> True)
    (\_ -> \_ -> \_ -> False)
    a
    l;

data Maybe : Type 0 -> Type 0 where {
  Just : (a : Type 0) -> a -> Maybe a;
  Nothing : (a : Type 0) -> Maybe a;
}

maybe : Maybe (List Nat);
maybe = Just (List Nat) (Nil Nat);

head : (a : Type 0) -> List a -> Maybe a;
head = \a -> \l ->
  List-cases
    (\a -> \_ -> Maybe a)
    (\a -> Nothing a)
    (\a -> \x -> \l' -> Just a x)
    a
    l;

last : (a : Type 0) -> List a -> Maybe a;
last =
  fix
    ((a : Type 0) -> List a -> Maybe a)
    (\rec -> \a -> \l ->
      List-cases
        (\a -> \_ -> Maybe a)
        (\a -> Nothing a)
        (\a -> \x -> \l' ->
          List-cases
            (\a -> \_ -> Maybe a)
            (\a -> Just a x)
            (\a -> \_ -> \_ ->
              rec a l'
            )
            a
            l'
        )
        a
        l
    );

last-of : Maybe Nat;
last-of = last Nat (Cons Nat Zero (Nil Nat));

take-2 : List Nat;
take-2 = take Nat (Succ (Succ Zero)) five-zeros;

head-of : Maybe Nat;
head-of = head Nat (Cons Nat (Succ (Succ (Succ  (Succ  (Succ  (Succ  (Succ Zero))))))) (Cons Nat Zero (Nil Nat)));

is-null : Bool;
is-null = null Nat (Nil Nat);
