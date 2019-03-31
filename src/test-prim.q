data Bit : Type where {
  I : Bit;
  O : Bit;
}

data Pair : Type -> Type -> Type where {
  pair : (a : Type) -> (b : Type) -> a -> b -> Pair a b;
}

data Unit : Type where {
  unit : Unit;
}

Int : Type;
Int = Bytes 4;

#total
Vec : Int -> Type -> Type;
Vec 0 a = Unit;
Vec (add n 1) a = Pair a (Vec n a);

head : (n : Int) -> (a : Type) -> Vec (add n 1) a -> a;
head n a (pair a (Vec n a) x xs) = x;

tail : (n : Int) -> (a : Type) -> Vec (add n 1) a -> Vec n a;
tail n a (pair a (Vec n a) x xs) = xs;

Byte : Type;
Byte = Vec 8 Bit;

two : Int -> Int -> Vec 2 Int;
two x y = pair (Bytes 4) (Vec 1 (Bytes 4)) x (pair (Bytes 4) Unit y unit);

three : Int -> Int -> Int -> Vec 3 Int;
three x y z = pair Int (Vec 2 Int) x (two y z);

main : Bytes 4;
main = head 1 (Bytes 4) (tail 2 (Bytes 4) (three 1 3 6));
