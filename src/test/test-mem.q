data Bit : Type 0 where {
  I : Bit;
  O : Bit;
}

data Nat : Type 0 where {
  Zero : Nat;
  Succ : Nat -> Nat;
}

data Unit : Type 0 where {
  MkUnit : Unit;
}

data Pair : Type 0 -> Type 0 -> Type 0 where {
  MkPair : (a : Type 0) -> (b : Type 0) -> a -> b -> Pair a b;
}

data List : (a : Type 0) -> Type 0 where {
  Nil : (a : Type 0) -> List a;
  Cons : (a : Type 0) -> a -> List a -> List a;
}

Array : Nat -> Type 0 -> Type 0;

a : Type 0 .
Array Zero a = Unit;

n : Nat , a : Type 0 .
Array (Succ n) a = Pair a (Array n a);

zero : Nat;
zero = Zero;

one : Nat;
one = Succ zero;

two : Nat;
two = Succ one;

three : Nat;
three = Succ two;

four : Nat;
four = Succ three;

five : Nat;
five = Succ four;

six : Nat;
six = Succ five;

seven : Nat;
seven = Succ six;

eight : Nat;
eight = Succ seven;

Byte : Type 0;
Byte = Array eight Bit;

main : Nat;
main = Zero;

data UTF8Char : Type 0 where {
    OneByte : Byte -> UTF8Char;
    TwoByte : Byte -> Byte -> UTF8Char;
    ThreeByte : Byte -> Byte -> Byte -> UTF8Char;
    FourByte : Byte -> Byte -> Byte -> Byte -> UTF8Char;
}


UTF8Char : (byte : Array eight bit) -> UTF8CharType byte;

xs : Array seven Bit .
UTF8Char (MkPair Bit (Array seven Bit) O xs) = Array eight bit;

xs : Array six Bit .
UTF8Char (MkPair Bit (Array seven Bit) I (MkPair Bit (Array six Bit) O xs))  = UTF8ExtraType one;

xs : Array five Bit .
ys : Array six Bit .
UTF8Char
    (MkPair Bit (Array seven Bit) I (MkPair Bit (Array six Bit) I (MkPair Bit (Array five Bit) O xs))) 
    (MkPair Bit (Array seven Bit) I (MkPair Bit (Array six Bit) O ys)) = Pair Byte Byte;

xs : Array four Bit .
ys : Array six Bit .
zs : Array six Bit .
UTF8Char
    (MkPair Bit (Array seven Bit) I (MkPair Bit (Array six Bit) I (MkPair Bit (Array five Bit) I (MkPair Bit (Array four Bit))))) 
    (MkPair Bit (Array seven Bit) I (MkPair Bit (Array six Bit) O ys))
    = Pair Byte Byte;

UTF8Char
    (MkPair Bit (Array seven Bit) I (MkPair Bit (Array six Bit) I (MkPair Bit (Array five Bit) I (MkPair Bit (Array four Bit))))) 
    _
    = Void;

xs : Array four Bit .
UTF8Char (MkPair Bit (Array seven Bit) I (MkPair Bit (Array six Bit) I (MkPair Bit (Array five Bit) I (MkPair Bit (Array four Bit) O xs))))
    (MkPair Bit (Array seven Bit) I (MkPair Bit (Array six Bit) O ys))
    (MkPair Bit (Array seven Bit) I (MkPair Bit (Array six Bit) O ys))
    = UTF8ExtraType three;

UTF8ExtraType : Nat -> Type 0;

UTF8ExtraType Zero = Unit;
n : Nat .
UTF8ExtraType (Succ n) = Pair (Array eight Bit) (UTF8ExtraType n);


UTF8CharType : Array eight Bit -> Type 0;

xs : Array seven Bit .
UTF8CharType (MkPair Bit (Array seven Bit) O xs) = Array eight Bit;

xs : Array six Bit .
UTF8CharType (MkPair Bit (Array seven Bit) I (MkPair Bit (Array six Bit) O xs)) = UTF8ExtraType one;

xs : Array five Bit .
UTF8CharType (MkPair Bit (Array seven Bit) I (MkPair Bit (Array six Bit) I (MkPair Bit (Array five Bit) O xs))) = UTF8ExtraType two;

xs : Array four Bit .
UTF8CharType (MkPair Bit (Array seven Bit) I (MkPair Bit (Array six Bit) I (MkPair Bit (Array five Bit) I (MkPair Bit (Array four Bit) O xs)))) = UTF8ExtraType three;
