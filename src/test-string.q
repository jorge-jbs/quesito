Char : Type;
Char = Bytes 1;

data Str : Char -> Char -> Type where {
  Nil : (end : Char) -> Str end end;
  Cons : (c : Char) -> Str x end -> Str x end;
}

data CStr : Char -> Char -> Type where {
  Nil : Str end end;
  Cons : (c : Char) -> (d : Char) -> Str d end -> Str c end;
}

data CStr : Char -> Type where {
  Nil : Str 0;
  Cons : (c : Char) -> Str 0 -> Str 0;
}

data CStr : Char -> Nat -> Type where {
  Nil : Str 0 Z;
  Cons : Char -> Str 0 n -> Str 0 (S n);
}

data Str : Char -> Char -> Type where {
  Nil : (c : Char) -> Str c c;
  Cons : (c : Char) -> (c /= end) -> Str d end -> Str c end;
}

CStr : Char -> Type;
CStr c = Str c 0
