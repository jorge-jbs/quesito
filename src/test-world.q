data World : Type 0 UniqueAttr where {
}

#extern
printInt
    : Attr (Attr (Bytes 4) SharedAttr
    -> Attr (World
    -> World) SharedAttr) SharedAttr;

fib : Attr (Attr (Bytes 4) SharedAttr
    -> Attr (Attr (Bytes 4) SharedAttr
    -> Attr (Attr (Bytes 4) SharedAttr
    -> Attr (Bytes 4) SharedAttr) SharedAttr) SharedAttr) SharedAttr;
fib x y 0 = x;
fib x y n = fib y (add x y) (sub n 1);

main : Attr (World -> World) SharedAttr;
main w = printInt 2 (printInt (fib 0 1 1000000000) w);
