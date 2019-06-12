data World : Type 0 UniqueAttr where {
}

#extern
printInt : Attr (Bytes 4) SharedAttr -S> World -U> World;

fib : Attr (Bytes 4) SharedAttr
    -S> Attr (Bytes 4) SharedAttr
    -U> Attr (Bytes 4) SharedAttr
    -U> Attr (Bytes 4) SharedAttr;
fib x y 0 = x;
fib x y n = fib y (add x y) (sub n 1);

main : World -S> World;
main w = printInt 2 (printInt (fib 0 1 1000000000) w);
