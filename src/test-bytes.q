id : (a : Type) -> a -> a;
id = \a -> \x -> x;

main2 : Bytes 1;
main2 = id (Bytes 1) 255;
