id : (A : Type) -S> A -S> A;
id A x = x;

main : Attr (Bytes 4) SharedAttr;
main = id _ 2;
