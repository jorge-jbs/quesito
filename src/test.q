id : (a : Type 0) -> (x : a) -> a;
id = \a -> \x -> x;

main : Int;
main = (1 + 2) + (id Int 2);
