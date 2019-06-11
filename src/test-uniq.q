x : Attr (Bytes 4) SharedAttr;
x = 2;

data Bool : BaseType where {
  true : Attr ((u : UniquenessAttr) -> Attr Bool u) SharedAttr;
  false : Attr ((u : UniquenessAttr) -> Attr Bool u) SharedAttr;
}

b : Attr Bool SharedAttr;
b = false SharedAttr;

not : Attr ((u : UniquenessAttr) -> Attr (Attr Bool u -> Attr Bool u) SharedAttr) SharedAttr;
not u (true u) = false u;
not u (false u) = true u;

bool->int : Attr (Attr Bool SharedAttr -> Attr (Bytes 4) SharedAttr) SharedAttr;
bool->int (false SharedAttr) = 0;
bool->int (true SharedAttr) = 1;

main : Attr (Bytes 4) SharedAttr;
main = bool->int (not SharedAttr b);
