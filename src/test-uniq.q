x : Attr (Bytes 4) SharedAttr;
x = 2;

data Bool : BaseType where {
  true : (u : UniquenessAttr) -S> Attr Bool u;
  false : (u : UniquenessAttr) -S> Attr Bool u;
}

b : Attr Bool SharedAttr;
b = false SharedAttr;

not : (u : UniquenessAttr) -S> Attr Bool u -U> Attr Bool u;
not u (true u) = false u;
not u (false u) = true u;

bool->int : Attr Bool SharedAttr -S> Attr (Bytes 4) SharedAttr;
bool->int (false SharedAttr) = 0;
bool->int (true SharedAttr) = 1;

main : Attr (Bytes 4) SharedAttr;
main = bool->int (not SharedAttr b);
