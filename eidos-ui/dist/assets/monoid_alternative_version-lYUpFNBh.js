var e=`{
  signature {
    sort D; // D is the domain
    op : D, D → D; // op is a binary operation
    sort D; // D is the domain
    n : D; // n will be the neutral element
  },
  axioms {
    facts {
      x : D,  y : D,  z : D,  op(op(x, y), z) = op(x, op(y, z)); // Associativity
      x : D,  x = op(n, x); // n is a neutral element for left multiplication
      x : D,  x = op(x, n); // n is a neutral element for right multiplication
    },
    metafacts {
      x : D,  y : D,  ((op#1 ∸ x) + (op#2 ∸ y)) ⇒ (op#res ∸ op(x, y)) = 𝕌#min;
      x : D,  y : D,  op(x, y) = Σz : D (((op#1 ∸ x) + (op#2 ∸ y)) ⇒ (op#res ∸ z)) = 𝕌#min;
    }
  }
}
`;export{e as default};