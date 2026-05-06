var e=`/* Theory in coherent logic that axiomatizes the concept of an integral domain */
{
  subtheories {
    implicit {
      ring: @ring
    }
  },
  axioms {
    assertions {
      x : D,  y : D,  (prod(x, y) = zero) → ((x = zero) ∨ (y = zero));
    }
  }
}`;export{e as default};