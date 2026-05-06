var e=`/* Theory in coherent logic that axiomatizes the concept of a strict linear order */
{
  subtheories {
    implicit {
      strict_preorder: @strict_preorder
    }
  },
  axioms {
    assertions {
      x : D,  y : D,  (LessThan(x, y) ∨ LessThan(y, x)); // Totality
    }
  }
}`;export{e as default};