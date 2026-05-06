var e=`/* Theory in regular logic that axiomatizes the concept of a partial order */
{
  subtheories {
    implicit {
      preorder: @preorder
    }
  },
  axioms {
    assertions {
      x : D,  y : D,  (LessThanOrEq(x, y) ∧ LessThanOrEq(y, x)) → (x = y); // Symmetry
    }
  }
}`;export{e as default};