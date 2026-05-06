var e=`/* Theory in regular logic that axiomatizes the concept of an upper semi-lattice */
{
  subtheories {
    implicit {
      partial_order: @partial_order
    }
  },
  signature {
    join : D, D → D;
  },
  axioms {
    assertions {
      x : D,  y : D,  LessThanOrEq(x, join(x, y));
      x : D,  y : D,  LessThanOrEq(y, join(x, y));
      x : D,  y : D,  z : D,  (LessThanOrEq(x, z) ∧ LessThanOrEq(y, z)) → LessThanOrEq(join(x, y), z);
    }
  }
}`;export{e as default};