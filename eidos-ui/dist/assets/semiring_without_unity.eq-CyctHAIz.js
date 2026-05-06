var e=`/* Equational theory that axiomatizes the concept of a semiring without unity */
{
  subtheories {
    implicit
    {
      additive_monoid: @commutative_monoid,
      multiplicative_semigroup: @semigroup
    }
  },
  signature {
    sort D;
    sum : D, D → D;
    zero: D;
    prod : D, D → D;
  },
  axioms {
    facts {
      //D = additive_monoid.D; // There is only a single domain D
      //D = multiplicative_semigroup.D; // There is only a single domain D
      //sum = additive_monoid.op; // sum is the binary operation in the additive monoid
      //prod = multiplicative_semigroup.op; // prod is the binary operation in the multiplicative semiring
      //zero = additive_monoid.n; // zero is the neutral element in the additive monoid
      x : D,  y : D,  z : D,  prod (x, sum(y, z)) = sum(prod (x, y), prod (x, z));
      x : D,  y : D,  z : D,  prod (sum(x, y), z) = sum(prod (x, z), prod (y, z));
    }
  }
}`;export{e as default};