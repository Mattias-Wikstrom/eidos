var e=`/* Equational theory that axiomatizes the concept of a semiring */\r
{\r
  subtheories {\r
    implicit {\r
      semiring_without_unity: @semiring_without_unity,\r
    }, \r
    named {\r
      multiplicative_monoid: @monoid\r
    }    \r
  },\r
  signature {\r
    one: D;\r
  },\r
  axioms {\r
    facts {\r
      semiring_without_unity.D = multiplicative_monoid.D; // There is only a single domain D\r
      semiring_without_unity.prod = multiplicative_monoid.op;\r
      one = multiplicative_monoid.n; // One is the neutral element for multiplication\r
    }\r
  }\r
}`;export{e as default};