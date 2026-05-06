var e=`/* Equational theory that axiomatizes the concept of a ring without unity */\r
{\r
  subtheories {\r
    named {\r
      additive_group: @commutative_group\r
    },    \r
    implicit {\r
      semiring_without_unity: @semiring_without_unity,\r
    },\r
  },\r
  signature {\r
    sort D;\r
    additive_inv: D → D;\r
  },\r
  axioms {\r
    facts {\r
      semiring_without_unity.D = additive_group.D; // There is only a single domain D\r
      semiring_without_unity.sum = additive_group.op;\r
      additive_inv = additive_group.inv;\r
    }\r
  }\r
}`;export{e as default};