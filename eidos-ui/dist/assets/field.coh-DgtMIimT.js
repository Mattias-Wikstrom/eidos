var e=`/* Theory in coherent logic that axiomatizes the concept of a field */\r
{\r
  // A field is a shew field where the multiplicative monoid is a commutative monoid\r
  subtheories {\r
    implicit {\r
      shew_field: @shew_field,\r
      integral_domain: @integral_domain,\r
    },\r
    named {\r
      multiplicative_monoid: @commutative_monoid\r
    }\r
  },\r
  axioms {\r
    assertions {\r
      multiplicative_monoid.D = D; // There is only a single domain D\r
      shew_field.prod = multiplicative_monoid.op;\r
      shew_field.one = multiplicative_monoid.n;\r
    }\r
  }\r
}`;export{e as default};