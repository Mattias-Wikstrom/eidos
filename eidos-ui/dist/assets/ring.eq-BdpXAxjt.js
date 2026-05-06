var e=`/* Equational theory that axiomatizes the concept of a ring */\r
{\r
  /* All that is needed here is to combine the theory for a ring without unity with the \r
    theory for a semiring */\r
  subtheories {\r
    implicit {\r
      ring_without_unity: @ring_without_unity, // Provides additive inverses\r
      semiring: @semiring // Provides a multiplicative unit\r
    }\r
  }\r
}`;export{e as default};