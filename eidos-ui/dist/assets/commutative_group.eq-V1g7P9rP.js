var e=`/* Equational theory that axiomatizes the concept of a commutative group */\r
{\r
  /* All that is needed here is to combine the theory for a group with the \r
     theory for a commutative monoid */\r
  subtheories {\r
    implicit {\r
      group: @group,\r
      commutative_monoid: @commutative_monoid\r
    }\r
  }\r
}`;export{e as default};