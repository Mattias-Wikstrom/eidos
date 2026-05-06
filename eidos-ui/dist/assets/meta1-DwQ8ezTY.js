var e=`/* Theory that demonstrates how one theory can be a metafacts theory for another theory */\r
{\r
  signature {\r
    sort S; // Everything in object_theory\r
    sort T; // The propositions in object_theory\r
    sort U; // The domain of object_theory\r
    a : U; \r
    b : U;\r
  },\r
  axioms {\r
    assertions {\r
      // The following will make the sort S encompass everything in object_theory\r
      S#max = object_theory.𝕌#max;\r
      S#min = object_theory.𝕌#min;\r
\r
      // The following will make T encompass the propositions in object_theory\r
      T#max = object_theory.⊥;\r
      T#min = object_theory.⊤;\r
    \r
      U = object_theory.D;\r
\r
      // The following will make object_theory prove that either a or b is zero\r
      object_theory.prod(a, b) = object_theory.zero; \r
    \r
      // That does /not/ mean that the following is provable here:\r
      (a = object_theory.zero) ∨ (b = object_theory.zero);\r
\r
      // The following is what is actually provable\r
      // object_theory.⊤ → ((a = object_theory.zero) ∨ (b = object_theory.zero));\r
    },\r
  },\r
  subtheories {\r
    /* Using a coherent theory as the object_theory for demo purposes */\r
    named {\r
      object_theory: @integral_domain \r
    }\r
  }\r
}\r
`;export{e as default};