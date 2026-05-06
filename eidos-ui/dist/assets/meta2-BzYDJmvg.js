var e=`\r
/* Theory that demonstrates how to interpret predicate logic using quantified propositional logic */\r
{\r
  signature {\r
    D_max : Prop; \r
    D_min : Prop;\r
\r
    T_max : Prop; \r
    T_min : Prop;\r
\r
    a : object_theory.D;\r
    b : object_theory.D;\r
  },\r
  axioms {\r
    assertions {\r
      // Make the propositions D_min and D_max delimit the domain of the object_theory\r
      D_max#mereological = object_theory.D#max;\r
      D_min#mereological = object_theory.D#min;\r
\r
      // Make the propositions T_min and T_max delimit the propositions of the object_theory\r
      T_max#mereological = object_theory.⊥#mereological;\r
      T_min#mereological = object_theory.⊤#mereological;\r
\r
      // This ensures that a is within the domain of object_theory\r
      D_min ≤ a;\r
      a ≤ D_max;\r
\r
      // This ensures that b is within the domain of object_theory\r
      b ⇒ D_min = 𝕌#min; // Using D_min ≤ b would also work\r
      D_max ⇒ b = 𝕌#min;\r
\r
      // The following will make object_theory prove that either a or b is zero\r
      object_theory.prod(a, b) = object_theory.zero;\r
\r
      // That does /not/ mean that the following is provable here:\r
      (a = object_theory.zero) ∨ (b = object_theory.zero);\r
\r
      // The following is what is actually provable:\r
      object_theory.⊤ → ((a = object_theory.zero) ∨ (b = object_theory.zero));\r
    }\r
  },\r
  subtheories {\r
    /* Using a coherent theory as the object_theory for demo purposes */\r
    named {\r
      object_theory: @integral_domain\r
    } \r
  }\r
}`;export{e as default};