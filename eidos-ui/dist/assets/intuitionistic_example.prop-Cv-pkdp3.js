var e=`{
  signature {
    P1 : ℙ;
    P2 : ℙ;
    Q : ℙ;
    MyOtherProp : ℙ;
    MyProp : ℙ;
  },
  axioms {
    assertions {
      P1 ∨ Q;
      P1 ∨ P2;
      Q → (MyProp ∧ ¬P1);
      (P2 → ⊥) ↔ (¬MyProp);
      X : ℙ,  (X → (¬¬X));
      Q ← P1;
    }
  }
}`;export{e as default};