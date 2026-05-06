var e=`{
  signature {
    P : ℙ;
    Q : ℙ;
    R : ℙ;
  },
  axioms {
    assertions {
      X : ℙ,  (X ∨ ¬X);
      ¬P ∨ Q;
      ¬Q ∨ R;
      X : ℙ,  Y : ℙ,  ((¬X ∨ Y) ↔ (X → Y));
    }
  }
}`;export{e as default};