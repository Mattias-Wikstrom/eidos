var e=`{
  signature {
    A : 𝕌;
    P : 𝕌;
    Q : 𝕌;
    R : 𝕌;
  },
  axioms {
    metafacts {
      X : 𝕌,  (X × (A - X));
      (A - P) × Q;
      (A - Q) × R;
      X : 𝕌,  Y : 𝕌,  (((A - X) × Y) ∸ (Y - X));
    }
  }
}`;export{e as default};