var e=`{ 
  signature { 
    sort S; 
    sort T; 
    S1 ⊆ S; 
    g : S → S; 
    G : S → S; 
    idS : S → S;
  },
  axioms {
    assertions {
      X ⊆ S,  (idS(X) = X);
    }
  }
}
`;export{e as default};