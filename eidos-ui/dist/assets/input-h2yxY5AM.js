var e=`{
    /* Comment 1 */
	signature {
        sort S;
        sort MySort;
        sort B;
        sort E;
        A subsort E;
        C subquotient B;
        D quotient B;
        f : S, S → B;
        g : 𝔻;
        P ⊆ 𝔻;
        R ⊆ S, B;
        R2 ⊆ S, B, B;
        d : S, B → C;
        G : S, B, B → C;
    },
    axioms {
        assertions {
            // Comment 2
            X ⊆ sub.S, Y ⊆ sub.S, ∀Z ⊆ S (∃Y ⊆ S (Y ⊆ Y)↔((X ⊆ Y)→((Z ⊆ Y)←((Y ⊆ Y)∨(Y ⊆ Y)))));
            X ⊆ sub.S, Y ⊆ sub.S, (Y ⊆ Y)↔((Y ⊆ <<sub>>(∃Y ⊆ S Y))→((f(Y, Y) ⊆ f(f(X, X), Y))←((Y ⊆ Y)∨(Y ⊆ Y))));
            x : Q, Y ⊆ Q, (Y ⊆ Y)↔(Y ⊆ Y);
            x : S, y : S,  f(y, x) =_S f(x, y);
            ⊥ ∨ ¬sub.⊤;
            y : S,  (f(f(y, y), y) ⊆ f(f(y, y), Σy:𝔻(y)));
            x : S,  x = x;
            ¬⊥;
            //x : S,  ⊥ ∨ ¬x⊆x ∨ x≤x ∧ ¬sub.h(x)=sub.h(x) ∧ ¬sub.h(x)=sub.h(x);
        },
        facts {
        },
        metafacts {
        }
    },
    subtheories {
        implicit {
            sub1: {
                signature {
                    sort Q;
                }
            }
        },
        named {
            sub: @ext
        },
        reflection {
            sub2: {
                signature {
                    sort Z;
                    a : Z;
                    f : Z, Z → Z;
                },
                axioms {
                    assertions {
                        a = f(a, a + a);
                    }
                }
            }
        }
    }
}
`;export{e as default};