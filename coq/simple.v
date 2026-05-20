Require Import EidosRuntime.

Axiom univ : EidosUniverse.

Definition 𝕌 : EidosSort := universeSort univ.
Definition ℙ : EidosSort := propSort univ.

Definition 𝕌_ops : MereologicalOps 𝕌 := canonicalMereologicalOps 𝕌.

Axiom S       : EidosSort.
Axiom S_sub_𝕌 : OrdinarySortWithinUniverse S univ.

Axiom i1 : MereologicalObjectOfSort S.

Axiom ax1 : WrapAssertion (sMin ℙ) (sMax ℙ)
              (forall x : Prop, IsIndividual (sMin S) (sMax S) x -> (x <-> x)).
