Require Import EidosRuntime.

Axiom univ : EidosUniverse.

Definition 𝕌 : EidosSort := universeSort univ.
Definition ℙ : EidosSort := propSort univ.

Definition 𝕌_ops : MereologicalOps 𝕌 := canonicalMereologicalOps 𝕌.

Axiom S       : EidosSort.
Axiom S_sub_𝕌 : OrdinarySortWithinUniverse S univ.

Axiom R_dom     : EidosSort.
Axiom R_dom_sub : OrdinarySortWithinUniverse R_dom univ.

Axiom R : FOLRelation 2 (fun _ : Fin.t 2 => S) R_dom.
