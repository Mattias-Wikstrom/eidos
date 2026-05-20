Require Import EidosRuntime.

Axiom univ : EidosUniverse.

Definition 𝕌 : EidosSort := universeSort univ.
Definition ℙ : EidosSort := propSort univ.

Definition 𝕌_ops : MereologicalOps 𝕌 := canonicalMereologicalOps 𝕌.

Axiom S       : EidosSort.
Axiom S_sub_𝕌 : OrdinarySortWithinUniverse S univ.

(* f.folFact                               was: f_fact
   f.folImagePair  bundles f#dir_img, f#inv_img, and the adjunction
   f.folArg        was: f_arg / f_1 + bounds (canonical input in S)
   f.folRes        was: f_res + bounds (canonical result in S)
   Note: f#dom is now identified with S directly (no separate domain sort) *)
Axiom f : FOLFunctionOneArg S S.

Definition fApply (X : MereologicalObject) : MereologicalObject :=
  solApply S S (imageFn S S (folImagePair S S f)) X.
