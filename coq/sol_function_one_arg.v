Require Import EidosRuntime.

Axiom univ : EidosUniverse.

Definition 𝕌 : EidosSort := universeSort univ.
Definition ℙ : EidosSort := propSort univ.

Definition 𝕌_ops : MereologicalOps 𝕌 := canonicalMereologicalOps 𝕌.

Axiom S       : EidosSort.
Axiom S_sub_𝕌 : OrdinarySortWithinUniverse S univ.

Axiom T       : EidosSort.
Axiom T_sub_𝕌 : OrdinarySortWithinUniverse T univ.

(* F.solApply                       was: axiom F : MereologicalObject -> MereologicalObject
   F.solArg.mereologicalObject      was: axiom F_1 : MereologicalObject
   F.solArg.mereologicalObjectHasSort  was: axioms F_1_min + F_1_max
   F.solRes.mereologicalObject      was: axiom F_res : MereologicalObject
   F.solRes.mereologicalObjectHasSort  was: axioms F_res_min + F_res_max
   F.solFact                        was: axiom F_fact *)
Axiom F : SOLFunctionOneArg S T.
