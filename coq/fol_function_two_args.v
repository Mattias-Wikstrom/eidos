Require Import EidosRuntime.

Axiom univ : EidosUniverse.

Definition 𝕌 : EidosSort := universeSort univ.
Definition ℙ : EidosSort := propSort univ.

Definition 𝕌_ops : MereologicalOps 𝕌 := canonicalMereologicalOps 𝕌.

Axiom S       : EidosSort.
Axiom S_sub_𝕌 : OrdinarySortWithinUniverse S univ.

Axiom T       : EidosSort.
Axiom T_sub_𝕌 : OrdinarySortWithinUniverse T univ.

Axiom U       : EidosSort.
Axiom U_sub_𝕌 : OrdinarySortWithinUniverse U univ.

(* f#dom: the product sort for argument tuples (S, T); distinct from S and T *)
Axiom f_dom     : EidosSort.
Axiom f_dom_sub : OrdinarySortWithinUniverse f_dom univ.

(* f : S × T → U
   f.folFnProductStructure              was: f_dom projections + tuple
   f.folFnImagePair.imageFn.apply       was: f_dir_img / def f
   f.folFnImagePair.inverseImageFn      was: f_inv_img
   f.folFnImagePair.adjunction          was: f_image_adjunction
   f.folFnArg                           was: f_arg + bounds
   f.folFnArgN Fin.F1                   was: f_1 + bounds (in S)
   f.folFnArgN (Fin.FS Fin.F1)          was: f_2 + bounds (in T)
   f.folFnRes                           was: f_res + bounds (in U)
   f.folFnFact                          was: f_fact *)
Axiom f : FOLFunction 2
            (fun i : Fin.t 2 => match i with Fin.F1 => S | _ => T end)
            U f_dom.
