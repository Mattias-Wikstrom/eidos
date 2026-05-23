(* Eidos compiler runtime library *)

Require Import Fin.

(* A mereological object is a Prop *)
Definition MereologicalObject : Type := Prop.

Definition IsWithinBounds (lo hi x : MereologicalObject) : MereologicalObject :=
  (hi -> x) /\ (x -> lo).

Definition IsIndividual (lo hi x : MereologicalObject) : MereologicalObject :=
  IsWithinBounds lo hi x.

Definition ProjectIntoInterval (x lo hi : MereologicalObject) : MereologicalObject :=
  (x /\ lo) \/ hi.

Definition WrapFact (x y : MereologicalObject) : MereologicalObject :=
  (x /\ y) <-> x.

Definition WrapAssertion (x y z : MereologicalObject) : MereologicalObject :=
  (x /\ (y \/ z)) <-> x.

Definition WrapMetafact (x y : MereologicalObject) : MereologicalObject :=
  (x /\ y) <-> x.

Record Interval : Type := mkInterval
  { iMin : MereologicalObject
  ; iMax : MereologicalObject
  }.

Record EidosSort : Type := mkEidosSort
  { sMin     : MereologicalObject
  ; sMax     : MereologicalObject
  ; ordering : sMax -> sMin
  }.

Record MereologicalObjectOfSort (s : EidosSort) : Type := mkMOOfSort
  { mereologicalObject        : MereologicalObject
  ; mereologicalObjectHasSort : IsWithinBounds (sMin s) (sMax s) mereologicalObject
  }.

Record IndividualOfSort (s : EidosSort) : Type := mkIndividualOfSort
  { individualObject : MereologicalObjectOfSort s
  ; isIndividual     : IsIndividual (sMin s) (sMax s)
                         (mereologicalObject s individualObject)
  }.

Record Subquotient (inner outer : EidosSort) : Type := mkSubquotient
  { sqUpper : sMax outer -> sMax inner
  ; sqLower : sMin inner -> sMin outer
  }.

Record SortWithinInterval (sort : EidosSort) (interval : Interval) : Type :=
  mkSortWithinInterval
  { swiUpper : iMax interval -> sMax sort
  ; swiLower : sMin sort -> iMin interval
  }.

Record EidosUniverse : Type := mkEidosUniverse
  { universeSort          : EidosSort
  ; propSort              : EidosSort
  ; propsWithinUniverse   :
      SortWithinInterval propSort
        (mkInterval (sMin universeSort) (sMax universeSort))
  }.

Record OrdinarySortWithinUniverse (sort : EidosSort) (univ : EidosUniverse) : Type :=
  mkOrdinarySortWithinUniverse
  { sortWithinInterval :
      SortWithinInterval sort
        (mkInterval (sMin (propSort univ)) (sMax (universeSort univ)))
  }.

Record SOLFunctionOneArg (dom cod : EidosSort) : Type := mkSOLFunctionOneArg
  { solApply : MereologicalObject -> MereologicalObject
  ; solArg   : MereologicalObjectOfSort dom
  ; solRes   : MereologicalObjectOfSort cod
  ; solFact  : forall X1 : MereologicalObject,
                 IsWithinBounds (sMin dom) (sMax dom) X1 ->
               forall X2 : MereologicalObject,
                 IsWithinBounds (sMin cod) (sMax cod) X2 ->
               ((X1 <-> mereologicalObject dom solArg) /\
                (X2 <-> mereologicalObject cod solRes))
               <->
               (X2 <-> solApply X1)
  }.

(* n-ary SOL function; argDomains is a vector of domain sorts indexed by Fin n.
   We use (forall i : Fin n, ...) to represent Fin-indexed families. *)
Section FinIndexed.

  Record SOLFunction (n : nat) (argDomains : Fin.t n -> EidosSort) (codomain : EidosSort) : Type :=
    mkSOLFunction
    { nApply : (Fin.t n -> MereologicalObject) -> MereologicalObject
    ; nArgN  : forall i : Fin.t n, MereologicalObjectOfSort (argDomains i)
    ; nRes   : MereologicalObjectOfSort codomain
    }.

  Record ImageFunctionPair (dom cod : EidosSort) : Type := mkImageFunctionPair
    { imageFn        : SOLFunctionOneArg dom cod
    ; inverseImageFn : SOLFunctionOneArg cod dom
    ; adjunction     : forall X : MereologicalObject,
                         IsWithinBounds (sMin dom) (sMax dom) X ->
                       forall Y : MereologicalObject,
                         IsWithinBounds (sMin cod) (sMax cod) Y ->
                       (Y -> solApply dom cod imageFn X)
                       <->
                       (solApply cod dom inverseImageFn Y -> X)
    }.

  Record FOLFunctionOneArg (dom cod : EidosSort) : Type := mkFOLFunctionOneArg
    { folImagePair : ImageFunctionPair dom cod
    ; folArg       : MereologicalObjectOfSort dom
    ; folRes       : MereologicalObjectOfSort cod
    ; folFact      : forall X1 : MereologicalObject,
                       IsWithinBounds (sMin dom) (sMax dom) X1 ->
                     forall X2 : MereologicalObject,
                       IsWithinBounds (sMin cod) (sMax cod) X2 ->
                     ((X1 <-> mereologicalObject dom folArg) /\
                      (X2 <-> mereologicalObject cod folRes))
                     <->
                     (X2 <-> solApply dom cod (imageFn dom cod folImagePair) X1)
    ; folExtension : forall X : MereologicalObject,
                       solApply dom cod (imageFn dom cod folImagePair) X <->
                       solApply dom cod (imageFn dom cod folImagePair)
                         (ProjectIntoInterval X (sMin dom) (sMax dom))
    }.

  Record ProductSort (n : nat) (factors : Fin.t n -> EidosSort) (product : EidosSort) : Type :=
    mkProductSort
    { projections : forall i : Fin.t n, ImageFunctionPair product (factors i)
    ; tuple       : (Fin.t n -> MereologicalObject) -> MereologicalObject
    }.

  Record FOLRelation (n : nat) (doms : Fin.t n -> EidosSort) (relDomain : EidosSort) : Type :=
    mkFOLRelation
    { folRelProductStructure : ProductSort n doms relDomain
    ; folRelArgN             : forall i : Fin.t n, MereologicalObjectOfSort (doms i)
    ; folRelArg              : MereologicalObjectOfSort relDomain
    ; folRelArgRelationship  : forall xs : Fin.t n -> MereologicalObject,
                                 (forall i, IsWithinBounds (sMin (doms i)) (sMax (doms i)) (xs i)) ->
                                 (forall i, xs i <-> mereologicalObject (doms i) (folRelArgN i))
                                 <->
                                 mereologicalObject relDomain folRelArg =
                                   tuple n doms relDomain folRelProductStructure xs
    }.

  (* functionDomain is f#dom (the product sort for argument tuples),
     which must be declared separately since it cannot be inferred from doms.
     For n=1 use FOLFunctionOneArg instead (no product sort needed). *)
  Record FOLFunction (n : nat) (doms : Fin.t n -> EidosSort) (cod functionDomain : EidosSort) : Type :=
    mkFOLFunction
    { folFnProductStructure : ProductSort n doms functionDomain
    ; folFnArgN             : forall i : Fin.t n, MereologicalObjectOfSort (doms i)
    ; folFnArg              : MereologicalObjectOfSort functionDomain
    ; folFnArgRelationship  : forall xs : Fin.t n -> MereologicalObject,
                                (forall i, IsWithinBounds (sMin (doms i)) (sMax (doms i)) (xs i)) ->
                                (forall i, xs i <-> mereologicalObject (doms i) (folFnArgN i))
                                <->
                                mereologicalObject functionDomain folFnArg =
                                  tuple n doms functionDomain folFnProductStructure xs
    ; folFnImagePair        : ImageFunctionPair functionDomain cod
    ; folFnRes              : MereologicalObjectOfSort cod
    ; folFnFact             : forall xs : Fin.t n -> MereologicalObject,
                                (forall i, IsWithinBounds (sMin (doms i)) (sMax (doms i)) (xs i)) ->
                              forall Y : MereologicalObject,
                                IsWithinBounds (sMin cod) (sMax cod) Y ->
                                (((forall i, xs i <-> mereologicalObject (doms i) (folFnArgN i)) /\
                                  (Y <-> mereologicalObject cod folFnRes)))
                                <->
                                (Y <->
                                  solApply functionDomain cod
                                    (imageFn functionDomain cod folFnImagePair)
                                    (tuple n doms functionDomain folFnProductStructure xs))
    ; folFnExtension        : forall xs : Fin.t n -> MereologicalObject,
                                solApply functionDomain cod
                                  (imageFn functionDomain cod folFnImagePair)
                                  (tuple n doms functionDomain folFnProductStructure xs) <->
                                solApply functionDomain cod
                                  (imageFn functionDomain cod folFnImagePair)
                                  (tuple n doms functionDomain folFnProductStructure
                                    (fun i => ProjectIntoInterval (xs i) (sMin (doms i)) (sMax (doms i))))
    }.

End FinIndexed.

(* The five mereological operations for a sort, all derived from its Min/Max.
   Unlike the Lean version, Coq Records do not support default field values,
   so we provide a canonical constructor as a Definition instead. *)
Record MereologicalOps (s : EidosSort) : Type := mkMereologicalOps
  { mPlus   : MereologicalObject -> MereologicalObject -> MereologicalObject
  ; mTimes  : MereologicalObject -> MereologicalObject -> MereologicalObject
  ; mMinus  : MereologicalObject -> MereologicalObject -> MereologicalObject
  ; mImpl   : MereologicalObject -> MereologicalObject -> MereologicalObject
  ; mBicond : MereologicalObject -> MereologicalObject -> MereologicalObject
  }.

(* Canonical instance with the standard mereological definitions. *)
Definition canonicalMereologicalOps (s : EidosSort) : MereologicalOps s :=
  {| mPlus   := fun X Y => ProjectIntoInterval X (sMin s) (sMax s) /\
                            ProjectIntoInterval Y (sMin s) (sMax s)
   ; mTimes  := fun X Y => ProjectIntoInterval X (sMin s) (sMax s) \/
                            ProjectIntoInterval Y (sMin s) (sMax s)
   ; mMinus  := fun X Y => ProjectIntoInterval Y (sMin s) (sMax s) ->
                            ProjectIntoInterval X (sMin s) (sMax s)
   ; mImpl   := fun X Y => ProjectIntoInterval X (sMin s) (sMax s) ->
                            ProjectIntoInterval Y (sMin s) (sMax s)
   ; mBicond := fun X Y => ProjectIntoInterval X (sMin s) (sMax s) <->
                            ProjectIntoInterval Y (sMin s) (sMax s)
   |}.
