-- Eidos compiler runtime library

abbrev MereologicalObject : Type := Prop

def IsWithinBounds (lo hi x : MereologicalObject) : MereologicalObject := (hi → x) ∧ (x → lo)
def IsIndividual   (lo hi x : MereologicalObject) : MereologicalObject := IsWithinBounds lo hi x
def ProjectIntoInterval (x lo hi : MereologicalObject) : MereologicalObject := (x ∧ lo) ∨ hi
def WrapFact      (x y   : MereologicalObject) : MereologicalObject := (x ∧ y) ↔ x
def WrapAssertion (x y z : MereologicalObject) : MereologicalObject := (x ∧ (y ∨ z)) ↔ x
def WrapMetafact  (x y   : MereologicalObject) : MereologicalObject := (x ∧ y) ↔ x

structure Interval where
  Min      : MereologicalObject
  Max      : MereologicalObject

structure EidosSort where
  Min      : MereologicalObject
  Max      : MereologicalObject
  ordering : Max → Min

structure MereologicalObjectOfSort (s : EidosSort) where
  mereologicalObject        : MereologicalObject
  mereologicalObjectHasSort : IsWithinBounds s.Min s.Max mereologicalObject

structure IndividualOfSort (s : EidosSort) where
  mereologicalObjectOfSort : MereologicalObjectOfSort s
  isIndividual : IsIndividual s.Min s.Max mereologicalObjectOfSort.mereologicalObject

structure Subquotient (inner outer : EidosSort) where
  upper : outer.Max → inner.Max
  lower : inner.Min → outer.Min

structure SortWithinInterval (sort : EidosSort) (interval : Interval) where
  upper : interval.Max → sort.Max
  lower : sort.Min → interval.Min

structure EidosUniverse where
  universeSort : EidosSort
  propSort : EidosSort
  propsWithinUniverse : SortWithinInterval propSort { Min := universeSort.Min, Max := universeSort.Max }

structure OrdinarySortWithinUniverse (sort : EidosSort) (univ : EidosUniverse) where
  sortWithinInverval : SortWithinInterval sort { Min := univ.propSort.Min, Max := univ.universeSort.Max }

structure SOLFunctionOneArg (dom cod : EidosSort) where
  apply   : MereologicalObject → MereologicalObject
  arg     : MereologicalObjectOfSort dom
  res     : MereologicalObjectOfSort cod
  fact    : ∀ X1 : MereologicalObject, IsWithinBounds dom.Min dom.Max X1 →
            ∀ X2 : MereologicalObject, IsWithinBounds cod.Min cod.Max X2 →
            ((X1 ↔ arg.mereologicalObject) ∧ (X2 ↔ res.mereologicalObject)) ↔
            (X2 ↔ apply X1)

structure SOLFunction (n : Nat) (argDomains : Fin n → EidosSort) (codomain : EidosSort) where
  apply   : (Fin n → MereologicalObject) → MereologicalObject
  argN    : (i : Fin n) → MereologicalObjectOfSort (argDomains i)
  res     : MereologicalObjectOfSort codomain

structure ImageFunctionPair (dom cod : EidosSort) where
  imageFn        : SOLFunctionOneArg dom cod
  inverseImageFn : SOLFunctionOneArg cod dom
  adjunction     : ∀ X, IsWithinBounds dom.Min dom.Max X →
                   ∀ Y, IsWithinBounds cod.Min cod.Max Y →
                   (Y → imageFn.apply X) ↔ (inverseImageFn.apply Y → X)

structure FOLFunctionOneArg (dom cod : EidosSort) where
  imagePair       : ImageFunctionPair dom cod
  arg             : MereologicalObjectOfSort dom
  res             : MereologicalObjectOfSort cod
  fact : ∀ X1 : MereologicalObject, IsWithinBounds dom.Min dom.Max X1 →
         ∀ X2 : MereologicalObject, IsWithinBounds cod.Min cod.Max X2 →
         ((X1 ↔ arg.mereologicalObject) ∧ (X2 ↔ res.mereologicalObject)) ↔
         (X2 ↔ imagePair.imageFn.apply X1)

structure ProductSort (n : Nat) (factors : Fin n → EidosSort) (product : EidosSort) where
  projections   : (i : Fin n) → ImageFunctionPair product (factors i)
  tuple         : (Fin n → MereologicalObject) → MereologicalObject

structure FOLRelation (n : Nat) (doms : Fin n → EidosSort) (relDomain : EidosSort) where
  productStructure : ProductSort n doms relDomain
  argN             : (i : Fin n) → MereologicalObjectOfSort (doms i)
  arg              : MereologicalObjectOfSort relDomain
  argRelationship  : ∀ (xs : Fin n → MereologicalObject),
                     (∀ i, IsWithinBounds (doms i).Min (doms i).Max (xs i)) →
                     (∀ i, xs i ↔ (argN i).mereologicalObject) ↔
                     arg.mereologicalObject = productStructure.tuple xs

-- functionDomain is f#dom (the product sort for argument tuples),
-- which must be declared separately since it cannot be inferred from doms.
-- For n=1 use FOLFunctionOneArg instead (no product sort needed).
structure FOLFunction (n : Nat) (doms : Fin n → EidosSort) (cod functionDomain : EidosSort) where
  productStructure : ProductSort n doms functionDomain
  argN             : (i : Fin n) → MereologicalObjectOfSort (doms i)
  arg        : MereologicalObjectOfSort functionDomain
  argRelationship  : ∀ (xs : Fin n → MereologicalObject),
                    (∀ i, IsWithinBounds (doms i).Min (doms i).Max (xs i)) →
                    (∀ i, xs i ↔ (argN i).mereologicalObject) ↔
                    arg.mereologicalObject = productStructure.tuple xs
  imagePair        : ImageFunctionPair functionDomain cod
  res              : MereologicalObjectOfSort cod
  fact : ∀ (xs : Fin n → MereologicalObject),
         (∀ i, IsWithinBounds (doms i).Min (doms i).Max (xs i)) →
         ∀ Y : MereologicalObject, IsWithinBounds cod.Min cod.Max Y →
         ((∀ i, xs i ↔ (argN i).mereologicalObject) ∧ Y ↔ res.mereologicalObject) ↔
         (Y ↔ imagePair.imageFn.apply (productStructure.tuple xs))


-- The five mereological operations for a sort, all derived from its Min/Max.
-- Construct with `{}` to get the canonical definitions:
--   def myOps : MereologicalOps s := {}
structure MereologicalOps (s : EidosSort) where
  plus   : MereologicalObject → MereologicalObject → MereologicalObject :=
    fun X Y => (ProjectIntoInterval X s.Min s.Max) ∧ (ProjectIntoInterval Y s.Min s.Max)
  times  : MereologicalObject → MereologicalObject → MereologicalObject :=
    fun X Y => (ProjectIntoInterval X s.Min s.Max) ∨ (ProjectIntoInterval Y s.Min s.Max)
  minus  : MereologicalObject → MereologicalObject → MereologicalObject :=
    fun X Y => (ProjectIntoInterval Y s.Min s.Max) → (ProjectIntoInterval X s.Min s.Max)
  impl   : MereologicalObject → MereologicalObject → MereologicalObject :=
    fun X Y => (ProjectIntoInterval X s.Min s.Max) → (ProjectIntoInterval Y s.Min s.Max)
  bicond : MereologicalObject → MereologicalObject → MereologicalObject :=
    fun X Y => (ProjectIntoInterval X s.Min s.Max) ↔ (ProjectIntoInterval Y s.Min s.Max)
