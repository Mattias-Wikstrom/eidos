-- | Intermediate representation for EidosLang after name resolution and type checking.
--
-- This IR represents a fully resolved theory where:
--   * All references are resolved to concrete entities
--   * Types are determined and attached to expressions
--   * Facts are categorized by their kind
--   * Subtheories are properly nested
{-# LANGUAGE PatternSynonyms #-}

module Eidos.Pipeline.FromSyntax.IR where

import qualified Data.Map.Strict as Map

-- ---------------------------------------------------------------------------
-- Core types
-- ---------------------------------------------------------------------------

data Origin
  = FromSignature
  | FromSubtheory
  | InEveryTheory
  | FromSort
  | FromFunction
  | FromRelation
  | FromReflection     -- ^ Entity produced by a reflection subtheory
  deriving (Show, Eq)

data EntityKind
  -- Sort kinds
  = SortKindFromSignature          -- ^ User-declared sort from a @sort@ declaration
  | SortKindUniverse               -- ^ The built-in universe sort 𝕌
  | SortKindDomain                 -- ^ The built-in domain sort 𝔻
  | SortKindProp                   -- ^ The built-in proposition sort ℙ
  | SortKindProduct                -- ^ Product sort generated for FOL function domains
  | SortKindFromReflection         -- ^ Marker: sort was produced by @reflectEntity@.
                                   --   This variant is set in 'sortKind' but is currently
                                   --   a pure marker — no code path branches on it after
                                   --   construction.  It is reserved for future type-checking
                                   --   passes that may need to distinguish reflected sorts.
  -- Function kinds
  | FunctionKindFOLFunctionFromTheory      -- ^ User-declared FOL (lowercase) function
  | FunctionKindSOLFunctionFromTheory      -- ^ User-declared SOL (uppercase) function
  | FunctionKindFOLFunctionFromReflection  -- ^ FOL function produced by reflection
  | FunctionKindDirectImageFunction        -- ^ Auto-generated direct-image SOL function f#dir_img
  | FunctionKindInverseImageFunction       -- ^ Auto-generated inverse-image SOL function f#inv_img
  | FunctionKindMereologicalOperation      -- ^ Built-in mereological op (+, ×, -, ⇒, ∸)
  | FunctionKindUserAbbreviation           -- ^ User-defined abbreviation from @abbreviations { }@ section
  | FunctionKindProjectionFunction         -- ^ Auto-generated projection f_pi_k (product sort → component sort)
  | FunctionKindProjectionInverse          -- ^ Auto-generated inverse projection f_pi_k_inv (component → product)
  | FunctionKindTupleFormation             -- ^ Auto-generated tuple formation f_tuple (components → product)
  -- Mereological object kinds
  | MereologicalEntityKindMereological          -- ^ Bare mereological object (no subtype)
  | MereologicalEntityKindIndividual            -- ^ An individual element of a sort
  | MereologicalEntityKindSet                   -- ^ A set of individuals
  | MereologicalEntityKindProposition           -- ^ A proposition (lives in ℙ)
  | MereologicalEntityKindUpperLimitForSort      -- ^ The S#max limit object for sort S
  | MereologicalEntityKindLowerLimitForSort      -- ^ The S#min limit object for sort S
  | MereologicalEntityKindResultOfSOLFunction    -- ^ The f#res result object of an SOL function
  | MereologicalEntityKindArgumentOfSOLFunction  -- ^ The f#N argument object of an SOL function
  | MereologicalEntityKindRelationFromReflection -- ^ A relation reflected into its parent theory as an individual
  deriving (Show, Eq)

data FactCategory
  = FCUserInput
  | FCMereologicalTranslation
  | FCSortStructure
  | FCImplicitMerge
  deriving (Show, Eq)

data FactSubkind
  = FSFact
  | FSAssertion
  | FSMetafactsFact
  | FSTranslationOfFact
  | FSTranslationOfAssertion
  | FSTranslationOfMetafact
  | FSSortLimitation
  | FSImplicitMerge
  | FSImplicitMergeFunction
  deriving (Show, Eq)

data FactKind = FactKind
  { factCategory :: FactCategory
  , factSubkind  :: FactSubkind
  }
  deriving (Show, Eq)

-- Smart constructors for user-input facts
factKindFact, factKindAssertion, factKindMetafactsFact :: FactKind
factKindFact          = FactKind FCUserInput FSFact
factKindAssertion     = FactKind FCUserInput FSAssertion
factKindMetafactsFact = FactKind FCUserInput FSMetafactsFact

-- Smart constructors for mereological translation facts
factKindMereoOfFact, factKindMereoOfAssertion, factKindMereoOfMetafact :: FactKind
factKindMereoOfFact      = FactKind FCMereologicalTranslation FSTranslationOfFact
factKindMereoOfAssertion = FactKind FCMereologicalTranslation FSTranslationOfAssertion
factKindMereoOfMetafact  = FactKind FCMereologicalTranslation FSTranslationOfMetafact

-- Smart constructors for structural facts
factKindSortLimitation, factKindImplicitMerge, factKindImplicitMergeFunction :: FactKind
factKindSortLimitation        = FactKind FCSortStructure FSSortLimitation
factKindImplicitMerge         = FactKind FCImplicitMerge FSImplicitMerge
factKindImplicitMergeFunction = FactKind FCImplicitMerge FSImplicitMergeFunction

-- Pattern synonyms for backward compatibility and exhaustive matching
pattern FactKindFact :: FactKind
pattern FactKindFact = FactKind FCUserInput FSFact

pattern FactKindAssertion :: FactKind
pattern FactKindAssertion = FactKind FCUserInput FSAssertion

pattern FactKindMetafactsFact :: FactKind
pattern FactKindMetafactsFact = FactKind FCUserInput FSMetafactsFact

pattern FactKindMereoOfFact :: FactKind
pattern FactKindMereoOfFact = FactKind FCMereologicalTranslation FSTranslationOfFact

pattern FactKindMereoOfAssertion :: FactKind
pattern FactKindMereoOfAssertion = FactKind FCMereologicalTranslation FSTranslationOfAssertion

pattern FactKindMereoOfMetafact :: FactKind
pattern FactKindMereoOfMetafact = FactKind FCMereologicalTranslation FSTranslationOfMetafact

pattern FactKindSortLimitation :: FactKind
pattern FactKindSortLimitation = FactKind FCSortStructure FSSortLimitation

pattern FactKindImplicitMerge :: FactKind
pattern FactKindImplicitMerge = FactKind FCImplicitMerge FSImplicitMerge

pattern FactKindImplicitMergeFunction :: FactKind
pattern FactKindImplicitMergeFunction = FactKind FCImplicitMerge FSImplicitMergeFunction

{-# COMPLETE FactKindFact, FactKindAssertion, FactKindMetafactsFact,
             FactKindMereoOfFact, FactKindMereoOfAssertion, FactKindMereoOfMetafact,
             FactKindSortLimitation, FactKindImplicitMerge, FactKindImplicitMergeFunction #-}

-- ---------------------------------------------------------------------------
-- Mereological expression type
-- ---------------------------------------------------------------------------

-- | Abstract syntax tree for mereological expressions.
--
-- This is the semantic representation used by the mereological translation
-- pass and consumed by backends (Lean, Coq, etc.).  Backends translate
-- 'MereoExpr' to their target language without needing to re-derive
-- mereological structure from 'ResolvedPropExpr'.
data MereoExpr
  = MSum     MereoExpr MereoExpr
    -- ^ Binary mereological sum: x + y  (→ conjunction ∧ in logic)
  | MProd    MereoExpr MereoExpr
    -- ^ Binary mereological product: x × y  (→ disjunction ∨)
  | MDiff    MereoExpr MereoExpr
    -- ^ Mereological difference: x - y  (→ reverse implication ←)
  | MRevDiff MereoExpr MereoExpr
    -- ^ Reverse difference: x ⇒ y  (→ implication →)
  | MSymDiff MereoExpr MereoExpr
    -- ^ Symmetric difference: x ∸ y  (→ biconditional ↔)
  | MVar     String
    -- ^ Named object: a sort bound (𝕌#min), proposition (⊤), variable, etc.
  | MZero
    -- ^ Mereological zero 0  (→ True in _Props backends)
  | MAbbrevApp String [MereoExpr]
    -- ^ Application of a compiler-internal abbreviation:
    --   IsWithinBounds(lo, hi, x), WrapFact(x, y), etc.
    -- | MBoundedSum Bool Bool String MereoExpr MereoExpr MereoExpr
    -- ^ Bounded quantification: (isExists, isIndividual, varName, lo, hi, body).
    --   When @isExists = False@, this is universal (∀ varName ∈ [lo, hi]. body).
    --   When @isExists = True@,  this is existential (∃ varName ∈ [lo, hi]. body).
    --   @isIndividual = True@ means the variable was declared with @:@ syntax
    --   (a first-order individual); backends should guard with @IsIndividual@
    --   rather than @IsWithinBounds@.
  | MBoundedSum String MereoExpr MereoExpr MereoExpr
  | MBoundedProduct String MereoExpr MereoExpr MereoExpr
  | MSumOfIndividuals String MereoExpr MereoExpr MereoExpr
  | MProductOfIndividuals String MereoExpr MereoExpr MereoExpr
  
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Abbreviation definitions (compiler-internal)
-- ---------------------------------------------------------------------------

-- | A compiler-internal abbreviation: a named definition with typed parameters
-- and a body expressed as a 'MereoExpr'.  Backends use the registry to decide
-- which abbreviations to emit and how to render them.
data AbbrevDef = AbbrevDef
  { abbrevName   :: String
  , abbrevParams :: [String]
  , abbrevBody   :: MereoExpr
  } deriving (Show, Eq)

-- | Registry of all compiler-internal abbreviation definitions.
-- Backends should use 'collectUsedAbbrevNames' to find the subset actually
-- needed and emit only those.
allAbbrevDefs :: [AbbrevDef]
allAbbrevDefs =
  [ AbbrevDef "IsWithinBounds" ["lo", "hi", "x"]
      -- (hi⇒x) + (x⇒lo)
      (MSum (MRevDiff (MVar "hi") (MVar "x")) (MRevDiff (MVar "x") (MVar "lo")))
  , AbbrevDef "ProjectIntoInterval" ["x", "lo", "hi"]
      -- (x+lo) × hi
      (MProd (MSum (MVar "x") (MVar "lo")) (MVar "hi"))
  , AbbrevDef "IsIndividual" ["lo", "hi", "x"]
      -- (hi⇒x) + (x⇒lo)  — same structure as IsWithinBounds for now
      (MSum (MRevDiff (MVar "hi") (MVar "x")) (MRevDiff (MVar "x") (MVar "lo")))
  , AbbrevDef "WrapFact" ["x", "y"]
      -- (x+y) ∸ x
      (MSymDiff (MSum (MVar "x") (MVar "y")) (MVar "x"))
  , AbbrevDef "WrapAssertion" ["x", "y", "z"]
      -- (x+(y×z)) ∸ x
      (MSymDiff (MSum (MVar "x") (MProd (MVar "y") (MVar "z"))) (MVar "x"))
  , AbbrevDef "WrapMetafact" ["x", "y"]
      -- (x+y) ∸ x
      (MSymDiff (MSum (MVar "x") (MVar "y")) (MVar "x"))
  ]

-- | Collect all 'MAbbrevApp' names reachable from a 'MereoExpr'.
collectUsedAbbrevNames :: MereoExpr -> [String]
collectUsedAbbrevNames = go
  where
    go (MSum a b)            = go a ++ go b
    go (MProd a b)           = go a ++ go b
    go (MDiff a b)           = go a ++ go b
    go (MRevDiff a b)        = go a ++ go b
    go (MSymDiff a b)        = go a ++ go b
    go (MVar _)              = []
    go MZero                 = []
    go (MAbbrevApp n args)   = n : concatMap go args
    go (MBoundedSum _ lo hi body) = go lo ++ go hi ++ go body
    go (MBoundedProduct _ lo hi body) = go lo ++ go hi ++ go body
    go (MSumOfIndividuals _ lo hi body) = go lo ++ go hi ++ go body
    go (MProductOfIndividuals _ lo hi body) = go lo ++ go hi ++ go body

-- ---------------------------------------------------------------------------
-- Entity sum type
-- ---------------------------------------------------------------------------

data Entity
  = EntitySort Sort
  | EntityFunction Function
  | EntityMereological MereologicalObject
  | EntityRelation Relation
  | EntityTheory Theory
  deriving (Show)

entityTheory :: Entity -> Theory
entityTheory (EntitySort s)       = sortTheory s
entityTheory (EntityFunction f)   = funcTheory f
entityTheory (EntityMereological m) = mereoTheory m
entityTheory (EntityRelation r)   = relTheory r
entityTheory (EntityTheory t)     = t

entityName :: Entity -> String
entityName (EntitySort s)         = sortName s
entityName (EntityFunction f)     = funcName f
entityName (EntityMereological m) = mereoName m
entityName (EntityRelation r)     = relName r
entityName (EntityTheory t)       = theoryName t

-- | Return the 'EntityKind' of an entity.
--
-- __Partial__: throws a runtime error for 'EntityTheory' because theories do
-- not carry an 'EntityKind'.  Call sites should pattern-match on 'Entity'
-- directly when 'EntityTheory' is a possible case, or guard with
-- @classifyLevel1 e /= L1Theory@.
entityKind :: Entity -> EntityKind
entityKind (EntitySort s)         = sortKind s
entityKind (EntityFunction f)     = funcKind f
entityKind (EntityMereological m) = mereoKind m
entityKind (EntityRelation r)     = relKind r
entityKind (EntityTheory _)       = error "entityKind: EntityTheory has no EntityKind"

-- | Return the 'Origin' of an entity.
--
-- __Partial__: throws a runtime error for 'EntityTheory' — same rationale as
-- 'entityKind'.
entityOrigin :: Entity -> Origin
entityOrigin (EntitySort s)         = sortOrigin s
entityOrigin (EntityFunction f)     = funcOrigin f
entityOrigin (EntityMereological m) = mereoOrigin m
entityOrigin (EntityRelation r)     = relOrigin r
entityOrigin (EntityTheory _)       = error "entityOrigin: EntityTheory has no Origin"
    
-- ---------------------------------------------------------------------------
-- Sort
-- ---------------------------------------------------------------------------

-- | Relationship between a sort and a parent sort (for relational sort declarations).
data SortRelationship
  = NotRelational
    -- ^ A regular (non-relational) sort declaration.
  | SubSort
    -- ^ Declared with @subsort@: child#min = parent#min, child#max ≤ parent#max
  | Quotient
    -- ^ Declared with @quotient@: parent#min ≤ child#min, child#max = parent#max
  | SubQuotient
    -- ^ Declared with @subquotient@: parent#min ≤ child#min, child#max ≤ parent#max
  deriving (Show, Eq)

data Sort = Sort
  { sortKind             :: EntityKind
  , sortTheory           :: Theory
  , sortOrigin           :: Origin
  , sortMin              :: MereologicalObject
  , sortMax              :: MereologicalObject
  , sortName             :: String
  , sortComponentSorts   :: [Sort]
  , sortAssociatedEntity :: Maybe Entity
  , sortReflectedFrom    :: Maybe Theory
  , sortRelationship     :: SortRelationship
  , sortParent           :: Maybe Sort
  , sortSeparationAxiom  :: Maybe MereoExpr
    -- ^ For 'SortKindProduct' sorts: the mereological expression for the Separation axiom
    --   (∀X,Y∈dom. X↔Y ↔ ∀Z∈dom. IR(Z)→((X⇒Z)↔(Y⇒Z))).  'Nothing' for all other sorts.
  }

instance Show Sort where
  show s = "Sort{" ++ sortName s ++ "}"

-- ---------------------------------------------------------------------------
-- Function
-- ---------------------------------------------------------------------------

data Function = Function
  { funcKind         :: EntityKind
  , funcOrigin       :: Origin
  , funcTheory       :: Theory
  , funcName         :: String
  , funcArgSorts     :: [Sort]
  , funcResSort      :: Sort
  , funcResObject    :: Maybe MereologicalObject
  , funcArgObjects   :: [MereologicalObject]
  , funcDomain       :: Maybe Sort
  , funcArgument     :: Maybe MereologicalObject
  , funcDirectImage     :: Maybe Function
  , funcInverseImage    :: Maybe Function
  , funcReflectedFrom   :: Maybe Theory   -- ^ Just originalTheory when this is a reflected copy
  }

instance Show Function where
  show f = "Function{" ++ funcName f ++ "}"

-- ---------------------------------------------------------------------------
-- MereologicalObject
-- ---------------------------------------------------------------------------

data MereologicalObject = MereologicalObject
  { mereoKind         :: EntityKind
  , mereoOrigin       :: Origin
  , mereoTheory       :: Theory
  , mereoName         :: String
  , mereoSort         :: Sort
  , mereoLimitForSort :: Maybe Sort
  , mereoReflectedFrom :: Maybe Theory   -- ^ Just originalTheory when this is a reflected copy
  , mereoAlias        :: Maybe Entity
    -- ^ When set, this object is an alias for another entity.  Any lookup
    -- that finds this object should dereference to the alias target via
    -- 'resolveEntityAlias'.  Used for built-in keywords such as @⊤@ and
    -- @⊥@ which alias the ℙ-sort lower and upper bounds respectively.
  }

instance Show MereologicalObject where
  show m = "MereologicalObject{" ++ mereoName m ++ "}"

-- ---------------------------------------------------------------------------
-- Relation
-- ---------------------------------------------------------------------------

data Relation = Relation
  { relOrigin        :: Origin
  , relKind          :: EntityKind
    -- ^ Always 'MereologicalEntityKindSet' in the current implementation.
    -- Relations are represented as sets of tuples; this field exists for
    -- symmetry with the other entity records but carries no additional
    -- discriminating information.  It is kept so that 'entityKind' works
    -- uniformly across all non-theory entities.
  , relTheory        :: Theory
  , relName          :: String
  , relArgSorts      :: [Sort]
  , relDomain        :: Sort
  , relArgObjects    :: [MereologicalObject]
  , relArgument      :: MereologicalObject
  , relAssociatedSet :: Maybe MereologicalObject
  , relReflectedFrom :: Maybe Theory   -- ^ Just originalTheory when this is a reflected copy
  }

instance Show Relation where
  show r = "Relation{" ++ relName r ++ "}"

-- ---------------------------------------------------------------------------
-- Theory
-- ---------------------------------------------------------------------------

data Theory = Theory
  { theoryParent                    :: Maybe Theory
  , theoryName                      :: String
  , theoryFullyQualifiedName        :: String
  , theoryReflection                :: Bool
  , theoryUsesDomain                :: Bool
  , theoryUsesProp                  :: Bool
  , theoryClosestReflectionAncestor :: Maybe Theory
  , theorySubtheories               :: [Theory]
  , theoryObjects                   :: [Entity]
  , theoryObjectsByName             :: Map.Map String [Entity]
    -- ^ Maps each declared name to the list of entities that share it.
    -- A singleton list is the normal case.  A list with more than one entry
    -- signals an ambiguous name (e.g. the same name imported from two
    -- incompatible implicit subtheories).  Lookup helpers such as
    -- 'lookupEntity' treat multi-entry lists as "ambiguous" and return
    -- @Left "Ambiguous name: …"@; they do /not/ silently pick one.
    -- Callers that need all bindings (e.g. equality-fact propagation) iterate
    -- over the list directly.
  , theoryFacts                     :: [Fact]
  , theoryUniverse                  :: Sort
  , theoryDomain                    :: Sort
  , theoryProp                      :: Sort
  , theoryTruth                     :: MereologicalObject
  , theoryFalsity                   :: MereologicalObject
  , theorySum                       :: Function
  , theoryProd                      :: Function
  , theoryDiff                      :: Function
  , theoryRevDiff                   :: Function
  , theorySymDiff                   :: Function
  , theoryUserAbbrevDefs            :: [AbbrevDef]
    -- ^ User-defined abbreviations from @abbreviations { }@ sections in the
    -- source theory.  These are separate from the compiler-internal
    -- 'allAbbrevDefs' registry and must never pollute that namespace.
    -- Backends may use this list to emit user abbreviation definitions.
  }

instance Show Theory where
  show t = "Theory{" ++ theoryFullyQualifiedName t ++ "}"

data Fact = Fact
  { factKind      :: FactKind
  , factPropExpr  :: Maybe ResolvedPropExpr
    -- ^ The logical expression for this fact.
    --   'Just' for 'FCUserInput', 'FCSortStructure', and 'FCImplicitMerge' facts.
    --   'Nothing' for 'FCMereologicalTranslation' facts (use 'factMereoExpr').
  , factMereoExpr :: Maybe MereoExpr
    -- ^ The mereological expression for this fact.
    --   'Just' for 'FCMereologicalTranslation' facts.
    --   'Nothing' for facts that have no mereological representation yet.
  , factFreeVars  :: [ResolvedVarDecl]
  }
  deriving (Show)

-- ---------------------------------------------------------------------------
-- Type system
-- ---------------------------------------------------------------------------

data MajorType
  = MajorTypeMereologicalObject
  | MajorTypeFunction
  | MajorTypeSort
  deriving (Show, Eq)

data MereologicalSubtype
  = MereologicalSubtypeIndividual
  | MereologicalSubtypeSet
  | MereologicalSubtypeProposition
  | MereologicalSubtypeMereological
  deriving (Show, Eq)

data EntityClass
  = SortClass
  | FOLFunctionClass Int      -- arity
  | SOLFunctionClass Int
  | RelationClass Int         -- arity (1 for sets, n for n-ary relations)
  | IndividualClass
  | PropositionClass
  | OtherMereologicalClass    -- e.g., S#min, S#max, function argument/result objects
  | TheoryClass
  deriving (Eq, Show)

type ExprType = EntityClass

-- ---------------------------------------------------------------------------
-- Resolved expressions
-- ---------------------------------------------------------------------------

data VarKind
  = VarKindMereological  -- X : 𝕌
  | VarKindIndividual    -- x : S
  | VarKindSet           -- X ⊆ S
  | VarKindProposition   -- X : ℙ
  deriving (Show, Eq)

data ResolvedVarDecl = ResolvedVarDecl
  { resolvedVarName :: String
  , resolvedVarKind :: VarKind
  , resolvedVarSort :: Sort
  }
  deriving (Show)

data ResolvedConstantRef = ResolvedConstantRef
  { resolvedConstRefName :: String
  , resolvedConstEntity  :: Entity
  , resolvedConstType    :: ExprType
  }
  deriving (Show)

data ResolvedPropExpr
  = ResolvedPropBicond ResolvedRightImpl [ResolvedPropRest]
  deriving (Show)

data ResolvedPropRest = ResolvedPropRest
  { resolvedPropRestOp    :: String
  , resolvedPropRestRight :: ResolvedRightImpl
  }
  deriving (Show)

data ResolvedRightImpl = ResolvedRightImpl
  { resolvedRLeft  :: ResolvedLeftImpl
  , resolvedRRight :: Maybe (String, ResolvedRightImpl)
  }
  deriving (Show)

data ResolvedLeftImpl = ResolvedLeftImpl
  { resolvedLLeft  :: ResolvedDisj
  , resolvedLRests :: [ResolvedLeftImplRest]
  }
  deriving (Show)

data ResolvedLeftImplRest = ResolvedLeftImplRest
  { resolvedLirOp    :: String
  , resolvedLirRight :: ResolvedDisj
  }
  deriving (Show)

data ResolvedDisj = ResolvedDisj
  { resolvedDisjLeft  :: ResolvedConj
  , resolvedDisjRests :: [ResolvedDisjRest]
  }
  deriving (Show)

data ResolvedDisjRest = ResolvedDisjRest
  { resolvedDisjRestOp    :: String
  , resolvedDisjRestRight :: ResolvedConj
  }
  deriving (Show)

data ResolvedConj = ResolvedConj
  { resolvedConjLeft  :: ResolvedNeg
  , resolvedConjRests :: [ResolvedConjRest]
  }
  deriving (Show)

data ResolvedConjRest = ResolvedConjRest
  { resolvedConjRestOp    :: String
  , resolvedConjRestRight :: ResolvedNeg
  }
  deriving (Show)

data ResolvedNeg
  = ResolvedNegNot   ResolvedNeg
  | ResolvedNegChild ResolvedQuantified
  deriving (Show)

data ResolvedQuantified = ResolvedQuantified
  { resolvedQuantifiers :: [ResolvedQuantifier]
  , resolvedQuantAtomic :: ResolvedAtomicProp
  }
  deriving (Show)

data ResolvedQuantifier
  = ResolvedQForall ResolvedVarDecl
  | ResolvedQExists ResolvedVarDecl
  deriving (Show)

data ResolvedAtomicProp
  = ResolvedAtomicConstant ResolvedConstantRef
  | ResolvedAtomicTermPair ResolvedTermPair
  deriving (Show)

data ResolvedTermPair = ResolvedTermPair
  { resolvedTPLeft  :: ResolvedTerm
  , resolvedTPRight :: [ResolvedRelationFollowedByTerm]
  , resolvedTPType  :: ExprType
  }
  deriving (Show)

data ResolvedRelationFollowedByTerm = ResolvedRelationFollowedByTerm
  { resolvedRFTTheoryPath :: [String]
  , resolvedRFTOp         :: String
  , resolvedRFTSortQual   :: Maybe ResolvedOptionalSortExpr
  , resolvedRFTRight      :: ResolvedTerm
  }
  deriving (Show)

data ResolvedOptionalSortExpr = ResolvedOptionalSortExpr
  { resolvedOSIndicator :: String
  , resolvedOSSort      :: Sort
  }
  deriving (Show)

data ResolvedTerm = ResolvedTerm
  { resolvedTermLeft  :: ResolvedFactor
  , resolvedTermRight :: [ResolvedOperationFollowedByFactor]
  , resolvedTermType  :: ExprType
  }
  deriving (Show)

data ResolvedOperationFollowedByFactor = ResolvedOperationFollowedByFactor
  { resolvedOFFTheoryPath :: [String]
  , resolvedOFFOp         :: String
  , resolvedOFFRight      :: ResolvedFactor
  }
  deriving (Show)

data ResolvedFactor = ResolvedFactor
  { resolvedFactorBase   :: ResolvedBaseTerm
  , resolvedFactorSuffix :: [ResolvedTermSuffix]
  , resolvedFactorType   :: ExprType
  }
  deriving (Show)

data ResolvedBaseTerm
  = ResolvedBTEvaluationInTheory      ResolvedEvaluationInTheory
  | ResolvedBTProjectionToInterval    ResolvedProjectionToInterval
  | ResolvedBTProjectionToSort        ResolvedProjectionToSort
  | ResolvedBTGeneralizedSumOrProduct ResolvedGeneralizedSumOrProduct
  | ResolvedBTSetComprehension        ResolvedSetComprehension
  | ResolvedBTDescription             ResolvedDescription
  | ResolvedBTSingleton               ResolvedTerm
  | ResolvedBTTermParen               ResolvedTerm   -- ( term )
  | ResolvedBTPropParen               ResolvedPropExpr   -- ( proposition )
  | ResolvedBTAtomic                  ResolvedConstantRef
  deriving (Show)

-- | Resolved set comprehension { x : A | φ(x) }.
data ResolvedSetComprehension = ResolvedSetComprehension
  { resolvedSCVar  :: ResolvedVarDecl
  , resolvedSCBody :: ResolvedPropExpr
  } deriving (Show)

-- | Resolved description ιx : A φ(x).
data ResolvedDescription = ResolvedDescription
  { resolvedDescVar  :: ResolvedVarDecl
  , resolvedDescBody :: ResolvedPropExpr
  } deriving (Show)

data ResolvedEvaluationInTheory = ResolvedEvaluationInTheory
  { resolvedEITTheoryPath :: [String]
  , resolvedEITTheory     :: Theory
  , resolvedEITOperand    :: ResolvedPropExpr
  }
  deriving (Show)

data ResolvedProjectionToSort = ResolvedProjectionToSort
  { resolvedPTSort    :: Sort
  , resolvedPTOperand :: ResolvedTerm
  }
  deriving (Show)

data ResolvedProjectionToInterval = ResolvedProjectionToInterval
  { resolvedPTILo      :: ResolvedTerm
  , resolvedPTIHi      :: ResolvedTerm
  , resolvedPTIOperand :: ResolvedTerm
  }
  deriving (Show)

data ResolvedGeneralizedSumOrProduct = ResolvedGeneralizedSumOrProduct
  { resolvedGSPSymbol  :: String
  , resolvedGSPVar     :: Either ResolvedVarDecl String
  , resolvedGSPOperand :: ResolvedTerm
  }
  deriving (Show)

data ResolvedTermSuffix
  = ResolvedSuffixDotAttr   String
  | ResolvedSuffixCall      [ResolvedTerm]
  | ResolvedSuffixSpecialOp String (Maybe Entity)
      -- ^ op name (for printing) + resolved result entity (Nothing for type-coercion ops)
  deriving (Show)

-- ---------------------------------------------------------------------------
-- Variable context
-- ---------------------------------------------------------------------------

data VarContext = VarContext
  { varContextBindings :: Map.Map String ResolvedVarDecl
  , varContextParent   :: Maybe VarContext
  }
  deriving (Show)

emptyVarContext :: VarContext
emptyVarContext = VarContext Map.empty Nothing

extendVarContext :: VarContext -> ResolvedVarDecl -> VarContext
extendVarContext ctx vd =
  VarContext (Map.insert (resolvedVarName vd) vd (varContextBindings ctx)) (Just ctx)

lookupVarContext :: VarContext -> String -> Maybe ResolvedVarDecl
lookupVarContext ctx name =
  case Map.lookup name (varContextBindings ctx) of
    Just vd -> Just vd
    Nothing -> varContextParent ctx >>= \p -> lookupVarContext p name

termTypeSort :: ExprType
termTypeSort = SortClass

termTypeIndividual :: ExprType
termTypeIndividual = IndividualClass

termTypeSet :: ExprType
termTypeSet = RelationClass 1

termTypeProposition :: ExprType
termTypeProposition = PropositionClass

termTypeFOLFunction :: Int -> ExprType
termTypeFOLFunction arity = FOLFunctionClass arity

termTypeSOLFunction :: Int -> ExprType
termTypeSOLFunction arity = SOLFunctionClass arity

termTypeRelation :: Int -> ExprType
termTypeRelation arity = RelationClass arity

termTypeOtherMereological :: ExprType
termTypeOtherMereological = OtherMereologicalClass

termTypeTheory :: ExprType
termTypeTheory = TheoryClass

-- ---------------------------------------------------------------------------
-- Misc helpers
-- ---------------------------------------------------------------------------

isPropSort :: Sort -> Bool
isPropSort s = sortKind s == SortKindProp

isUniverseSort :: Sort -> Bool
isUniverseSort s = sortKind s == SortKindUniverse

isDomainSort :: Sort -> Bool
isDomainSort s = sortKind s == SortKindDomain

-- ---------------------------------------------------------------------------
-- Theory query helpers  (inspired by the Go version's explicit accessors)
--
-- The Go code exposed typed accessors like FOLFunctions(), Sorts(), etc.
-- on the theory struct. Here we provide pure functions over 'Theory' that
-- filter 'theoryObjects' by entity class, returning strongly-typed lists.
-- ---------------------------------------------------------------------------

-- | All user-declared FOL functions in this theory (not inherited, not
--   auto-generated auxiliary functions).
theoryFOLFunctions :: Theory -> [Function]
theoryFOLFunctions th =
  [ f | EntityFunction f <- theoryObjects th
      , funcKind f `elem` [FunctionKindFOLFunctionFromTheory, FunctionKindFOLFunctionFromReflection] ]

-- | All SOL functions declared directly in this theory (uppercase names).
theorySOLFunctions :: Theory -> [Function]
theorySOLFunctions th =
  [ f | EntityFunction f <- theoryObjects th
      , funcKind f == FunctionKindSOLFunctionFromTheory ]

-- | All sorts declared directly in this theory (excludes built-ins and
--   auto-generated product sorts).
theorySorts :: Theory -> [Sort]
theorySorts th =
  [ s | EntitySort s <- theoryObjects th
      , sortKind s == SortKindFromSignature ]

-- | All individual mereological objects declared in this theory.
theoryIndividuals :: Theory -> [MereologicalObject]
theoryIndividuals th =
  [ m | EntityMereological m <- theoryObjects th
      , mereoKind m == MereologicalEntityKindIndividual ]

-- | All proposition objects declared in this theory.
theoryPropositions :: Theory -> [MereologicalObject]
theoryPropositions th =
  [ m | EntityMereological m <- theoryObjects th
      , mereoKind m == MereologicalEntityKindProposition ]

-- | All set objects declared in this theory (singleton-sort relations).
theorySets :: Theory -> [MereologicalObject]
theorySets th =
  [ m | EntityMereological m <- theoryObjects th
      , mereoKind m == MereologicalEntityKindSet ]

-- | All n-ary relations declared in this theory.
theoryRelations :: Theory -> [Relation]
theoryRelations th =
  [ r | EntityRelation r <- theoryObjects th ]

-- | All auto-generated auxiliary entities (image functions, domain sorts,
--   arg/result objects) — i.e. everything whose origin is 'FromFunction'.
theoryFunctionAuxEntities :: Theory -> [Entity]
theoryFunctionAuxEntities th =
  filter (\e -> entityOrigin e == FromFunction) (theoryObjects th)

-- ---------------------------------------------------------------------------
-- Fully-qualified name
--
-- Mirrors Go's FullyQualifiedName(entity Entity) string.
-- Walks up theoryParent links and prepends ancestor theory names.
-- ---------------------------------------------------------------------------

-- | Return the fully-qualified name of a theory (dot-separated ancestors).
theoryFQN :: Theory -> String
theoryFQN = theoryFullyQualifiedName

-- | Return the fully-qualified name of an entity, prefixing ancestor
--   theory names when the entity is nested inside subtheories.
entityFullyQualifiedName :: Entity -> String
entityFullyQualifiedName e =
  let nm = entityName e
      th = entityTheory e
  in qualifyWithAncestors th nm
  where
    qualifyWithAncestors th nm =
      case theoryParent th of
        Nothing  -> nm
        Just par -> qualifyWithAncestors par (theoryName th ++ "." ++ nm)

-- | Follow alias links until reaching a non-alias entity.
--
-- Only 'EntityMereological' values carry aliases ('mereoAlias').  All other
-- entity variants are returned unchanged.  Chains longer than one step are
-- supported but are not expected in practice.
resolveEntityAlias :: Entity -> Entity
resolveEntityAlias e@(EntityMereological mo) =
  case mereoAlias mo of
    Nothing     -> e
    Just target -> resolveEntityAlias target
resolveEntityAlias e = e

-- ---------------------------------------------------------------------------
-- Flexible entity search  (inspired by the Go version's bit-flag lookup)
--
-- Rather than raw Int bit-flags we use a proper Haskell sum type.
-- 'SearchCriteria' values can be combined with '(<>)' / 'mconcat'.
-- The search is performed with 'lookupEntities' and 'lookupEntity''.
-- ---------------------------------------------------------------------------

-- | Each constructor corresponds to one Go FindRefInclude* constant.
data SearchCriterion
  = IncludeFOLFunctions   -- ^ FOL (lowercase) functions
  | IncludeSOLFunctions   -- ^ SOL (uppercase) functions
  | IncludeSorts          -- ^ User-declared sorts
  | IncludePropositions   -- ^ Proposition objects (live in ℙ)
  | IncludeIndividuals    -- ^ Individual mereological objects
  | IncludeSets           -- ^ Set mereological objects
  | IncludeRelations      -- ^ n-ary relations
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | A set of search criteria.  Use 'allEntityCriteria', 'mempty', or
--   explicit lists together with 'mkSearchCriteria'.
newtype SearchCriteria = SearchCriteria { unSearchCriteria :: [SearchCriterion] }
  deriving (Show, Eq)

instance Semigroup SearchCriteria where
  SearchCriteria a <> SearchCriteria b = SearchCriteria (a ++ b)

instance Monoid SearchCriteria where
  mempty = SearchCriteria []

-- | Build a 'SearchCriteria' from a list of criteria.
mkSearchCriteria :: [SearchCriterion] -> SearchCriteria
mkSearchCriteria = SearchCriteria

-- | Match everything — equivalent to all Go flags OR-ed together.
allEntityCriteria :: SearchCriteria
allEntityCriteria = SearchCriteria [minBound .. maxBound]

-- | Test whether an entity satisfies any criterion in the set.
entityMatchesCriteria :: SearchCriteria -> Entity -> Bool
entityMatchesCriteria (SearchCriteria criteria) e = any (matchOne e) criteria
  where
    matchOne (EntityFunction f) IncludeFOLFunctions =
      funcKind f `elem` [ FunctionKindFOLFunctionFromTheory
                         , FunctionKindFOLFunctionFromReflection ]
    matchOne (EntityFunction f) IncludeSOLFunctions =
      funcKind f `elem` [ FunctionKindSOLFunctionFromTheory
                         , FunctionKindDirectImageFunction
                         , FunctionKindInverseImageFunction ]
    matchOne (EntitySort _)         IncludeSorts        = True
    matchOne (EntityMereological m) IncludePropositions =
      mereoKind m == MereologicalEntityKindProposition
    matchOne (EntityMereological m) IncludeIndividuals  =
      mereoKind m == MereologicalEntityKindIndividual
    matchOne (EntityMereological m) IncludeSets         =
      mereoKind m == MereologicalEntityKindSet
    matchOne (EntityRelation _)     IncludeRelations    = True
    matchOne _                      _                   = False

-- | Return all entities in the theory (local only, not inherited subtheory
--   objects) whose name equals @nm@ and that match the given criteria.
lookupEntities :: Theory -> String -> SearchCriteria -> [Entity]
lookupEntities th nm criteria =
  case Map.lookup nm (theoryObjectsByName th) of
    Nothing -> []
    Just es -> filter (entityMatchesCriteria criteria) es

-- | Like 'lookupEntities' but returns the first match or 'Nothing'.
lookupEntity' :: Theory -> String -> SearchCriteria -> Maybe Entity
lookupEntity' th nm criteria =
  case lookupEntities th nm criteria of
    []    -> Nothing
    (e:_) -> Just e
