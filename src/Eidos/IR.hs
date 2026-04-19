-- | Intermediate representation for EidosLang after name resolution and type checking.
--
-- This IR represents a fully resolved theory where:
--   * All references are resolved to concrete entities
-- * Types are determined and attached to expressions
--   * Facts are categorized by their kind
--   * Subtheories are properly nested
module Eidos.IR where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (isJust)

-- ---------------------------------------------------------------------------
-- Core types
-- ---------------------------------------------------------------------------

-- | Origin of an entity (where it was defined)
data Origin
  = FromSignature
  | FromSubtheory
  | InEveryTheory
  | FromSort
  | FromFunction
  | FromRelation
  deriving (Show, Eq)

-- | Entity kinds
data EntityKind
  -- Sorts
  = SortKindFromSignature
  | SortKindUniverse
  | SortKindDomain
  | SortKindProp
  | SortKindProduct
  | SortKindFromReflection
  -- Functions
  | FunctionKindFOLFunctionFromTheory
  | FunctionKindSOLFunctionFromTheory
  | FunctionKindFOLFunctionFromReflection
  | FunctionKindDirectImageFunction
  | FunctionKindInverseImageFunction
  | FunctionKindMereologicalOperation
  -- Mereological objects
  | MereologicalEntityKindMereological
  | MereologicalEntityKindIndividual
  | MereologicalEntityKindSet
  | MereologicalEntityKindProposition
  | MereologicalEntityKindUpperLimitForSort
  | MereologicalEntityKindLowerLimitForSort
  | MereologicalEntityKindResultOfSOLFunction
  | MereologicalEntityKindArgumentOfSOLFunction
  deriving (Show, Eq)

-- | Fact kinds
data FactKind
  = FactKindFact
  | FactKindAssertion
  | FactKindMetafactsFact
  | FactKindSortLimitation
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Entity sum type (replaces the type class)
-- ---------------------------------------------------------------------------

-- | Entity - a sum type of all possible entities
data Entity
  = EntitySort Sort
  | EntityFunction Function
  | EntityMereological MereologicalObject
  | EntityRelation Relation
  | EntityTheory Theory
  deriving (Show)

-- Helper functions for Entity
entityTheory :: Entity -> Theory
entityTheory (EntitySort s) = sortTheory s
entityTheory (EntityFunction f) = funcTheory f
entityTheory (EntityMereological m) = mereoTheory m
entityTheory (EntityRelation r) = relTheory r
entityTheory (EntityTheory t) = t

entityName :: Entity -> String
entityName (EntitySort s) = sortName s
entityName (EntityFunction f) = funcName f
entityName (EntityMereological m) = mereoName m
entityName (EntityRelation r) = relName r
entityName (EntityTheory t) = theoryName t

entityKind :: Entity -> EntityKind
entityKind (EntitySort s) = sortKind s
entityKind (EntityFunction f) = funcKind f
entityKind (EntityMereological m) = mereoKind m
entityKind (EntityRelation r) = relKind r
entityKind (EntityTheory _) = error "Theories don't have an EntityKind"

entityOrigin :: Entity -> Origin
entityOrigin (EntitySort s) = sortOrigin s
entityOrigin (EntityFunction f) = funcOrigin f
entityOrigin (EntityMereological m) = mereoOrigin m
entityOrigin (EntityRelation r) = relOrigin r
entityOrigin (EntityTheory _) = error "Theories don't have an Origin"

entityToString :: Entity -> String
entityToString (EntitySort s) = sortToString s
entityToString (EntityFunction f) = funcToString f
entityToString (EntityMereological m) = mereoToString m
entityToString (EntityRelation r) = relToString r
entityToString (EntityTheory t) = theoryToString t

-- ---------------------------------------------------------------------------
-- Sort entity
-- ---------------------------------------------------------------------------

data Sort = Sort
  { sortKind :: EntityKind
  , sortTheory :: Theory
  , sortOrigin :: Origin
  , sortMin :: MereologicalObject
  , sortMax :: MereologicalObject
  , sortName :: String  -- Empty string for product sorts
  , sortComponentSorts :: [Sort]  -- For product sorts
  , sortAssociatedEntity :: Maybe Entity  -- For product sorts, the relation/function
  }
  deriving (Show)

sortToString :: Sort -> String
sortToString s = 
  let name = if null (sortName s) 
             then case sortAssociatedEntity s of
                    Just e -> entityName e ++ "#dom"
                    Nothing -> "[anonymous sort]"
             else sortName s
  in name ++ " " ++ show (sortOrigin s)

-- ---------------------------------------------------------------------------
-- Function entity
-- ---------------------------------------------------------------------------

data Function = Function
  { funcKind :: EntityKind
  , funcOrigin :: Origin
  , funcTheory :: Theory
  , funcName :: String
  , funcArgSorts :: [Sort]
  , funcResSort :: Sort
  , funcResObject :: MereologicalObject
  , funcArgObjects :: [MereologicalObject]
  , funcDomain :: Maybe Sort  -- Product sort for FOL functions
  , funcArgument :: Maybe MereologicalObject  -- For FOL functions
  , funcDirectImage :: Maybe Function  -- For FOL functions
  , funcInverseImage :: Maybe Function  -- For FOL functions
  }
  deriving (Show)

funcToString :: Function -> String
funcToString f = funcName f ++ " : " ++ show (funcArgSorts f) ++ " -> " ++ show (funcResSort f)

-- ---------------------------------------------------------------------------
-- Mereological object
-- ---------------------------------------------------------------------------

data MereologicalObject = MereologicalObject
  { mereoKind :: EntityKind
  , mereoOrigin :: Origin
  , mereoTheory :: Theory
  , mereoName :: String
  , mereoSort :: Sort
  , mereoLimitForSort :: Maybe Sort  -- For sort limits
  }
  deriving (Show)

mereoToString :: MereologicalObject -> String
mereoToString mo = 
  let rel = case mereoKind mo of
        MereologicalEntityKindSet -> " ⊆ "
        _ -> " : "
  in mereoName mo ++ rel ++ show (mereoSort mo)

-- ---------------------------------------------------------------------------
-- Relation entity
-- ---------------------------------------------------------------------------

data Relation = Relation
  { relOrigin :: Origin
  , relKind :: EntityKind
  , relTheory :: Theory
  , relName :: String
  , relArgSorts :: [Sort]
  , relDomain :: Sort  -- Product sort
  , relArgObjects :: [MereologicalObject]
  , relArgument :: MereologicalObject
  , relAssociatedSet :: MereologicalObject
  }
  deriving (Show)

relToString :: Relation -> String
relToString r = relName r ++ " ⊆ " ++ show (relArgSorts r)

-- ---------------------------------------------------------------------------
-- Theory structure
-- ---------------------------------------------------------------------------

-- Forward declaration for mutual recursion
data Theory = Theory
  { theoryParent :: Maybe Theory
  , theoryName :: String
  , theoryFullyQualifiedName :: String
  , theoryReflection :: Bool
  , theoryClosestReflectionAncestor :: Maybe Theory
  , theorySubtheories :: [Theory]
  , theoryObjects :: [Entity]
  , theoryObjectsByName :: Map.Map String [Entity]
  , theoryFacts :: [Fact]
  , theoryUniverse :: Sort
  , theoryDomain :: Sort
  , theoryProp :: Sort
  , theoryTruth :: MereologicalObject
  , theoryFalsity :: MereologicalObject
  , theorySum :: Function
  , theoryProd :: Function
  , theoryDiff :: Function
  , theoryRevDiff :: Function
  , theorySymDiff :: Function
  }
  deriving (Show)

theoryToString :: Theory -> String
theoryToString t = "theory " ++ theoryFullyQualifiedName t

-- | A fact in a theory
data Fact = Fact
  { factIsMereologicalTranslation :: Bool
  , factIsInherited :: Bool
  , factKind :: FactKind
  , factPropExpr :: ResolvedPropExpr
  }
  deriving (Show)

-- ---------------------------------------------------------------------------
-- Resolved expressions (with types and references)
-- ---------------------------------------------------------------------------

-- | Major type classification
data MajorType
  = MajorTypeMereologicalObject
  | MajorTypeFunction
  | MajorTypeSort
  deriving (Show, Eq)

-- | Mereological object subtype
data MereologicalSubtype
  = MereologicalSubtypeIndividual
  | MereologicalSubtypeSet
  | MereologicalSubtypeProposition
  | MereologicalSubtypeMereological
  deriving (Show, Eq)

-- | Type information for expressions
data ExprType = ExprType
  { exprMajorType :: MajorType
  , exprMereoSubtype :: Maybe MereologicalSubtype
  , exprSort :: Maybe Sort
  , exprNumArgs :: Maybe Int  -- For functions
  }
  deriving (Show)

-- | Resolved variable declaration
data ResolvedVarDecl = ResolvedVarDecl
  { resolvedVarName :: String
  , resolvedVarIsSet :: Bool  -- True if "⊆", False if ":"
  , resolvedVarSort :: Sort
  }
  deriving (Show)

-- | Resolved constant reference
data ResolvedConstantRef = ResolvedConstantRef
  { resolvedConstRefName :: String
  , resolvedConstEntity :: Entity
  , resolvedConstType :: ExprType
  }
  deriving (Show)

-- | Resolved proposition expression (fully typed and with resolved references)
data ResolvedPropExpr
  = ResolvedPropBicond ResolvedRightImpl [ResolvedPropRest]
  deriving (Show)

data ResolvedPropRest = ResolvedPropRest
  { resolvedPropRestOp :: String  -- "↔"
  , resolvedPropRestRight :: ResolvedRightImpl
  }
  deriving (Show)

data ResolvedRightImpl = ResolvedRightImpl
  { resolvedRLeft :: ResolvedLeftImpl
  , resolvedRRight :: Maybe (String, ResolvedRightImpl)  -- "→"
  }
  deriving (Show)

data ResolvedLeftImpl = ResolvedLeftImpl
  { resolvedLLeft :: ResolvedDisj
  , resolvedLRests :: [ResolvedLeftImplRest]
  }
  deriving (Show)

data ResolvedLeftImplRest = ResolvedLeftImplRest
  { resolvedLirOp :: String  -- "←"
  , resolvedLirRight :: ResolvedDisj
  }
  deriving (Show)

data ResolvedDisj = ResolvedDisj
  { resolvedDisjLeft :: ResolvedConj
  , resolvedDisjRests :: [ResolvedDisjRest]
  }
  deriving (Show)

data ResolvedDisjRest = ResolvedDisjRest
  { resolvedDisjRestOp :: String  -- "∨"
  , resolvedDisjRestRight :: ResolvedConj
  }
  deriving (Show)

data ResolvedConj = ResolvedConj
  { resolvedConjLeft :: ResolvedNeg
  , resolvedConjRests :: [ResolvedConjRest]
  }
  deriving (Show)

data ResolvedConjRest = ResolvedConjRest
  { resolvedConjRestOp :: String  -- "∧"
  , resolvedConjRestRight :: ResolvedNeg
  }
  deriving (Show)

data ResolvedNeg
  = ResolvedNegNot ResolvedQuantified
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

-- | Resolved term pair (proposition formed from relation)
data ResolvedTermPair = ResolvedTermPair
  { resolvedTPLeft :: ResolvedTerm
  , resolvedTPRight :: [ResolvedRelationFollowedByTerm]
  , resolvedTPType :: ExprType
  }
  deriving (Show)

data ResolvedRelationFollowedByTerm = ResolvedRelationFollowedByTerm
  { resolvedRFTTheoryPath :: [String]  -- Resolved theory references
  , resolvedRFTOp :: String  -- "=" | "≤" | "⊆" | "∈"
  , resolvedRFTSortQual :: Maybe ResolvedOptionalSortExpr
  , resolvedRFTRight :: ResolvedTerm
  }
  deriving (Show)

data ResolvedOptionalSortExpr = ResolvedOptionalSortExpr
  { resolvedOSIndicator :: String  -- "_" | "^"
  , resolvedOSSort :: Sort
  }
  deriving (Show)

-- | Resolved term
data ResolvedTerm = ResolvedTerm
  { resolvedTermLeft :: ResolvedFactor
  , resolvedTermRight :: [ResolvedOperationFollowedByFactor]
  , resolvedTermType :: ExprType
  }
  deriving (Show)

data ResolvedOperationFollowedByFactor = ResolvedOperationFollowedByFactor
  { resolvedOFFTheoryPath :: [String]
  , resolvedOFFOp :: String  -- "+" | "×" | "*" | "-" | "∸" | "∪" | "∩" | "⇒"
  , resolvedOFFRight :: ResolvedFactor
  }
  deriving (Show)

-- | Resolved factor
data ResolvedFactor = ResolvedFactor
  { resolvedFactorBase :: ResolvedBaseTerm
  , resolvedFactorSuffix :: [ResolvedTermSuffix]
  , resolvedFactorType :: ExprType
  }
  deriving (Show)

data ResolvedBaseTerm
  = ResolvedBTEvaluationInTheory ResolvedEvaluationInTheory
  | ResolvedBTProjectionToInterval ResolvedProjectionToInterval
  | ResolvedBTProjectionToSort ResolvedProjectionToSort
  | ResolvedBTGeneralizedSumOrProduct ResolvedGeneralizedSumOrProduct
  | ResolvedBTSingleton ResolvedTerm
  | ResolvedBTParen ResolvedPropExpr
  | ResolvedBTAtomic ResolvedConstantRef
  deriving (Show)

data ResolvedEvaluationInTheory = ResolvedEvaluationInTheory
  { resolvedEITTheoryPath :: [String]  -- Resolved theory names
  , resolvedEITTheory :: Theory  -- The actual theory being evaluated in
  , resolvedEITOperand :: ResolvedPropExpr
  }
  deriving (Show)

data ResolvedProjectionToSort = ResolvedProjectionToSort
  { resolvedPTSort :: Sort
  , resolvedPTOperand :: ResolvedTerm
  }
  deriving (Show)

data ResolvedProjectionToInterval = ResolvedProjectionToInterval
  { resolvedPTILo :: ResolvedTerm
  , resolvedPTIHi :: ResolvedTerm
  , resolvedPTIOperand :: ResolvedTerm
  }
  deriving (Show)

data ResolvedGeneralizedSumOrProduct = ResolvedGeneralizedSumOrProduct
  { resolvedGSPSymbol :: String  -- "Σ" | "Π"
  , resolvedGSPVar :: Either ResolvedVarDecl String  -- Left = typed, Right = bare id
  , resolvedGSPOperand :: ResolvedTerm
  }
  deriving (Show)

data ResolvedTermSuffix
  = ResolvedSuffixDotAttr String  -- ".min" | ".max" | ".res" | ".arg" | ".dom"
  | ResolvedSuffixCall [ResolvedTerm]
  | ResolvedSuffixSpecialOp String  -- "#min" | "#max" | "#set" | "#1" | "#metafacts"
  deriving (Show)

-- ---------------------------------------------------------------------------
-- Context for name resolution (used during IR construction)
-- ---------------------------------------------------------------------------

-- | Variable context tracking bound variables
data VarContext = VarContext
  { varContextBindings :: Map.Map String ResolvedVarDecl
  , varContextParent :: Maybe VarContext
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
    Nothing -> case varContextParent ctx of
      Just parent -> lookupVarContext parent name
      Nothing -> Nothing

-- ---------------------------------------------------------------------------
-- Helper functions for IR construction
-- ---------------------------------------------------------------------------

-- | Check if a sort is the proposition sort
isPropSort :: Sort -> Bool
isPropSort s = sortKind s == SortKindProp

-- | Check if a sort is the universe sort
isUniverseSort :: Sort -> Bool
isUniverseSort s = sortKind s == SortKindUniverse

-- | Check if a sort is the domain sort
isDomainSort :: Sort -> Bool
isDomainSort s = sortKind s == SortKindDomain

-- | Check if a mereological object is a set
isSet :: MereologicalObject -> Bool
isSet mo = mereoKind mo == MereologicalEntityKindSet

-- | Check if a mereological object is an individual
isIndividual :: MereologicalObject -> Bool
isIndividual mo = mereoKind mo == MereologicalEntityKindIndividual

-- | Check if a mereological object is a proposition
isProposition :: MereologicalObject -> Bool
isProposition mo = mereoKind mo == MereologicalEntityKindProposition

-- | Create a term type for a mereological object
termTypeMereological :: Maybe MereologicalSubtype -> Maybe Sort -> ExprType
termTypeMereological subtype msort = ExprType
  { exprMajorType = MajorTypeMereologicalObject
  , exprMereoSubtype = subtype
  , exprSort = msort
  , exprNumArgs = Nothing
  }

-- | Create a term type for a function
termTypeFunction :: Int -> ExprType
termTypeFunction numArgs = ExprType
  { exprMajorType = MajorTypeFunction
  , exprMereoSubtype = Nothing
  , exprSort = Nothing
  , exprNumArgs = Just numArgs
  }

-- | Create a term type for a sort
termTypeSort :: ExprType
termTypeSort = ExprType
  { exprMajorType = MajorTypeSort
  , exprMereoSubtype = Nothing
  , exprSort = Nothing
  , exprNumArgs = Nothing
  }

-- | Construct the fully qualified name for an entity
fullyQualifiedName :: Entity -> String
fullyQualifiedName e = go (entityTheory e) (entityName e)
  where
    go :: Theory -> String -> String
    go th name = 
      let parentName = case theoryParent th of
            Just parent -> go parent (theoryName parent) ++ "."
            Nothing -> ""
      in parentName ++ name

-- | Find a sort in a theory by name
findSortInTheory :: Theory -> String -> Maybe Sort
findSortInTheory th name = 
  case Map.lookup name (theoryObjectsByName th) of
    Just entities -> case filter isSortEntity entities of
      (EntitySort s:_) -> Just s
      _ -> Nothing
    Nothing -> Nothing
  where
    isSortEntity :: Entity -> Bool
    isSortEntity (EntitySort _) = True
    isSortEntity _ = False

-- | Find a subtheory by name
findSubtheory :: Theory -> String -> Maybe Theory
findSubtheory th name = 
  case filter (\st -> theoryName st == name) (theorySubtheories th) of
    (st:_) -> Just st
    [] -> Nothing