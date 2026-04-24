-- | Abstract syntax tree for EidosLang.
--
-- The structure mirrors the Go parser exactly:
--
--   TheoryDecl → TheoryBody → [Section]
--   Section    → SignatureSection | AxiomsWrapper | SubtheoriesSection | BareAxioms
--
-- Naming conventions follow the Go source.  Every 'Maybe' corresponds to an
-- optional field; every '[…]' to a repeated one.
module Eidos.AST where

-- ---------------------------------------------------------------------------
-- Top-level
-- ---------------------------------------------------------------------------

newtype TheoryDecl = TheoryDecl { theoryBody :: TheoryBody }
  deriving (Show, Eq)

newtype TheoryBody = TheoryBody { sections :: [Section] }
  deriving (Show, Eq)

data Section
  = SectionSignature   SignatureSection
  | SectionAxioms      AxiomsWrapper
  | SectionSubtheories SubtheoriesSection
  | SectionBareAxioms  AxiomsSection
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Signature
-- ---------------------------------------------------------------------------

newtype SignatureSection = SignatureSection { sigItems :: [SignatureItem] }
  deriving (Show, Eq)

data SignatureItem
  = SigSimpleSort     SimpleSortDeclaration
  | SigRelationalSort RelationalSortDeclaration
  | SigSet            SetDeclaration
  | SigFunction       FunctionDeclaration
  | SigIndividual     IndividualDeclaration
  deriving (Show, Eq)

-- | sort MySort ;
newtype SimpleSortDeclaration = SimpleSortDeclaration { simpleSortName :: String }
  deriving (Show, Eq)

-- | T subsort S ;  /  Q quotient S ;  /  SQ subquotient S ;
data RelationalSortDeclaration = RelationalSortDeclaration
  { relSortName :: String
  , relSortRel  :: String   -- "subsort" | "quotient" | "subquotient"
  , relSortSort :: SortExpr
  } deriving (Show, Eq)

-- | f : S, T → U ;
data FunctionDeclaration = FunctionDeclaration
  { funcName     :: String
  , funcDomain   :: [SortExpr]
  , funcCodomain :: SortExpr
  } deriving (Show, Eq)

-- | x : S ;
data IndividualDeclaration = IndividualDeclaration
  { indivName :: String
  , indivSort :: SortExpr
  } deriving (Show, Eq)

-- | mySet ⊆ S ;  /  r ⊆ S, T, U ;
data SetDeclaration = SetDeclaration
  { setName   :: String
  , setDomain :: [SortExpr]
  } deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Sort expressions
-- ---------------------------------------------------------------------------

newtype SortExpr = SortExpr { sortRef :: SortRef }
  deriving (Show, Eq)

data SortRef = SortRef
  { sortSpecifier :: [TheoryRef]
  , sortConstant  :: String
  } deriving (Show, Eq)

-- | One dot-qualified path segment, e.g. "sub." in "sub.S".
newtype TheoryRef = TheoryRef { theoryRefName :: String }
  deriving (Show, Eq)

newtype TheoryName = TheoryName { theoryName :: String }
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Axioms
-- ---------------------------------------------------------------------------

data AxiomsWrapper = AxiomsWrapper { axiomsSections :: [AxiomsSection] }
  deriving (Show, Eq)

data AxiomsSection
  = AxAssertions AssertionsSection
  | AxFacts      FactsSection
  | AxMetafacts  MetafactsSection
  deriving (Show, Eq)

newtype AssertionsSection = AssertionsSection { assertions :: [PropExprInclVars] }
  deriving (Show, Eq)

newtype FactsSection = FactsSection { facts :: [PropExprInclVars] }
  deriving (Show, Eq)

newtype MetafactsSection = MetafactsSection { metafacts :: [PropExprInclVars] }
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Subtheories
-- ---------------------------------------------------------------------------

newtype SubtheoriesSection = SubtheoriesSection { subtheoryEntries :: [SubtheoryEntry] }
  deriving (Show, Eq)

data SubtheoryEntry
  = SubtheoryEntryGroup SubtheoryGroup
  | SubtheoryEntryItem  SubtheoryItem
  deriving (Show, Eq)

data SubtheoryGroup = SubtheoryGroup
  { groupKeyword :: String   -- "implicit" | "named" | "reflection"
  , groupItems   :: [SubtheoryItem]
  } deriving (Show, Eq)

data SubtheoryItem = SubtheoryItem
  { itemQualifier :: Maybe String   -- "[implicit]" | "[named]" | "[reflection]"
  , itemName      :: Maybe String
  , itemDef       :: SubtheoryDef
  } deriving (Show, Eq)

data SubtheoryDef
  = SubtheoryBody        TheoryBody
  | SubtheoryExternalRef String
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Propositions
-- ---------------------------------------------------------------------------

data PropExprInclVars = PropExprInclVars
  { propSourceLine :: Int
  , propSourceCol  :: Int
  , propVars       :: [VarDecl]
  , propExprBody :: PropExpr
  } deriving (Show, Eq)

data VarDecl = VarDecl
  { varId            :: String
  , varColonOrSubset :: String   -- ":" | "⊆"
  , varSort          :: SortExpr
  } deriving (Show, Eq)

-- Proposition expression grammar (lowest → highest precedence):
--   PropExpr   biconditional  ↔  (left-associative)
--   RightImpl  implication    →  (right-associative)
--   LeftImpl   rev-implication ← (left-associative)
--   Disj       disjunction    ∨
--   Conj       conjunction    ∧
--   Neg        negation       ¬
--   Quantified quantifiers    ∀ ∃
--   AtomicProp term or paren

data PropExpr = PropExpr
  { propLeft  :: RightImpl
  , propRests :: [PropExprRest]
  } deriving (Show, Eq)

data PropExprRest = PropExprRest
  { propRestOp    :: String
  , propRestRight :: RightImpl
  } deriving (Show, Eq)

data RightImpl = RightImpl
  { riLeft  :: LeftImpl
  , riRight :: Maybe (String, RightImpl)
  } deriving (Show, Eq)

data LeftImpl = LeftImpl
  { liLeft  :: Disj
  , liRests :: [LeftImplRest]
  } deriving (Show, Eq)

data LeftImplRest = LeftImplRest
  { lirOp    :: String
  , lirRight :: Disj
  } deriving (Show, Eq)

data Disj = Disj
  { disjLeft  :: Conj
  , disjRests :: [DisjRest]
  } deriving (Show, Eq)

data DisjRest = DisjRest
  { disjRestOp    :: String
  , disjRestRight :: Conj
  } deriving (Show, Eq)

data Conj = Conj
  { conjLeft  :: Neg
  , conjRests :: [ConjRest]
  } deriving (Show, Eq)

data ConjRest = ConjRest
  { conjRestOp    :: String
  , conjRestRight :: Neg
  } deriving (Show, Eq)

data Neg
  = NegNot Neg
  | NegChild Quantified
  deriving (Show, Eq)

data Quantified = Quantified
  { quantifiers :: [Quantifier]
  , atomic      :: AtomicProp
  } deriving (Show, Eq)

data Quantifier
  = QForall VarDecl
  | QExists VarDecl
  deriving (Show, Eq)

newtype AtomicProp = AtomicProp { termPair :: TermPair }
  deriving (Show, Eq)

data TermPair = TermPair
  { termPairLeft  :: Term
  , termPairRight :: [RelationFollowedByTerm]
  } deriving (Show, Eq)

data RelationFollowedByTerm = RelationFollowedByTerm
  { rftSpecifier        :: [TheoryRef]
  , rftOp               :: String   -- "=" | "≤" | "⊆" | "∈"
  , rftOptionalSortExpr :: Maybe OptionalSortExpr
  , rftRight            :: Term
  } deriving (Show, Eq)

-- | _S or ^S qualifier on = (giving =_S or =^S)
data OptionalSortExpr = OptionalSortExpr
  { osIndicator :: String   -- "_" | "^"
  , osSortExpr  :: SortExpr
  } deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

data Term = Term
  { termLeft  :: Factor
  , termRight :: [OperationFollowedByFactor]
  } deriving (Show, Eq)

data OperationFollowedByFactor = OperationFollowedByFactor
  { offSpecifier :: [TheoryRef]
  , offOp        :: String   -- "+" | "×" | "*" | "-" | "∸" | "∪" | "∩" | "⇒"
  , offRight     :: Factor
  } deriving (Show, Eq)

data Factor = Factor
  { factorBase   :: BaseTerm
  , factorSuffix :: [TermSuffix]
  } deriving (Show, Eq)

data BaseTerm
  = BTEvaluationInTheory      EvaluationInTheory
  | BTProjectionToInterval    ProjectionToInterval
  | BTProjectionToSort        ProjectionToSort
  | BTGeneralizedSumOrProduct GeneralizedSumOrProduct
  | BTSingleton               Term
  | BTParen                   PropExpr
  | BTAtomic                  ConstantRef
  deriving (Show, Eq)

data EvaluationInTheory = EvaluationInTheory
  { eitTheoryNames :: [TheoryName]
  , eitOperand     :: PropExpr
  } deriving (Show, Eq)

data ProjectionToSort = ProjectionToSort
  { ptsSort    :: SortExpr
  , ptsOperand :: Term
  } deriving (Show, Eq)

data ProjectionToInterval = ProjectionToInterval
  { ptiLo      :: Term
  , ptiHi      :: Term
  , ptiOperand :: Term
  } deriving (Show, Eq)

data GeneralizedSumOrProduct = GeneralizedSumOrProduct
  { gspSymbol  :: String   -- "Σ" | "Π"
  , gspVar     :: Either VarDecl String  -- Left = typed, Right = bare id
  , gspOperand :: Term
  } deriving (Show, Eq)

data ConstantRef = ConstantRef
  { constSpecifier :: [TheoryRef]
  , constRef       :: String
  } deriving (Show, Eq)

data TermSuffix
  = SuffixDotAttr  String     -- ".min" | ".max" | ".res" | ".arg" | ".dom"
  | SuffixCall     CallSuffix
  | SuffixSpecialOp String    -- "#min" | "#max" | "#set" | "#1" | …
  deriving (Show, Eq)

newtype CallSuffix = CallSuffix { callArgs :: [Term] }
  deriving (Show, Eq)
