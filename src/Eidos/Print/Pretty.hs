-- | Pretty printer for EidosLang theories.
--
-- This module provides pretty-printing capabilities for the intermediate
-- representation ('Theory') and the abstract syntax tree ('TheoryDecl').
-- The output aims to be readable while preserving the structure of the
-- original theory.
module Eidos.Print.Pretty
  ( prettyTheory
  , prettyTheoryDecl
  , prettyTheoryDeclWithOpts
  , prettyFact
  , prettyFactDebug
  , prettyResolvedPropExpr
  , prettyResolvedPropExprWithOpts
  , PrettyOptions(..)
  , defaultPrettyOptions
  ) where

import           Data.List      (intercalate)
import qualified Data.Map.Strict as Map
import           Data.Maybe     (isJust, mapMaybe)

import           Eidos.Parse.AST
import qualified Eidos.Parse.AST as AST
import           Eidos.IR as IR


-- ---------------------------------------------------------------------------
-- Pretty-printing options
-- ---------------------------------------------------------------------------

data PrettyOptions = PrettyOptions
  { poIndentAmount :: Int      -- ^ Number of spaces per indentation level
  , poShowFQN      :: Bool     -- ^ Show fully qualified names
  , poShowTypes    :: Bool     -- ^ Show type information for expressions
  , poCompact      :: Bool     -- ^ Compact mode (fewer line breaks)
  } deriving (Show, Eq)

defaultPrettyOptions :: PrettyOptions
defaultPrettyOptions = PrettyOptions
  { poIndentAmount = 2
  , poShowFQN = False
  , poShowTypes = False
  , poCompact = False
  }

-- ---------------------------------------------------------------------------
-- Pretty printer state
-- ---------------------------------------------------------------------------

type Doc = String

indent :: Int -> Doc -> Doc
indent n = unlines . map (replicate n ' ' ++) . lines

prettyWithOpts :: PrettyOptions -> Int -> Doc -> Doc
prettyWithOpts opts level = indent (poIndentAmount opts * level)

-- ---------------------------------------------------------------------------
-- Theory pretty-printing
-- ---------------------------------------------------------------------------

prettyTheory :: Theory -> Doc
prettyTheory = prettyTheoryWithOpts defaultPrettyOptions

prettyTheoryWithOpts :: PrettyOptions -> Theory -> Doc
prettyTheoryWithOpts opts th =
  let nameLine = if IR.theoryName th == ""
                 then "theory"
                 else "theory " ++ IR.theoryName th
      body = prettyTheoryBodyWithOpts opts (mkTheoryBody th)
  in nameLine ++ " " ++ body

mkTheoryBody :: Theory -> TheoryBody
mkTheoryBody th = TheoryBody $ concat
  [ [SectionSignature $ mkSignatureSection th]
  , [SectionSubtheories $ mkSubtheoriesSection th | not (null (IR.theorySubtheories th))]
  , [SectionAxioms $ mkAxiomsWrapper th | not (null (IR.theoryFacts th))]
  ]

-- Convert IR Sort to AST SortExpr (simplified - just use the name)
sortToSortExpr :: IR.Sort -> SortExpr
sortToSortExpr s = SortExpr $ SortRef [] (IR.sortName s)

mkSignatureSection :: Theory -> SignatureSection
mkSignatureSection th = SignatureSection $
  mapMaybe entityToSignatureItem (IR.theoryObjects th)

entityToSignatureItem :: Entity -> Maybe SignatureItem
entityToSignatureItem (EntitySort s) =
  Just $ SigSimpleSort $ SimpleSortDeclaration (IR.sortName s)
entityToSignatureItem (EntityFunction f) =
  Just $ SigFunction $ FunctionDeclaration
    (IR.funcName f)
    (map sortToSortExpr (IR.funcArgSorts f))
    (sortToSortExpr (IR.funcResSort f))
entityToSignatureItem (EntityMereological m) =
  case IR.mereoKind m of
    MereologicalEntityKindIndividual ->
      Just $ SigIndividual $ IndividualDeclaration (IR.mereoName m) (sortToSortExpr (IR.mereoSort m))
    MereologicalEntityKindSet ->
      Just $ SigSet $ SetDeclaration (IR.mereoName m) [sortToSortExpr (IR.mereoSort m)]
    _ -> Nothing
entityToSignatureItem (EntityRelation r) =
  Just $ SigSet $ SetDeclaration
    (IR.relName r)
    (map sortToSortExpr (IR.relArgSorts r))
entityToSignatureItem _ = Nothing

mkSubtheoriesSection :: Theory -> SubtheoriesSection
mkSubtheoriesSection th = SubtheoriesSection $
  map (\sub -> SubtheoryEntryItem $ SubtheoryItem Nothing (Just (IR.theoryName sub))
        (SubtheoryBody (mkTheoryBody sub))) (IR.theorySubtheories th)

mkAxiomsWrapper :: Theory -> AxiomsWrapper
mkAxiomsWrapper th = AxiomsWrapper $
  filter (not . isEmptyAxiomsSection) $
  [ AxAssertions $ AssertionsSection
      [ PropExprInclVars 0 0 [] (stringToPropExpr (prettyResolvedPropExpr (factPropExpr f)))
      | f <- IR.theoryFacts th
      , IR.factKind f == FactKindAssertion ]
  , AxFacts $ FactsSection
      [ PropExprInclVars 0 0 [] (stringToPropExpr (prettyResolvedPropExpr (factPropExpr f)))
      | f <- IR.theoryFacts th
      , IR.factKind f == FactKindFact ]
  , AxMetafacts $ MetafactsSection
      [ PropExprInclVars 0 0 [] (stringToPropExpr (prettyResolvedPropExpr (factPropExpr f)))
      | f <- IR.theoryFacts th
      , IR.factKind f == FactKindMetafactsFact ]
  ]
  where
    stringToPropExpr s = 
      let commentTerm = Term (Factor (BTAtomic (ConstantRef [] ("/* " ++ s ++ " */"))) []) []
          commentPair = TermPair commentTerm []
          commentAtomic = AtomicProp commentPair
          commentQuantified = Quantified [] commentAtomic
          commentNeg = NegChild commentQuantified
          commentConj = Conj commentNeg []
          commentDisj = Disj commentConj []
          commentLeftImpl = LeftImpl commentDisj []
          commentRightImpl = RightImpl commentLeftImpl Nothing
      in PropExpr commentRightImpl []

isEmptyAxiomsSection :: AxiomsSection -> Bool
isEmptyAxiomsSection (AxAssertions (AssertionsSection [])) = True
isEmptyAxiomsSection (AxFacts (FactsSection [])) = True
isEmptyAxiomsSection (AxMetafacts (MetafactsSection [])) = True
isEmptyAxiomsSection _ = False

-- Create a simple placeholder proposition expression
factToPropExpr :: Fact -> PropExpr
factToPropExpr _ = 
  let topTerm = Term (Factor (BTAtomic (ConstantRef [] "⊤")) []) []
      topPair = TermPair topTerm []
      atomic = AtomicProp topPair
      quantified = Quantified [] atomic
      neg = NegChild quantified
      conj = Conj neg []
      disj = Disj conj []
      leftImpl = LeftImpl disj []
      rightImpl = RightImpl leftImpl Nothing
  in PropExpr rightImpl []

prettyTheoryDecl :: TheoryDecl -> Doc
prettyTheoryDecl = prettyTheoryDeclWithOpts defaultPrettyOptions

prettyTheoryDeclWithOpts :: PrettyOptions -> TheoryDecl -> Doc
prettyTheoryDeclWithOpts opts (TheoryDecl body) =
  "{" ++ (if poCompact opts then " " else "\n") ++
  prettyTheoryBodyWithOpts opts body ++
  (if poCompact opts then " " else "\n") ++ "}"

prettyTheoryBodyWithOpts :: PrettyOptions -> TheoryBody -> Doc
prettyTheoryBodyWithOpts opts (TheoryBody sections) =
  let secs = filter (not . isEmptySection) sections
  in if null secs
     then ""
     else intercalate (if poCompact opts then ", " else ",\n") $
          map (prettySectionWithOpts opts 1) secs

isEmptySection :: Section -> Bool
isEmptySection (SectionSignature (SignatureSection [])) = True
isEmptySection (SectionAxioms (AxiomsWrapper [])) = True
isEmptySection (SectionSubtheories (SubtheoriesSection [])) = True
isEmptySection _ = False

-- ---------------------------------------------------------------------------
-- Section pretty-printing
-- ---------------------------------------------------------------------------

prettySectionWithOpts :: PrettyOptions -> Int -> Section -> Doc
prettySectionWithOpts opts level sec =
  prettyWithOpts opts level $
    case sec of
      SectionSignature sig ->
        "signature " ++ prettySignatureSectionWithOpts opts sig
      SectionAxioms axs ->
        "axioms " ++ prettyAxiomsWrapperWithOpts opts axs
      SectionSubtheories subs ->
        "subtheories " ++ prettySubtheoriesSectionWithOpts opts subs

prettySignatureSectionWithOpts :: PrettyOptions -> SignatureSection -> Doc
prettySignatureSectionWithOpts opts (SignatureSection items) =
  if null items
  then "{}"
  else "{\n" ++
       intercalate "\n" (map (prettyWithOpts opts 1 . prettySignatureItem) items) ++
       "\n}"

prettySignatureItem :: SignatureItem -> Doc
prettySignatureItem item =
  case item of
    SigSimpleSort (SimpleSortDeclaration nm) ->
      "sort " ++ nm ++ ";"
    SigRelationalSort (RelationalSortDeclaration nm rel sortExpr) ->
      nm ++ " " ++ rel ++ " " ++ prettySortExpr sortExpr ++ ";"
    SigFunction (FunctionDeclaration nm domain codomain) ->
      nm ++ " : " ++ intercalate ", " (map prettySortExpr domain) ++
      " → " ++ prettySortExpr codomain ++ ";"
    SigIndividual (IndividualDeclaration nm sortExpr) ->
      nm ++ " : " ++ prettySortExpr sortExpr ++ ";"
    SigSet (SetDeclaration nm domain) ->
      nm ++ " ⊆ " ++ intercalate ", " (map prettySortExpr domain) ++ ";"

prettySortExpr :: SortExpr -> Doc
prettySortExpr (SortExpr (SortRef specifiers constName)) =
  (if null specifiers then "" else concatMap (++ ".") (map prettyTheoryRef specifiers)) ++ constName

prettyTheoryRef :: TheoryRef -> Doc
prettyTheoryRef (TheoryRef nm) = nm

prettyAxiomsWrapperWithOpts :: PrettyOptions -> AxiomsWrapper -> Doc
prettyAxiomsWrapperWithOpts opts (AxiomsWrapper sections) =
  if null sections
  then "{}"
  else "{\n" ++
       intercalate "\n" (map (prettyWithOpts opts 1 . prettyAxiomsSection) sections) ++
       "\n}"

prettyAxiomsSection :: AxiomsSection -> Doc
prettyAxiomsSection axSec =
  case axSec of
    AxAssertions (AssertionsSection props) ->
      if null props then "assertions {}" else
      "assertions {\n" ++
      intercalate "\n" (map prettyPropExprInclVars props) ++
      "\n}"
    AxFacts (FactsSection props) ->
      if null props then "facts {}" else
      "facts {\n" ++
      intercalate "\n" (map prettyPropExprInclVars props) ++
      "\n}"
    AxMetafacts (MetafactsSection props) ->
      if null props then "metafacts {}" else
      "metafacts {\n" ++
      intercalate "\n" (map prettyPropExprInclVars props) ++
      "\n}"

prettyAxiomsSectionWithOpts :: PrettyOptions -> AxiomsSection -> Doc
prettyAxiomsSectionWithOpts _ axSec = prettyAxiomsSection axSec

prettySubtheoriesSectionWithOpts :: PrettyOptions -> SubtheoriesSection -> Doc
prettySubtheoriesSectionWithOpts opts (SubtheoriesSection entries) =
  if null entries
  then "{}"
  else "{\n" ++
       intercalate "\n" (map (prettyWithOpts opts 1 . prettySubtheoryEntry) entries) ++
       "\n}"

prettySubtheoryEntry :: SubtheoryEntry -> Doc
prettySubtheoryEntry entry =
  case entry of
    SubtheoryEntryGroup (SubtheoryGroup kw items) ->
      kw ++ " {\n" ++
      intercalate "\n" (map prettySubtheoryItem items) ++
      "\n}"
    SubtheoryEntryItem item ->
      prettySubtheoryItem item

prettySubtheoryItem :: SubtheoryItem -> Doc
prettySubtheoryItem (SubtheoryItem qual name def) =
  (case qual of
     Just q -> "[" ++ q ++ "] "
     Nothing -> "") ++
  (case name of
     Just n -> n ++ ": "
     Nothing -> "") ++
  prettySubtheoryDef def

prettySubtheoryDef :: SubtheoryDef -> Doc
prettySubtheoryDef def =
  case def of
    SubtheoryBody body ->
      "{" ++ "\n" ++ prettyTheoryBodyWithOpts defaultPrettyOptions body ++ "\n}"
    SubtheoryExternalRef ref ->
      "@" ++ ref

-- ---------------------------------------------------------------------------
-- Proposition pretty-printing (AST)
-- ---------------------------------------------------------------------------

prettyPropExprInclVars :: PropExprInclVars -> Doc
prettyPropExprInclVars (PropExprInclVars _ _ vars expr) =
  (if null vars then "" else intercalate ", " (map prettyVarDecl vars) ++ ", ") ++
  prettyPropExpr expr

prettyVarDecl :: VarDecl -> Doc
prettyVarDecl (VarDecl name op sortExpr) =
  name ++ " " ++ op ++ " " ++ prettySortExpr sortExpr

prettyPropExpr :: PropExpr -> Doc
prettyPropExpr (PropExpr left rests) =
  prettyRightImpl left ++
  if null rests then "" else " " ++ intercalate " " (map prettyPropExprRest rests)

prettyPropExprRest :: PropExprRest -> Doc
prettyPropExprRest (PropExprRest op right) =
  op ++ " " ++ prettyRightImpl right

prettyRightImpl :: RightImpl -> Doc
prettyRightImpl (RightImpl left mbRight) =
  prettyLeftImpl left ++
  case mbRight of
    Nothing -> ""
    Just (op, right) -> " " ++ op ++ " " ++ prettyRightImpl right

prettyLeftImpl :: LeftImpl -> Doc
prettyLeftImpl (LeftImpl left rests) =
  prettyDisj left ++
  if null rests then "" else " " ++ intercalate " " (map prettyLeftImplRest rests)

prettyLeftImplRest :: LeftImplRest -> Doc
prettyLeftImplRest (LeftImplRest op right) =
  op ++ " " ++ prettyDisj right

prettyDisj :: Disj -> Doc
prettyDisj (Disj left rests) =
  prettyConj left ++
  if null rests then "" else " " ++ intercalate " " (map prettyDisjRest rests)

prettyDisjRest :: DisjRest -> Doc
prettyDisjRest (DisjRest op right) =
  op ++ " " ++ prettyConj right

prettyConj :: Conj -> Doc
prettyConj (Conj left rests) =
  prettyNeg left ++
  if null rests then "" else " " ++ intercalate " " (map prettyConjRest rests)

prettyConjRest :: ConjRest -> Doc
prettyConjRest (ConjRest op right) =
  op ++ " " ++ prettyNeg right

prettyNeg :: Neg -> Doc
prettyNeg (NegNot inner) = "¬ " ++ prettyNeg inner
prettyNeg (NegChild inner) = prettyQuantified inner

prettyQuantified :: Quantified -> Doc
prettyQuantified (Quantified qs atomic) =
  concatMap prettyQuantifier qs ++ " " ++ prettyAtomicProp atomic

prettyQuantifier :: Quantifier -> Doc
prettyQuantifier (QForall vd) = "∀" ++ prettyVarDecl vd
prettyQuantifier (QExists vd) = "∃" ++ prettyVarDecl vd

prettyAtomicProp :: AtomicProp -> Doc
prettyAtomicProp (AtomicProp tp) = prettyTermPair tp

prettyTermPair :: TermPair -> Doc
prettyTermPair (TermPair left rights) =
  prettyTerm left ++
  if null rights then "" else " " ++ intercalate " " (map prettyRelationFollowedByTerm rights)

prettyRelationFollowedByTerm :: RelationFollowedByTerm -> Doc
prettyRelationFollowedByTerm (RelationFollowedByTerm specs op mbSort right) =
  (if null specs then "" else concatMap (++ ".") (map prettyTheoryRef specs)) ++
  op ++
  (case mbSort of
     Nothing -> ""
     Just (OptionalSortExpr ind sortExpr) -> ind ++ prettySortExpr sortExpr) ++
  " " ++ prettyTerm right

-- ---------------------------------------------------------------------------
-- Term pretty-printing (AST)
-- ---------------------------------------------------------------------------

prettyTerm :: Term -> Doc
prettyTerm (Term left rights) =
  prettyFactor left ++
  if null rights then "" else " " ++ intercalate " " (map prettyOperationFollowedByFactor rights)

prettyOperationFollowedByFactor :: OperationFollowedByFactor -> Doc
prettyOperationFollowedByFactor (OperationFollowedByFactor specs op right) =
  (if null specs then "" else concatMap (++ ".") (map prettyTheoryRef specs)) ++
  op ++ " " ++ prettyFactor right

prettyFactor :: Factor -> Doc
prettyFactor (Factor base suffixes) =
  prettyBaseTerm base ++ concatMap prettyTermSuffix suffixes

prettyBaseTerm :: BaseTerm -> Doc
prettyBaseTerm bt =
  case bt of
    BTAtomic (ConstantRef specs ref) ->
      (if null specs then "" else concatMap (++ ".") (map prettyTheoryRef specs)) ++ ref
    BTEvaluationInTheory (EvaluationInTheory tnames operand) ->
      "<<" ++ intercalate "." (map prettyTheoryName tnames) ++ ">>(" ++
      prettyPropExpr operand ++ ")"
    BTProjectionToSort (ProjectionToSort sortExpr operand) ->
      "<" ++ prettySortExpr sortExpr ++ ">(" ++ prettyTerm operand ++ ")"
    BTProjectionToInterval (ProjectionToInterval lo hi operand) ->
      "<" ++ prettyTerm lo ++ ", " ++ prettyTerm hi ++ ">(" ++
      prettyTerm operand ++ ")"
    BTGeneralizedSumOrProduct (GeneralizedSumOrProduct sym var operand) ->
      sym ++
      (case var of
         Left vd -> prettyVarDecl vd
         Right vid -> vid) ++
      "(" ++ prettyTerm operand ++ ")"
    BTSetComprehension (SetComprehension vd body) ->
      "{ " ++ prettyVarDecl vd ++ " | " ++ prettyPropExpr body ++ " }"
    BTDescription (Description vd body) ->
      "ι" ++ prettyVarDecl vd ++ " " ++ prettyPropExpr body
    BTSingleton inner ->
      "{" ++ prettyTerm inner ++ "}"
    BTParen inner ->
      "(" ++ prettyPropExpr inner ++ ")"

prettyTermSuffix :: TermSuffix -> Doc
prettyTermSuffix suffix =
  case suffix of
    SuffixDotAttr attr -> "." ++ attr
    SuffixCall (CallSuffix args) ->
      "(" ++ intercalate ", " (map prettyTerm args) ++ ")"
    SuffixSpecialOp op -> "#" ++ op

prettyTheoryName :: TheoryName -> Doc
prettyTheoryName (TheoryName nm) = nm

-- ---------------------------------------------------------------------------
-- Fact pretty-printing (AST placeholder)
-- ---------------------------------------------------------------------------

prettyFact :: Fact -> Doc
prettyFact f =
  (case IR.factKind f of
     FactKindAssertion     -> "assertion: "
     FactKindFact          -> "fact: "
     FactKindMetafactsFact -> "metafact: "
     FactKindSortLimitation -> "sort limit: "
     FactKindImplicitMerge -> "implicit merge: ") ++
  "<resolved expression>"

-- ---------------------------------------------------------------------------
-- IR Pretty-printing (Resolved expressions) - for debugging
-- ---------------------------------------------------------------------------

-- | Pretty-print a resolved proposition expression with options
prettyResolvedPropExprWithOpts :: PrettyOptions -> ResolvedPropExpr -> Doc
prettyResolvedPropExprWithOpts opts (ResolvedPropBicond left rests) =
  prettyResolvedRightImplWithOpts opts left ++
  concatMap (\(ResolvedPropRest op right) -> " " ++ op ++ " " ++ prettyResolvedRightImplWithOpts opts right) rests

prettyResolvedRightImplWithOpts :: PrettyOptions -> ResolvedRightImpl -> Doc
prettyResolvedRightImplWithOpts opts (ResolvedRightImpl left mbRight) =
  prettyResolvedLeftImplWithOpts opts left ++
  case mbRight of
    Nothing -> ""
    Just (op, right) -> " " ++ op ++ " " ++ prettyResolvedRightImplWithOpts opts right

prettyResolvedLeftImplWithOpts :: PrettyOptions -> ResolvedLeftImpl -> Doc
prettyResolvedLeftImplWithOpts opts (ResolvedLeftImpl left rests) =
  prettyResolvedDisjWithOpts opts left ++
  concatMap (\(ResolvedLeftImplRest op d) -> " " ++ op ++ " " ++ prettyResolvedDisjWithOpts opts d) rests

prettyResolvedDisjWithOpts :: PrettyOptions -> ResolvedDisj -> Doc
prettyResolvedDisjWithOpts opts (ResolvedDisj left rests) =
  prettyResolvedConjWithOpts opts left ++
  concatMap (\(ResolvedDisjRest op c) -> " " ++ op ++ " " ++ prettyResolvedConjWithOpts opts c) rests

prettyResolvedConjWithOpts :: PrettyOptions -> ResolvedConj -> Doc
prettyResolvedConjWithOpts opts (ResolvedConj left rests) =
  prettyResolvedNegWithOpts opts left ++
  concatMap (\(ResolvedConjRest op n) -> " " ++ op ++ " " ++ prettyResolvedNegWithOpts opts n) rests

prettyResolvedNegWithOpts :: PrettyOptions -> ResolvedNeg -> Doc
prettyResolvedNegWithOpts opts (ResolvedNegNot inner) = "¬ " ++ prettyResolvedNegWithOpts opts inner
prettyResolvedNegWithOpts opts (ResolvedNegChild q) = prettyResolvedQuantifiedWithOpts opts q

prettyResolvedQuantifiedWithOpts :: PrettyOptions -> ResolvedQuantified -> Doc
prettyResolvedQuantifiedWithOpts opts (ResolvedQuantified qs atomic) =
  concatMap (prettyResolvedQuantifierWithOpts opts) qs ++ " " ++ prettyResolvedAtomicPropWithOpts opts atomic

prettyResolvedQuantifierWithOpts :: PrettyOptions -> ResolvedQuantifier -> Doc
prettyResolvedQuantifierWithOpts opts (ResolvedQForall vd) = "∀" ++ prettyResolvedVarDeclWithOpts opts vd
prettyResolvedQuantifierWithOpts opts (ResolvedQExists vd) = "∃" ++ prettyResolvedVarDeclWithOpts opts vd

prettyResolvedVarDeclWithOpts :: PrettyOptions -> ResolvedVarDecl -> Doc
prettyResolvedVarDeclWithOpts opts vd =
  let name = resolvedVarName vd
      sName = IR.sortName (resolvedVarSort vd)
      typeInfo = if poShowTypes opts
                 then " : " ++ show (resolvedVarSort vd)
                 else ""
  in "[" ++ name ++ (if resolvedVarIsSet vd then " ⊆ " else " : ") ++ sName ++ typeInfo ++ "]"

prettyResolvedAtomicPropWithOpts :: PrettyOptions -> ResolvedAtomicProp -> Doc
prettyResolvedAtomicPropWithOpts opts (ResolvedAtomicConstant ref) = 
  prettyResolvedConstantRefWithOpts opts ref
prettyResolvedAtomicPropWithOpts opts (ResolvedAtomicTermPair tp) = 
  prettyResolvedTermPairWithOpts opts tp

-- FIXED: Always use resolvedConstRefName for display, ignore poShowFQN for constants
prettyResolvedConstantRefWithOpts :: PrettyOptions -> ResolvedConstantRef -> Doc
prettyResolvedConstantRefWithOpts opts ref =
  let name = resolvedConstRefName ref
      typeInfo = if poShowTypes opts
                 then " : " ++ show (resolvedConstType ref)
                 else ""
  in name ++ typeInfo

prettyResolvedTermPairWithOpts :: PrettyOptions -> ResolvedTermPair -> Doc
prettyResolvedTermPairWithOpts opts (ResolvedTermPair left rights _) =
  prettyResolvedTermWithOpts opts left ++
  concatMap (\(ResolvedRelationFollowedByTerm _ op mbSort right) ->
               " " ++ op ++ 
               (case mbSort of 
                  Nothing -> "" 
                  Just (ResolvedOptionalSortExpr ind s) -> ind ++ IR.sortName s) ++
               " " ++ prettyResolvedTermWithOpts opts right) rights

prettyResolvedTermWithOpts :: PrettyOptions -> ResolvedTerm -> Doc
prettyResolvedTermWithOpts opts (ResolvedTerm left rights _) =
  prettyResolvedFactorWithOpts opts left ++
  concatMap (\(ResolvedOperationFollowedByFactor _ op right) -> " " ++ op ++ " " ++ prettyResolvedFactorWithOpts opts right) rights

prettyResolvedFactorWithOpts :: PrettyOptions -> ResolvedFactor -> Doc
prettyResolvedFactorWithOpts opts (ResolvedFactor base suffixes _) =
  prettyResolvedBaseTermWithOpts opts base ++ concatMap (prettyResolvedSuffixWithOpts opts) suffixes

prettyResolvedBaseTermWithOpts :: PrettyOptions -> ResolvedBaseTerm -> Doc
prettyResolvedBaseTermWithOpts opts bt = case bt of
  ResolvedBTAtomic ref -> prettyResolvedConstantRefWithOpts opts ref
  ResolvedBTPropParen inner -> "(" ++ prettyResolvedPropExprWithOpts opts inner ++ ")"
  ResolvedBTTermParen term -> "(" ++ prettyResolvedTermWithOpts opts term ++ ")"
  ResolvedBTSetComprehension (ResolvedSetComprehension rvd rbody) ->
    let op = if resolvedVarIsSet rvd then " ⊆ " else " : "
        binder = resolvedVarName rvd ++ op ++ IR.sortName (resolvedVarSort rvd)
    in "{ " ++ binder ++ " | " ++ prettyResolvedPropExprWithOpts opts rbody ++ " }"
  ResolvedBTDescription (ResolvedDescription rvd rbody) ->
    let op = if resolvedVarIsSet rvd then " ⊆ " else " : "
        binder = resolvedVarName rvd ++ op ++ IR.sortName (resolvedVarSort rvd)
    in "ι" ++ binder ++ " " ++ prettyResolvedPropExprWithOpts opts rbody
  ResolvedBTSingleton t -> "{" ++ prettyResolvedTermWithOpts opts t ++ "}"
  ResolvedBTEvaluationInTheory (ResolvedEvaluationInTheory path _ inner) ->
    "<<" ++ intercalate "." path ++ ">>(" ++ prettyResolvedPropExprWithOpts opts inner ++ ")"
  ResolvedBTProjectionToSort (ResolvedProjectionToSort s operand) ->
    "<" ++ IR.sortName s ++ ">(" ++ prettyResolvedTermWithOpts opts operand ++ ")"
  ResolvedBTProjectionToInterval (ResolvedProjectionToInterval lo hi operand) ->
    "<" ++ prettyResolvedTermWithOpts opts lo ++ ", " ++ prettyResolvedTermWithOpts opts hi ++ ">(" ++
    prettyResolvedTermWithOpts opts operand ++ ")"
  ResolvedBTGeneralizedSumOrProduct (ResolvedGeneralizedSumOrProduct sym var operand) ->
    sym ++ (case var of Left vd -> prettyResolvedVarDeclWithOpts opts vd; Right vid -> vid) ++
    "(" ++ prettyResolvedTermWithOpts opts operand ++ ")"

prettyResolvedSuffixWithOpts :: PrettyOptions -> ResolvedTermSuffix -> Doc
prettyResolvedSuffixWithOpts opts (ResolvedSuffixDotAttr attr) = "." ++ attr
prettyResolvedSuffixWithOpts opts (ResolvedSuffixCall args) = 
  "(" ++ intercalate ", " (map (prettyResolvedTermWithOpts opts) args) ++ ")"
prettyResolvedSuffixWithOpts opts (ResolvedSuffixSpecialOp op) = "#" ++ op

-- | Pretty-print a resolved proposition expression (with default options)
prettyResolvedPropExpr :: ResolvedPropExpr -> Doc
prettyResolvedPropExpr = prettyResolvedPropExprWithOpts defaultPrettyOptions { poShowFQN = True }

-- | Pretty-print a fact with full IR details (for debugging)
prettyFactDebug :: Fact -> Doc
prettyFactDebug f =
  let kindStr = case IR.factKind f of
        FactKindAssertion     -> "assertion: "
        FactKindFact          -> "fact: "
        FactKindMetafactsFact -> "metafact: "
        FactKindSortLimitation -> "sort limit: "
        FactKindImplicitMerge -> "implicit merge: "
  in kindStr ++ prettyResolvedPropExpr (factPropExpr f)
