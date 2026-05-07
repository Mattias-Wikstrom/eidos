{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Eidos.Print.JSON
  ( exportTheoryToJSON
  , exportTheoryToJSONString
  , exportTheoryToJSONCompact
  , TheoryExport(..)
  ) where

import           Data.Aeson
import           Data.Aeson.Encode.Pretty (encodePretty)
import qualified Data.ByteString.Lazy.Char8 as B8
import           Data.Char (isUpper)
import           Data.List (isInfixOf, intercalate)
import qualified Data.Map.Strict as Map
import           GHC.Generics

import qualified Eidos.IR as IR

-- | Simplified export structure for JSON (user-friendly, excludes internal noise)
data TheoryExport = TheoryExport
  { name :: String
  , qualifiedName :: String
  , isReflection :: Bool
  , usesDomain :: Bool
  , usesProp :: Bool
  , signature :: SignatureExport
  , axioms :: [String]
  , facts :: [String]
  , metafacts :: [String]
  , subtheories :: [TheoryExport]
  } deriving (Generic, Show)

data SignatureExport = SignatureExport
  { sorts :: [SortExport]
  , functions :: [FunctionExport]
  , individuals :: [IndividualExport]
  , relations :: [RelationExport]
  } deriving (Generic, Show)

data SortExport = SortExport
  { sortName :: String
  , sortKind :: String
  , isBuiltin :: Bool
  } deriving (Generic, Show)

data FunctionExport = FunctionExport
  { funcName :: String
  , funcDomain :: [String]
  , funcCodomain :: String
  , funcKind :: String
  } deriving (Generic, Show)

data IndividualExport = IndividualExport
  { indivName :: String
  , indivSort :: String
  } deriving (Generic, Show)

data RelationExport = RelationExport
  { relName :: String
  , relArity :: Int
  , relSorts :: [String]
  } deriving (Generic, Show)

-- JSON instances
instance ToJSON TheoryExport where
  toJSON = genericToJSON defaultOptions { fieldLabelModifier = dropWhile (== '_') }
  
instance ToJSON SignatureExport where
  toJSON = genericToJSON defaultOptions { fieldLabelModifier = dropWhile (== '_') }
  
instance ToJSON SortExport where
  toJSON = genericToJSON defaultOptions { fieldLabelModifier = dropWhile (== '_') }
  
instance ToJSON FunctionExport where
  toJSON = genericToJSON defaultOptions { fieldLabelModifier = dropWhile (== '_') }
  
instance ToJSON IndividualExport where
  toJSON = genericToJSON defaultOptions { fieldLabelModifier = dropWhile (== '_') }
  
instance ToJSON RelationExport where
  toJSON = genericToJSON defaultOptions { fieldLabelModifier = dropWhile (== '_') }

-- | Convert a Theory to the simplified export structure
exportTheoryToJSON :: IR.Theory -> TheoryExport
exportTheoryToJSON th = TheoryExport
  { name = if null (IR.theoryName th) then "<root>" else IR.theoryName th
  , qualifiedName = if null (IR.theoryFullyQualifiedName th) then "<root>" else IR.theoryFullyQualifiedName th
  , isReflection = IR.theoryReflection th
  , usesDomain = IR.theoryUsesDomain th
  , usesProp = IR.theoryUsesProp th
  , signature = extractSignature th
  , axioms = extractAxioms th
  , facts = extractFacts th
  , metafacts = extractMetafacts th
  , subtheories = map exportTheoryToJSON (IR.theorySubtheories th)
  }

extractSignature :: IR.Theory -> SignatureExport
extractSignature th = SignatureExport
  { sorts = extractSorts th
  , functions = extractFunctions th
  , individuals = extractIndividuals th
  , relations = extractRelations th
  }

extractSorts :: IR.Theory -> [SortExport]
extractSorts th = 
  [ SortExport (escapeUnicode (IR.sortName s)) (showSortKindFromSort s) isBuiltin
  | IR.EntitySort s <- IR.theoryObjects th
  , let isBuiltin = IR.sortKind s `elem` [IR.SortKindUniverse, IR.SortKindDomain, IR.SortKindProp]
  , not (isInternalSort s)
  ]
  where
    isInternalSort s = 
      any (`isInfixOf` IR.sortName s) ["#dom", "#res"] ||
      IR.sortKind s == IR.SortKindProduct

extractFunctions :: IR.Theory -> [FunctionExport]
extractFunctions th =
  [ FunctionExport 
      (escapeUnicode (IR.funcName f))
      (map (escapeUnicode . IR.sortName) (IR.funcArgSorts f))
      (escapeUnicode (IR.sortName (IR.funcResSort f)))
      (if IR.funcKind f == IR.FunctionKindFOLFunctionFromTheory then "FOL" else "SOL")
  | IR.EntityFunction f <- IR.theoryObjects th
  , IR.funcKind f `elem` [IR.FunctionKindFOLFunctionFromTheory, IR.FunctionKindSOLFunctionFromTheory]
  , not (isInternalFunction f)
  ]
  where
    isInternalFunction f =
      any (`isInfixOf` IR.funcName f) ["#dir_img", "#inv_img", "_inv"]

extractIndividuals :: IR.Theory -> [IndividualExport]
extractIndividuals th =
  [ IndividualExport (escapeUnicode (IR.mereoName m)) (escapeUnicode (IR.sortName (IR.mereoSort m)))
  | IR.EntityMereological m <- IR.theoryObjects th
  , IR.mereoKind m == IR.MereologicalEntityKindIndividual
  , IR.mereoOrigin m == IR.FromSignature
  ]

extractRelations :: IR.Theory -> [RelationExport]
extractRelations th =
  [ RelationExport (escapeUnicode (IR.relName r)) (length (IR.relArgSorts r)) (map (escapeUnicode . IR.sortName) (IR.relArgSorts r))
  | IR.EntityRelation r <- IR.theoryObjects th
  , IR.relOrigin r == IR.FromSignature
  ] ++
  [ RelationExport (escapeUnicode (IR.mereoName m)) 1 [escapeUnicode (IR.sortName (IR.mereoSort m))]
  | IR.EntityMereological m <- IR.theoryObjects th
  , IR.mereoKind m == IR.MereologicalEntityKindSet
  , IR.mereoOrigin m == IR.FromSignature
  ]

extractAxioms :: IR.Theory -> [String]
extractAxioms th = 
  [ prettyFact f
  | f <- IR.theoryFacts th
  , IR.factKind f == IR.FactKindAssertion
  , not (IR.factIsMereologicalTranslation f)
  ]

extractFacts :: IR.Theory -> [String]
extractFacts th =
  [ prettyFact f
  | f <- IR.theoryFacts th
  , IR.factKind f == IR.FactKindFact
  , not (IR.factIsMereologicalTranslation f)
  ]

extractMetafacts :: IR.Theory -> [String]
extractMetafacts th =
  [ prettyFact f
  | f <- IR.theoryFacts th
  , IR.factKind f == IR.FactKindMetafactsFact
  ]

-- | Better fact pretty-printer that extracts actual formulas
prettyFact :: IR.Fact -> String
prettyFact f = renderPropExpr (IR.factPropExpr f)

renderPropExpr :: IR.ResolvedPropExpr -> String
renderPropExpr (IR.ResolvedPropBicond left rests) =
  renderRightImpl left ++ concatMap renderRest rests
  where
    renderRest (IR.ResolvedPropRest op right) = " " ++ op ++ " " ++ renderRightImpl right

renderRightImpl :: IR.ResolvedRightImpl -> String
renderRightImpl (IR.ResolvedRightImpl left Nothing) =
  renderLeftImpl left
renderRightImpl (IR.ResolvedRightImpl left (Just (op, right))) =
  renderLeftImpl left ++ " " ++ op ++ " " ++ renderRightImpl right

renderLeftImpl :: IR.ResolvedLeftImpl -> String
renderLeftImpl (IR.ResolvedLeftImpl disj []) =
  renderDisj disj
renderLeftImpl (IR.ResolvedLeftImpl disj rests) =
  renderDisj disj ++ concatMap renderRest rests
  where
    renderRest (IR.ResolvedLeftImplRest op d) = " " ++ op ++ " " ++ renderDisj d

renderDisj :: IR.ResolvedDisj -> String
renderDisj (IR.ResolvedDisj conj []) =
  renderConj conj
renderDisj (IR.ResolvedDisj conj rests) =
  renderConj conj ++ concatMap renderRest rests
  where
    renderRest (IR.ResolvedDisjRest op c) = " " ++ op ++ " " ++ renderConj c

renderConj :: IR.ResolvedConj -> String
renderConj (IR.ResolvedConj neg []) =
  renderNeg neg
renderConj (IR.ResolvedConj neg rests) =
  renderNeg neg ++ concatMap renderRest rests
  where
    renderRest (IR.ResolvedConjRest op n) = " " ++ op ++ " " ++ renderNeg n

renderNeg :: IR.ResolvedNeg -> String
renderNeg (IR.ResolvedNegNot inner) = "¬ " ++ renderNeg inner
renderNeg (IR.ResolvedNegChild quant) = renderQuantified quant

renderQuantified :: IR.ResolvedQuantified -> String
renderQuantified (IR.ResolvedQuantified qs atomic) =
  concatMap renderQuantifier qs ++ " " ++ renderAtomic atomic
  where
    renderQuantifier (IR.ResolvedQForall vd) = "∀" ++ renderVarDecl vd
    renderQuantifier (IR.ResolvedQExists vd) = "∃" ++ renderVarDecl vd

renderVarDecl :: IR.ResolvedVarDecl -> String
renderVarDecl vd =
  "[" ++ IR.resolvedVarName vd ++ 
  (if IR.resolvedVarIsSet vd then " ⊆ " else " : ") ++
  IR.sortName (IR.resolvedVarSort vd) ++ "]"

renderAtomic :: IR.ResolvedAtomicProp -> String
renderAtomic (IR.ResolvedAtomicTermPair tp) = renderTermPair tp
renderAtomic (IR.ResolvedAtomicConstant ref) = IR.resolvedConstRefName ref

renderTermPair :: IR.ResolvedTermPair -> String
renderTermPair (IR.ResolvedTermPair left rights _) =
  renderTerm left ++ concatMap renderRFT rights
  where
    renderRFT (IR.ResolvedRelationFollowedByTerm _ op _ right) =
      " " ++ op ++ " " ++ renderTerm right

renderTerm :: IR.ResolvedTerm -> String
renderTerm (IR.ResolvedTerm left [] _) = renderFactor left
renderTerm (IR.ResolvedTerm left rights _) =
  renderFactor left ++ concatMap renderOFF rights
  where
    renderOFF (IR.ResolvedOperationFollowedByFactor _ op right) =
      " " ++ op ++ " " ++ renderFactor right

renderFactor :: IR.ResolvedFactor -> String
renderFactor (IR.ResolvedFactor base [] _) = renderBase base
renderFactor (IR.ResolvedFactor base suffixes _) =
  renderBase base ++ concatMap renderSuffix suffixes
  where
    renderSuffix (IR.ResolvedSuffixCall args) =
      "(" ++ intercalate ", " (map renderTerm args) ++ ")"
    renderSuffix (IR.ResolvedSuffixSpecialOp op) = "#" ++ op
    renderSuffix (IR.ResolvedSuffixDotAttr attr) = "." ++ attr

renderBase :: IR.ResolvedBaseTerm -> String
renderBase (IR.ResolvedBTAtomic ref) = IR.resolvedConstRefName ref
renderBase (IR.ResolvedBTPropParen inner) = "(" ++ renderPropExpr inner ++ ")"
renderBase (IR.ResolvedBTTermParen term) = "(" ++ renderTerm term ++ ")"
renderBase (IR.ResolvedBTSingleton t) = "{" ++ renderTerm t ++ "}"
renderBase (IR.ResolvedBTEvaluationInTheory (IR.ResolvedEvaluationInTheory path _ inner)) =
  "<<" ++ intercalate "." path ++ ">>(" ++ renderPropExpr inner ++ ")"
renderBase (IR.ResolvedBTProjectionToSort (IR.ResolvedProjectionToSort s operand)) =
  "<" ++ IR.sortName s ++ ">(" ++ renderTerm operand ++ ")"
renderBase (IR.ResolvedBTProjectionToInterval (IR.ResolvedProjectionToInterval lo hi operand)) =
  "<" ++ renderTerm lo ++ ", " ++ renderTerm hi ++ ">(" ++ renderTerm operand ++ ")"
renderBase (IR.ResolvedBTGeneralizedSumOrProduct (IR.ResolvedGeneralizedSumOrProduct sym var operand)) =
  sym ++ renderVar var ++ "(" ++ renderTerm operand ++ ")"
  where
    renderVar (Left vd) = renderVarDecl vd
    renderVar (Right vid) = vid

-- Helper to escape Unicode characters for JSON
escapeUnicode :: String -> String
escapeUnicode = id  -- JSON handles Unicode fine, we just need to ensure it's valid UTF-8

showSortKindFromSort :: IR.Sort -> String
showSortKindFromSort s = case IR.sortKind s of
  IR.SortKindFromSignature -> "user"
  IR.SortKindUniverse -> "universe"
  IR.SortKindDomain -> "domain"
  IR.SortKindProp -> "prop"
  IR.SortKindProduct -> "product"
  _ -> "other"

-- | Export to pretty JSON string
exportTheoryToJSONString :: IR.Theory -> String
exportTheoryToJSONString = B8.unpack . encodePretty . exportTheoryToJSON

-- | Export to compact JSON string (no pretty printing)
exportTheoryToJSONCompact :: IR.Theory -> String
exportTheoryToJSONCompact = B8.unpack . encode . exportTheoryToJSON