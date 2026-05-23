-- | Export an Eidos theory to Lean 4 using structure-based encoding.
--
-- Encoding conventions:
--   * Sorts → Types (U, P, D for built-ins; user-declared sorts as-is)
--   * Subsets S ⊆ T → S : T → P
--   * FOL functions f : S → T → f : S → T
--   * SOL functions F : S → T → F : (S → P) → (T → P)
--   * Facts become universally quantified fields
--   * Top-level theory → structure _Main where ...
--   * Subtheories → nested structures
module Eidos.Pipeline.Targets.Lean.Lean
  ( -- * Internal representation
    LeanTypeDoc (..)
  , LeanTypeDecl (..)
  , LeanTypeExpr (..)
    -- * Pipeline stages
  , theoryToLeanTypeDoc
  , renderLeanTypeDoc
    -- * Convenience entry point
  , exportToLean
  ) where

import qualified Eidos.Pipeline.FromSyntax.IR as IR
import           Eidos.Pipeline.IRProcessing.AxiomSet (AxiomBody (..), Tag (..), asAxioms, hasTag)
import           Eidos.Pipeline.IRProcessing.MkAxiomSets (theoryBlocks)
import           Eidos.Pipeline.PipelineCore (PreparedTheory (..), defaultPipelineOptions, prepareTheory)
import Data.List (intercalate)

-- ---------------------------------------------------------------------------
-- Internal representation for type-based Lean export
-- ---------------------------------------------------------------------------

data LeanTypeDoc = LeanTypeDoc
  { ltdTheoryName :: String
  , ltdDecls      :: [LeanTypeDecl]
  } deriving (Eq, Show)

data LeanTypeDecl
  = LTDStructure String [LeanTypeDecl]  -- ^ structure Name where { fields }
  | LTDField String LeanTypeExpr        -- ^ name : type
  | LTDComment String                   -- ^ -- comment
  | LTDBlankLine                         -- ^ empty line
  deriving (Eq, Show)

data LeanTypeExpr
  = LTType                              -- ^ Type
  | LTVar String                        -- ^ variable reference
  | LTArrow LeanTypeExpr LeanTypeExpr   -- ^ A → B
  | LTForall String LeanTypeExpr LeanTypeExpr  -- ^ ∀ x : T, body
  | LTEq LeanTypeExpr LeanTypeExpr      -- ^ A = B
  | LTApp LeanTypeExpr [LeanTypeExpr]   -- ^ f x y
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Stage 1 – Theory → LeanTypeDoc
-- ---------------------------------------------------------------------------

theoryToLeanTypeDoc :: IR.Theory -> LeanTypeDoc
theoryToLeanTypeDoc theory = theoryToLeanTypeDocP (prepareTheory defaultPipelineOptions theory)

theoryToLeanTypeDocP :: PreparedTheory -> LeanTypeDoc
theoryToLeanTypeDocP prepared =
  LeanTypeDoc
    { ltdTheoryName = "_Main"
    , ltdDecls      = structureDecls
    }
  where
    theory = ptTheory prepared
    structureDecls :: [LeanTypeDecl]
    structureDecls =
      [ LTDStructure "_Main" fields
      ]
    
    fields :: [LeanTypeDecl]
    fields = concat
      [ [LTDField "U" LTType]
      , [LTDField "P" LTType]
      , [LTDField "emb_P" (LTArrow (LTVar "P") (LTVar "U"))]
      , [LTDField "D" LTType | theoryUsesD]
      , [LTDField "emb_D" (LTArrow (LTVar "D") (LTVar "U")) | theoryUsesD]
      -- Built-in operations on U
      , [LTDField "plus"  uBinOp]
      , [LTDField "times" uBinOp]
      , [LTDField "minus" uBinOp]
      -- Embeddings from each user sort into U
      , [LTDField ("emb_" ++ sortName) (LTArrow (LTVar sortName) (LTVar "U"))
        | sortName <- allUserSorts]
      , map sortToField userSorts
      , map subsetToField userSubsets
      , map folFuncToField userFOLFunctions
      , map solFuncToField userSOLFunctions
      , userFactFields
      ]
        where
        uBinOp = LTArrow (LTVar "U") (LTArrow (LTVar "U") (LTVar "U"))
        
    -- All user-declared sorts
    allUserSorts = [ IR.sortName s 
                   | IR.EntitySort s <- IR.theoryObjects theory
                   , IR.sortKind s == IR.SortKindFromSignature ]
    
    -- Also embed P into U
    pEmbedding = LTDField "emb_P" (LTArrow (LTVar "P") (LTVar "U"))
    
    theoryUsesD = IR.theoryUsesDomain theory
    
    -- User sorts (excluding built-ins)
    userSorts = [ s | IR.EntitySort s <- IR.theoryObjects theory
                    , IR.sortKind s == IR.SortKindFromSignature ]
    
    sortToField s = LTDField (IR.sortName s) LTType
    
    -- User subsets
    userSubsets = [ m | IR.EntityMereological m <- IR.theoryObjects theory
                      , IR.mereoKind m == IR.MereologicalEntityKindSet
                      , IR.mereoOrigin m == IR.FromSignature
                      , IR.sortKind (IR.mereoSort m) == IR.SortKindFromSignature ]
    
    subsetToField m =
      LTDField (IR.mereoName m)
        (LTArrow (LTVar (IR.sortName (IR.mereoSort m))) (LTVar "P"))
    
    -- FOL functions (lowercase, user-declared)
    userFOLFunctions = [ f | IR.EntityFunction f <- IR.theoryObjects theory
                           , IR.funcKind f == IR.FunctionKindFOLFunctionFromTheory
                           , IR.funcOrigin f == IR.FromSignature ]
    
    folFuncToField f =
      let argTypes = map (LTVar . IR.sortName) (IR.funcArgSorts f)
          resType  = LTVar (IR.sortName (IR.funcResSort f))
          funcType = foldr LTArrow resType argTypes
      in LTDField (IR.funcName f) funcType
    
    -- SOL functions (uppercase, user-declared)
    userSOLFunctions = [ f | IR.EntityFunction f <- IR.theoryObjects theory
                           , IR.funcKind f == IR.FunctionKindSOLFunctionFromTheory
                           , IR.funcOrigin f == IR.FromSignature ]
    
    solFuncToField f =
      let argTypes = map (\s -> LTArrow (LTVar (IR.sortName s)) (LTVar "P")) (IR.funcArgSorts f)
          resType  = LTArrow (LTVar (IR.sortName (IR.funcResSort f))) (LTVar "P")
          funcType = foldr LTArrow resType argTypes
      in LTDField (IR.funcName f) funcType
    
    -- Fact fields derived from the mereological translation via MkAxiomSets.
    -- Free variables are already incorporated into the MereoExpr by FromSyntax.
    allAxiomSets = concatMap snd (theoryBlocks prepared)

    userFactFields =
      [ LTDField axName (mereoExprToLeanType mereoExpr)
      | as_ <- allAxiomSets
      , hasTag TagUserFact as_
      , (axName, ABMereo mereoExpr) <- asAxioms as_
      ]

-- ---------------------------------------------------------------------------
-- MereoExpr → LeanTypeExpr
-- ---------------------------------------------------------------------------

-- | Translate a mereological expression to a Lean type expression.
--
-- The structure-based encoding maps implication-like operations to 'LTArrow'.
-- Operations without a direct type-theoretic reading (sum, product, symmetric
-- difference, abbreviation applications, bounded quantifiers) are left as
-- @\<unsupported: ...>@ placeholders.
mereoExprToLeanType :: IR.MereoExpr -> LeanTypeExpr
mereoExprToLeanType = go
  where
    go (IR.MRevDiff a b)  = LTArrow (go a) (go b)
    go (IR.MDiff    a b)  = LTArrow (go b) (go a)
    go (IR.MVar     n)    = LTVar n
    go  IR.MZero          = LTVar "True"
    go (IR.MSum     _ _)  = LTVar "<unsupported: mereological sum>"
    go (IR.MProd    _ _)  = LTVar "<unsupported: mereological product>"
    go (IR.MSymDiff _ _)  = LTVar "<unsupported: symmetric difference>"
    go (IR.MAbbrevApp n _) = LTVar ("<unsupported: abbreviation " ++ n ++ ">")
    go (IR.MFOLApp    n _) = LTVar ("<unsupported: FOL application " ++ n ++ ">")
    go (IR.MUnboundedSum  _ _) = LTVar "<unsupported: unbounded sum>"
    go (IR.MBoundedSum     _ _ _ _) = LTVar "<unsupported: bounded sum>"
    go (IR.MBoundedProduct _ _ _ _) = LTVar "<unsupported: bounded product>"
    go (IR.MSumOfIndividuals     _ _ _ _) = LTVar "<unsupported: sum of individuals>"
    go (IR.MProductOfIndividuals _ _ _ _) = LTVar "<unsupported: product of individuals>"

-- ---------------------------------------------------------------------------
-- Stage 2 – LeanTypeDoc → String
-- ---------------------------------------------------------------------------

renderLeanTypeDoc :: LeanTypeDoc -> String
renderLeanTypeDoc doc = unlines $ map renderDecl (ltdDecls doc)

renderDecl :: LeanTypeDecl -> String
renderDecl (LTDComment c) = "-- " ++ c
renderDecl LTDBlankLine    = ""
renderDecl (LTDStructure name fields) =
  "structure " ++ name ++ " where\n" ++
  unlines (map (("  " ++) . renderField) fields)
renderDecl (LTDField name ty) = renderField (LTDField name ty)

renderField :: LeanTypeDecl -> String
renderField (LTDField name ty) = name ++ " : " ++ renderType ty
renderField _ = ""

renderType :: LeanTypeExpr -> String
renderType LTType = "Type"
renderType (LTVar n) = n
renderType (LTArrow a b) = parensIfNeeded a ++ " → " ++ renderType b
  where
    parensIfNeeded (LTArrow _ _) = "(" ++ renderType a ++ ")"
    parensIfNeeded _ = renderType a
renderType (LTForall x ty body) =
  "∀ " ++ x ++ " : " ++ renderType ty ++ ", " ++ renderType body
renderType (LTEq a b) = renderType a ++ " = " ++ renderType b
renderType (LTApp f args) = renderType f ++ " " ++ unwords (map renderArg args)
  where
    renderArg a@(LTApp _ _) = "(" ++ renderType a ++ ")"
    renderArg a = renderType a  -- Simple variables don't need parens

-- ---------------------------------------------------------------------------
-- Convenience entry point
-- ---------------------------------------------------------------------------

exportToLean :: IR.Theory -> String
exportToLean = renderLeanTypeDoc . theoryToLeanTypeDoc
