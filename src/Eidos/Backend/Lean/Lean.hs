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
module Eidos.Backend.Lean.Lean
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

import qualified Eidos.IR as IR
import Data.List (intercalate)
import Debug.Trace (trace) 

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
theoryToLeanTypeDoc theory =
  LeanTypeDoc
    { ltdTheoryName = "_Main"
    , ltdDecls      = structureDecls
    }
  where
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
      , map factToField (zip [1..] userFacts)
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
    
    -- User facts (assertions and metafacts)
    userFacts = [ f | f <- IR.theoryFacts theory
                    , IR.factCategory (IR.factKind f) == IR.FCUserInput
                    , IR.factSubkind  (IR.factKind f) `elem` [IR.FSAssertion, IR.FSMetafactsFact] ]

    factToField (idx, fact) =
      let fieldName = "fact" ++ show idx
          body = propExprToLeanType (maybe (error "factToField: no propExpr") id (IR.factPropExpr fact))
          foralls = wrapFreeVars (IR.factFreeVars fact)
          expr = foralls body
      in LTDField fieldName expr
    
    -- Wrap free variables as ∀ quantifiers
    wrapFreeVars [] body = body
    wrapFreeVars (vd:rest) body =
      let varName = IR.resolvedVarName vd
          -- Determine the type: if it's a subset variable, it's S → P; otherwise it's S
          varType = if IR.resolvedVarIsSet vd
                    then LTArrow (LTVar (IR.sortName (IR.resolvedVarSort vd))) (LTVar "P")
                    else LTVar (IR.sortName (IR.resolvedVarSort vd))
      in LTForall varName varType (wrapFreeVars rest body)
    
    -- Convert resolved prop expressions to Lean type expressions
    propExprToLeanType :: IR.ResolvedPropExpr -> LeanTypeExpr
    propExprToLeanType (IR.ResolvedPropBicond left rests) =
      case rests of
        [] -> rightImplToLeanType left
        _  -> error "Biconditional chains not yet supported in Lean type export"
    
    rightImplToLeanType :: IR.ResolvedRightImpl -> LeanTypeExpr
    rightImplToLeanType (IR.ResolvedRightImpl left Nothing) =
      leftImplToLeanType left
    rightImplToLeanType (IR.ResolvedRightImpl left (Just (_, right))) =
      LTArrow (leftImplToLeanType left) (rightImplToLeanType right)
    
    leftImplToLeanType :: IR.ResolvedLeftImpl -> LeanTypeExpr
    leftImplToLeanType (IR.ResolvedLeftImpl left []) =
      disjToLeanType left
    leftImplToLeanType _ = error "Left implication not yet supported in Lean type export"
    
    disjToLeanType :: IR.ResolvedDisj -> LeanTypeExpr
    disjToLeanType (IR.ResolvedDisj left []) = conjToLeanType left
    disjToLeanType _ = error "Disjunction not yet supported in Lean type export"
    
    conjToLeanType :: IR.ResolvedConj -> LeanTypeExpr
    conjToLeanType (IR.ResolvedConj left []) = negToLeanType left
    conjToLeanType _ = error "Conjunction not yet supported in Lean type export"
    
    negToLeanType :: IR.ResolvedNeg -> LeanTypeExpr
    negToLeanType (IR.ResolvedNegNot _) = error "Negation not yet supported in Lean type export"
    negToLeanType (IR.ResolvedNegChild q) = quantifiedToLeanType q
    
    quantifiedToLeanType :: IR.ResolvedQuantified -> LeanTypeExpr
    quantifiedToLeanType (IR.ResolvedQuantified [] atom) = atomicToLeanType atom
    quantifiedToLeanType _ = error "Nested quantifiers not yet supported in Lean type export"
    
    atomicToLeanType :: IR.ResolvedAtomicProp -> LeanTypeExpr
    atomicToLeanType (IR.ResolvedAtomicConstant ref) =
      LTVar (IR.resolvedConstRefName ref)
    atomicToLeanType (IR.ResolvedAtomicTermPair tp) = termPairToLeanType tp

    -- DEBUG: Show the term pair structure
    debugTermPair :: IR.ResolvedTermPair -> String
    debugTermPair (IR.ResolvedTermPair left rights _) =
      "Left: " ++ show (termDebug left) ++ 
      ", Rights: " ++ show (map debugRFT rights)
    
    debugRFT :: IR.ResolvedRelationFollowedByTerm -> String
    debugRFT (IR.ResolvedRelationFollowedByTerm _ op _ right) =
      "op=" ++ op ++ " right=" ++ show (termDebug right)
    
    termDebug :: IR.ResolvedTerm -> String
    termDebug (IR.ResolvedTerm factor [] _) = factorDebug factor
    termDebug _ = "<complex-term>"
    
    factorDebug :: IR.ResolvedFactor -> String
    factorDebug (IR.ResolvedFactor base [] _) = baseDebug base
    factorDebug (IR.ResolvedFactor base suffixes _) = 
      baseDebug base ++ show suffixes
    
    baseDebug :: IR.ResolvedBaseTerm -> String
    baseDebug (IR.ResolvedBTAtomic ref) = IR.resolvedConstRefName ref
    baseDebug _ = "<other>"

    termPairToLeanType :: IR.ResolvedTermPair -> LeanTypeExpr
    termPairToLeanType (IR.ResolvedTermPair left rights _) =
      case rights of
        [rft] | IR.resolvedRFTOp rft == "=" -> 
          LTEq (termToLeanType left) (termToLeanType (IR.resolvedRFTRight rft))
        [rft] | IR.resolvedRFTOp rft == "↔" ->
          LTEq (termToLeanType left) (termToLeanType (IR.resolvedRFTRight rft))
        [] -> termToLeanType left  -- No relation, just a bare term (e.g., parenthesized expr)
        _ -> LTVar "<multiple-relations>"
    
    termToLeanType :: IR.ResolvedTerm -> LeanTypeExpr
    termToLeanType (IR.ResolvedTerm factor [] _) = factorToLeanType factor
    termToLeanType _ = LTVar "<complex-term>"
    
    factorToLeanType :: IR.ResolvedFactor -> LeanTypeExpr
    factorToLeanType (IR.ResolvedFactor base [] _) = baseTermToLeanType base
    factorToLeanType (IR.ResolvedFactor base suffixes _) =
      foldl applySuffix (baseTermToLeanType base) suffixes
    
    applySuffix :: LeanTypeExpr -> IR.ResolvedTermSuffix -> LeanTypeExpr
    applySuffix expr (IR.ResolvedSuffixCall args) =
      LTApp expr (map termToLeanType args)
    applySuffix expr _ = expr
    
    baseTermToLeanType :: IR.ResolvedBaseTerm -> LeanTypeExpr
    baseTermToLeanType (IR.ResolvedBTAtomic ref) =
      LTVar (IR.resolvedConstRefName ref)
    baseTermToLeanType (IR.ResolvedBTPropParen inner) = propExprToLeanType inner
    baseTermToLeanType (IR.ResolvedBTTermParen term) = termToLeanType term
    -- Set comprehension { x : A | φ(x) } and description ιx : A φ(x) both
    -- translate to: ∀ x : A, φ'(x) → x
    baseTermToLeanType (IR.ResolvedBTSetComprehension sc) =
      let varN = IR.resolvedVarName (IR.resolvedSCVar sc)
          sn   = IR.sortName (IR.resolvedVarSort (IR.resolvedSCVar sc))
          phi  = propExprToLeanType (IR.resolvedSCBody sc)
      in LTForall varN (LTVar sn) (LTArrow phi (LTVar varN))
    baseTermToLeanType (IR.ResolvedBTDescription desc) =
      let varN = IR.resolvedVarName (IR.resolvedDescVar desc)
          sn   = IR.sortName (IR.resolvedVarSort (IR.resolvedDescVar desc))
          phi  = propExprToLeanType (IR.resolvedDescBody desc)
      in LTForall varN (LTVar sn) (LTArrow phi (LTVar varN))
    baseTermToLeanType _ = LTVar "<unsupported-base>"

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