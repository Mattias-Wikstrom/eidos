-- | Type checking for EidosLang expressions.
--
-- This module provides two levels of classification:
--   Level 1: Classifies expressions into four categories:
--     - Functions/Relations (with arities)
--     - Sorts
--     - Mereological objects
--     - Theories
--   Level 2: Refines mereological objects into:
--     - Individuals
--     - Sets
--     - Propositions
--     - Bare mereological objects (explicit any)
module Eidos.TypeCheck
  ( -- * Level 1 classification
    Level1Type(..)
  , classifyLevel1
  , checkLevel1
    -- * Level 2 classification
  , Level2Type(..)
  , TypeWithAny(..)
  , classifyLevel2
  , convertLevel2
    -- * Combined checking
  , TypeCheckResult(..)
  , checkExpression
  , validateOperation
    -- * Utilities
  , acceptIndividualOperand
  , acceptSetOperand
  , acceptPropositionOperand
  , isExplicitAny
    -- * Resolved expression checking
  , checkResolvedTerm
  , checkSetOperand
  , checkPropositionOperand
  , checkIndividualOperand
  , checkVarDecl
  , typeCheckResolvedExpr
  ) where

import           Data.List       (find)
import qualified Data.Map.Strict as Map
import           Data.Maybe      (fromMaybe)

import           Eidos.AST
import qualified Eidos.AST as AST
import           Eidos.IR
import qualified Eidos.IR as IR

-- ---------------------------------------------------------------------------
-- Level 1 Classification
-- ---------------------------------------------------------------------------

data Level1Type
  = L1Function Int          -- ^ Function/relation with given arity
  | L1Sort                  -- ^ Sort (like a type)
  | L1Mereological          -- ^ Mereological object (individual/set/proposition)
  | L1Theory                -- ^ Theory (namespace)
  | L1Unknown               -- ^ Unknown or error
  deriving (Show, Eq)

-- | Classify an expression at level 1 based on its entity type.
classifyLevel1 :: Entity -> Level1Type
classifyLevel1 (EntitySort _) = L1Sort
classifyLevel1 (EntityFunction f) = L1Function (length (funcArgSorts f))
classifyLevel1 (EntityRelation r) = L1Function (length (relArgSorts r))
classifyLevel1 (EntityMereological _) = L1Mereological
classifyLevel1 (EntityTheory _) = L1Theory

-- | Check level 1 compatibility for an operation.
checkLevel1 :: Level1Type -> String -> Level1Type -> Either String Bool
checkLevel1 L1Mereological op L1Mereological =
  case op of
    "+"  -> Right True
    "×"  -> Right True
    "-"  -> Right True
    "⇒"  -> Right True
    "∸"  -> Right True
    "≤"  -> Right True
    "="  -> Right True
    _    -> Left $ "Operation '" ++ op ++ "' requires mereological operands"
checkLevel1 L1Sort _ L1Sort = Right True
checkLevel1 (L1Function arity1) op (L1Function arity2)
  | op == "∘" && arity1 == arity2 = Right True
  | op == "∘" = Left $ "Function composition requires same arity, got " ++ show arity1 ++ " and " ++ show arity2
  | otherwise = Right True  -- Function application checked elsewhere
checkLevel1 L1Theory _ L1Theory = Right True
checkLevel1 t1 op t2 =
  Left $ "Level 1 type mismatch: " ++ show t1 ++ " " ++ op ++ " " ++ show t2

-- ---------------------------------------------------------------------------
-- Level 2 Classification (Mereological Subtypes)
-- ---------------------------------------------------------------------------

-- | Fine-grained classification of a mereological expression, used by the
-- operator-validation logic (e.g. checking that ∈ has an individual on the
-- left and a set on the right).
--
-- __Relationship to 'ExprType'\/'MereologicalSubtype' in "Eidos.IR"__:
-- 'ExprType' is the type attached to every resolved term in the IR tree and
-- carries the same individual\/set\/proposition\/mereological distinction via
-- 'MereologicalSubtype'.  'Level2Type' is a separate view used only inside
-- 'TypeCheck' to drive operator checks (e.g. 'acceptIndividualOperand').
-- The bridge is 'getResolvedTermType' in "Eidos.FromSyntax", which converts
-- an 'ExprType' to a 'Level2Type'.
-- Keeping them separate lets 'TypeCheck' evolve its classification logic
-- independently of the IR wire format, but the two must be kept consistent.
-- A future refactor could unify them via a @toLevel2Type :: ExprType ->
-- Level2Type@ conversion function and drop the duplication.
data Level2Type
  = L2Individual            -- ^ Individual (can be element of a set)
  | L2Set                   -- ^ Set (contains individuals)
  | L2Proposition           -- ^ Proposition (can be used in logical connectives)
  | L2BareMereological      -- ^ Bare mereological object (explicit any)
  | L2Function Int          -- ^ Function (with arity)
  | L2Sort                  -- ^ Sort
  | L2Theory                -- ^ Theory
  deriving (Show, Eq)

-- | Type with explicit any marker
type TypeWithAny = (Level2Type, Bool)  -- Bool = isExplicitAny (from #mereological)

-- | Classify an expression at level 2.
classifyLevel2 :: Entity -> Level2Type
classifyLevel2 (EntitySort _) = L2Sort
classifyLevel2 (EntityFunction f) = L2Function (length (funcArgSorts f))
classifyLevel2 (EntityRelation r) = L2Function (length (relArgSorts r))
classifyLevel2 (EntityMereological m) =
  case mereoKind m of
    MereologicalEntityKindIndividual -> L2Individual
    MereologicalEntityKindSet -> L2Set
    MereologicalEntityKindProposition -> L2Proposition
    _ -> L2BareMereological
classifyLevel2 (EntityTheory _) = L2Theory

-- | Convert between mereological views using #individual, #set, #proposition, #mereological.
convertLevel2 :: Level2Type -> String -> Maybe (Level2Type, Bool)
convertLevel2 L2Individual "#set" = Just (L2Set, False)
convertLevel2 L2Individual "#proposition" = Just (L2Proposition, False)
convertLevel2 L2Individual "#mereological" = Just (L2BareMereological, True)
convertLevel2 L2Set "#individual" = Just (L2Individual, False)
convertLevel2 L2Set "#proposition" = Just (L2Proposition, False)
convertLevel2 L2Set "#mereological" = Just (L2BareMereological, True)
convertLevel2 L2Proposition "#individual" = Just (L2Individual, False)
convertLevel2 L2Proposition "#set" = Just (L2Set, False)
convertLevel2 L2Proposition "#mereological" = Just (L2BareMereological, True)
convertLevel2 L2BareMereological "#individual" = Just (L2Individual, False)
convertLevel2 L2BareMereological "#set" = Just (L2Set, False)
convertLevel2 L2BareMereological "#proposition" = Just (L2Proposition, False)
convertLevel2 L2BareMereological "#mereological" = Just (L2BareMereological, True)
convertLevel2 _ _ = Nothing

-- | Check if a type has explicit any (from #mereological)
isExplicitAny :: TypeWithAny -> Bool
isExplicitAny (_, True) = True
isExplicitAny _ = False

-- | Accept an operand as individual (for ∈ left side)
acceptIndividualOperand :: TypeWithAny -> Bool
acceptIndividualOperand (L2Individual, _) = True
acceptIndividualOperand (_, True) = True  -- explicit any passes
acceptIndividualOperand _ = False

-- | Accept an operand as set (for ⊆, ∪, ∩, ∈ right side)
acceptSetOperand :: TypeWithAny -> Bool
acceptSetOperand (L2Set, _) = True
acceptSetOperand (_, True) = True  -- explicit any passes
acceptSetOperand _ = False

-- | Accept an operand as proposition (for →, ∧, ∨, ¬)
acceptPropositionOperand :: TypeWithAny -> Bool
acceptPropositionOperand (L2Proposition, _) = True
acceptPropositionOperand (_, True) = True  -- explicit any passes
acceptPropositionOperand _ = False

-- ---------------------------------------------------------------------------
-- Combined Type Checking
-- ---------------------------------------------------------------------------

data TypeCheckResult = TypeCheckResult
  { tcLevel1 :: Level1Type
  , tcLevel2 :: Maybe TypeWithAny
  , tcErrors :: [String]
  } deriving (Show)

-- | Check an expression's type at both levels.
checkExpression :: Entity -> Maybe String -> TypeCheckResult
checkExpression entity mbConversion =
  let l1 = classifyLevel1 entity
      l2 = case mbConversion of
             Nothing -> Just (classifyLevel2 entity, False)
             Just "#mereological" -> Just (L2BareMereological, True)
             Just conv -> convertLevel2 (classifyLevel2 entity) conv
  in TypeCheckResult l1 l2 []

-- | Validate an operation between two expressions.
validateOperation
  :: Entity -> Maybe String -> String -> Entity -> Maybe String
  -> Either [String] (TypeCheckResult, TypeCheckResult)
validateOperation left mbConvLeft op right mbConvRight = do
  let leftResult = checkExpression left mbConvLeft
  let rightResult = checkExpression right mbConvRight
  
  let errors = tcErrors leftResult ++ tcErrors rightResult
  
  -- Check level 1 compatibility
  case checkLevel1 (tcLevel1 leftResult) op (tcLevel1 rightResult) of
    Left err -> Left (errors ++ [err])
    Right _ -> return ()
  
  -- Check level 2 specific rules
  let l2Left = tcLevel2 leftResult
  let l2Right = tcLevel2 rightResult
  
  case op of
    "∈" -> do
      case (l2Left, l2Right) of
        (Just leftT, Just rightT) -> do
          if not (acceptIndividualOperand leftT)
            then Left (errors ++ ["Left operand of ∈ must be an individual, got " ++ show (fst leftT)])
            else if not (acceptSetOperand rightT)
              then Left (errors ++ ["Right operand of ∈ must be a set, got " ++ show (fst rightT)])
              else Right ()
        _ -> Right ()
      return ()
    
    "⊆" -> do
      case (l2Left, l2Right) of
        (Just leftT, Just rightT) -> do
          if not (acceptSetOperand leftT)
            then Left (errors ++ ["Left operand of ⊆ must be a set, got " ++ show (fst leftT)])
            else if not (acceptSetOperand rightT)
              then Left (errors ++ ["Right operand of ⊆ must be a set, got " ++ show (fst rightT)])
              else Right ()
        _ -> Right ()
      return ()
    
    "∪" -> do
      case (l2Left, l2Right) of
        (Just leftT, Just rightT) -> do
          if not (acceptSetOperand leftT)
            then Left (errors ++ ["Left operand of ∪ must be a set, got " ++ show (fst leftT)])
            else if not (acceptSetOperand rightT)
              then Left (errors ++ ["Right operand of ∪ must be a set, got " ++ show (fst rightT)])
              else Right ()
        _ -> Right ()
      return ()
    
    "∩" -> do
      case (l2Left, l2Right) of
        (Just leftT, Just rightT) -> do
          if not (acceptSetOperand leftT)
            then Left (errors ++ ["Left operand of ∩ must be a set, got " ++ show (fst leftT)])
            else if not (acceptSetOperand rightT)
              then Left (errors ++ ["Right operand of ∩ must be a set, got " ++ show (fst rightT)])
              else Right ()
        _ -> Right ()
      return ()
    
    "→" -> do
      case (l2Left, l2Right) of
        (Just leftT, Just rightT) -> do
          if not (acceptPropositionOperand leftT)
            then Left (errors ++ ["Left operand of → must be a proposition, got " ++ show (fst leftT)])
            else if not (acceptPropositionOperand rightT)
              then Left (errors ++ ["Right operand of → must be a proposition, got " ++ show (fst rightT)])
              else Right ()
        _ -> Right ()
      return ()
    
    "∧" -> do
      case (l2Left, l2Right) of
        (Just leftT, Just rightT) -> do
          if not (acceptPropositionOperand leftT)
            then Left (errors ++ ["Left operand of ∧ must be a proposition, got " ++ show (fst leftT)])
            else if not (acceptPropositionOperand rightT)
              then Left (errors ++ ["Right operand of ∧ must be a proposition, got " ++ show (fst rightT)])
              else Right ()
        _ -> Right ()
      return ()
    
    "∨" -> do
      case (l2Left, l2Right) of
        (Just leftT, Just rightT) -> do
          if not (acceptPropositionOperand leftT)
            then Left (errors ++ ["Left operand of ∨ must be a proposition, got " ++ show (fst leftT)])
            else if not (acceptPropositionOperand rightT)
              then Left (errors ++ ["Right operand of ∨ must be a proposition, got " ++ show (fst rightT)])
              else Right ()
        _ -> Right ()
      return ()
    
    "¬" -> do
      case l2Right of
        Just rightT -> do
          if not (acceptPropositionOperand rightT)
            then Left (errors ++ ["Operand of ¬ must be a proposition, got " ++ show (fst rightT)])
            else Right ()
        _ -> Right ()
      return ()
    
    _ -> return ()
  
  return (leftResult, rightResult)

-- ---------------------------------------------------------------------------
-- Type checking for resolved expressions (integration with IR)
-- ---------------------------------------------------------------------------

-- | Check a resolved term's type and return its Level2Type.
checkResolvedTerm :: ResolvedTerm -> Either String Level2Type
checkResolvedTerm term = do
  let ty = resolvedTermType term
  case exprMajorType ty of
    MajorTypeMereologicalObject ->
      case exprMereoSubtype ty of
        Just MereologicalSubtypeIndividual -> Right L2Individual
        Just MereologicalSubtypeSet -> Right L2Set
        Just MereologicalSubtypeProposition -> Right L2Proposition
        Just MereologicalSubtypeMereological -> Right L2BareMereological
        Nothing -> Right L2BareMereological
    MajorTypeFunction -> Right (L2Function (fromMaybe 0 (exprNumArgs ty)))
    MajorTypeSort -> Right L2Sort

-- | Check if a resolved term is a valid set (ignores the result).
checkSetOperand :: ResolvedTerm -> Either String ()
checkSetOperand term = do
  _ <- checkResolvedTerm term
  return ()

-- | Check if a resolved term is a valid proposition (ignores the result).
checkPropositionOperand :: ResolvedTerm -> Either String ()
checkPropositionOperand term = do
  _ <- checkResolvedTerm term
  return ()

-- | Check if a resolved term is a valid individual (ignores the result).
checkIndividualOperand :: ResolvedTerm -> Either String ()
checkIndividualOperand term = do
  _ <- checkResolvedTerm term
  return ()

-- ---------------------------------------------------------------------------
-- Type checking for variable declarations
-- ---------------------------------------------------------------------------

-- | Check that a variable declaration's sort is valid.
checkVarDecl :: Sort -> Either String ()
checkVarDecl sort = do
  let kind = sortKind sort
  case kind of
    SortKindUniverse -> Right ()
    SortKindDomain -> Right ()
    SortKindProp -> Right ()
    SortKindFromSignature -> Right ()
    SortKindProduct -> Left "Product sorts cannot be used directly in variable declarations"
    _ -> Left $ "Invalid sort kind for variable: " ++ show kind

-- ---------------------------------------------------------------------------
-- Resolved expression type checking
-- ---------------------------------------------------------------------------

-- | Type check a resolved proposition expression.
typeCheckResolvedExpr :: ResolvedPropExpr -> Either String ()
typeCheckResolvedExpr (ResolvedPropBicond left rests) = do
  checkResolvedRightImpl left
  mapM_ (\(ResolvedPropRest _ right) -> checkResolvedRightImpl right) rests

checkResolvedRightImpl :: ResolvedRightImpl -> Either String ()
checkResolvedRightImpl (ResolvedRightImpl left mbRight) = do
  checkResolvedLeftImpl left
  case mbRight of
    Nothing       -> return ()
    Just (_, right) -> checkResolvedRightImpl right

checkResolvedLeftImpl :: ResolvedLeftImpl -> Either String ()
checkResolvedLeftImpl (ResolvedLeftImpl disj rests) = do
  checkResolvedDisj disj
  mapM_ (\(ResolvedLeftImplRest _ d) -> checkResolvedDisj d) rests

checkResolvedDisj :: ResolvedDisj -> Either String ()
checkResolvedDisj (ResolvedDisj conj rests) = do
  checkResolvedConj conj
  mapM_ (\(ResolvedDisjRest _ c) -> checkResolvedConj c) rests

checkResolvedConj :: ResolvedConj -> Either String ()
checkResolvedConj (ResolvedConj neg rests) = do
  checkResolvedNeg neg
  mapM_ (\(ResolvedConjRest _ n) -> checkResolvedNeg n) rests

checkResolvedNeg :: ResolvedNeg -> Either String ()
checkResolvedNeg (ResolvedNegNot inner) = checkResolvedNeg inner
checkResolvedNeg (ResolvedNegChild quantified) = checkResolvedQuantified quantified

checkResolvedQuantified :: ResolvedQuantified -> Either String ()
checkResolvedQuantified (ResolvedQuantified qs atomic) = do
  mapM_ checkResolvedQuantifier qs
  checkResolvedAtomicProp atomic

checkResolvedQuantifier :: ResolvedQuantifier -> Either String ()
checkResolvedQuantifier (ResolvedQForall vd) =
  checkVarDecl (resolvedVarSort vd)
checkResolvedQuantifier (ResolvedQExists vd) =
  checkVarDecl (resolvedVarSort vd)

checkResolvedAtomicProp :: ResolvedAtomicProp -> Either String ()
checkResolvedAtomicProp (ResolvedAtomicTermPair tp) = checkResolvedTermPair tp
checkResolvedAtomicProp (ResolvedAtomicConstant _) = Right ()

checkResolvedTermPair :: ResolvedTermPair -> Either String ()
checkResolvedTermPair (ResolvedTermPair left rights _) = do
  _ <- checkResolvedTerm left
  mapM_ checkResolvedRFT rights
  return ()

checkResolvedRFT :: ResolvedRelationFollowedByTerm -> Either String ()
checkResolvedRFT (ResolvedRelationFollowedByTerm _ op _ right) = do
  _ <- checkResolvedTerm right
  case op of
    "∈" -> return ()
    "⊆" -> checkSetOperand right
    "≤" -> return ()
    "=" -> return ()
    _ -> Left $ "Unknown operator in relation: " ++ op

checkResolvedOFF :: ResolvedOperationFollowedByFactor -> Either String ()
checkResolvedOFF (ResolvedOperationFollowedByFactor _ op right) = do
  checkResolvedFactor right
  case op of
    "+" -> return ()
    "×" -> return ()
    "-" -> return ()
    "⇒" -> return ()
    "∸" -> return ()
    "∪" -> checkSetOperand (termFromFactor right)
    "∩" -> checkSetOperand (termFromFactor right)
    _ -> Left $ "Unknown term operator: " ++ op

checkResolvedFactor :: ResolvedFactor -> Either String ()
checkResolvedFactor (ResolvedFactor base _ _) = do
  checkResolvedBaseTerm base

checkResolvedBaseTerm :: ResolvedBaseTerm -> Either String ()
checkResolvedBaseTerm (ResolvedBTAtomic constRef) = do
  case resolvedConstEntity constRef of
    EntitySort _ -> return ()
    EntityFunction _ -> return ()
    EntityMereological m -> do
      let t = classifyLevel2 (EntityMereological m)
      case t of
        L2Individual -> return ()
        L2Set -> return ()
        L2Proposition -> return ()
        L2BareMereological -> return ()
        _ -> Left "Invalid mereological entity"
    EntityRelation _ -> return ()
    EntityTheory _ -> return ()
checkResolvedBaseTerm (ResolvedBTEvaluationInTheory _) = Right ()
checkResolvedBaseTerm (ResolvedBTProjectionToSort (ResolvedProjectionToSort _ operand)) = do
  _ <- checkResolvedTerm operand
  return ()
checkResolvedBaseTerm (ResolvedBTProjectionToInterval (ResolvedProjectionToInterval _ _ operand)) = do
  _ <- checkResolvedTerm operand
  return ()
checkResolvedBaseTerm (ResolvedBTGeneralizedSumOrProduct (ResolvedGeneralizedSumOrProduct _ var operand)) = do
  case var of
    Left vd -> checkVarDecl (resolvedVarSort vd)
    Right _ -> return ()
  _ <- checkResolvedTerm operand
  return ()
checkResolvedBaseTerm (ResolvedBTSingleton inner) = do
  _ <- checkResolvedTerm inner
  return ()
checkResolvedBaseTerm (ResolvedBTParen _) = Right ()

-- Helper to create a ResolvedTerm from a ResolvedFactor (simplified)
termFromFactor :: ResolvedFactor -> ResolvedTerm
termFromFactor factor = ResolvedTerm factor [] (resolvedFactorType factor)


-- Add to TypeCheck.hs:

-- | Validate a binary operation between two resolved terms.
validateBinaryOp :: ResolvedTerm -> String -> ResolvedTerm -> Either String ()
validateBinaryOp left op right = do
  leftType <- checkResolvedTerm left
  rightType <- checkResolvedTerm right
  
  -- For now, treat all resolved terms as non-any (they come from entities)
  -- The any flag would come from explicit #mereological conversions
  let leftWithAny = (leftType, False)
  let rightWithAny = (rightType, False)
  
  case op of
    "∈" -> do
      if not (acceptIndividualOperand leftWithAny)
        then Left $ "Left operand of ∈ must be an individual, got " ++ show leftType
        else if not (acceptSetOperand rightWithAny)
          then Left $ "Right operand of ∈ must be a set, got " ++ show rightType
          else Right ()
    "⊆" -> do
      if not (acceptSetOperand leftWithAny)
        then Left $ "Left operand of ⊆ must be a set, got " ++ show leftType
        else if not (acceptSetOperand rightWithAny)
          then Left $ "Right operand of ⊆ must be a set, got " ++ show rightType
          else Right ()
    "∪" -> do
      if not (acceptSetOperand leftWithAny)
        then Left $ "Left operand of ∪ must be a set, got " ++ show leftType
        else if not (acceptSetOperand rightWithAny)
          then Left $ "Right operand of ∪ must be a set, got " ++ show rightType
          else Right ()
    "∩" -> do
      if not (acceptSetOperand leftWithAny)
        then Left $ "Left operand of ∩ must be a set, got " ++ show leftType
        else if not (acceptSetOperand rightWithAny)
          then Left $ "Right operand of ∩ must be a set, got " ++ show rightType
          else Right ()
    "→" -> do
      if not (acceptPropositionOperand leftWithAny)
        then Left $ "Left operand of → must be a proposition, got " ++ show leftType
        else if not (acceptPropositionOperand rightWithAny)
          then Left $ "Right operand of → must be a proposition, got " ++ show rightType
          else Right ()
    "∧" -> do
      if not (acceptPropositionOperand leftWithAny)
        then Left $ "Left operand of ∧ must be a proposition, got " ++ show leftType
        else if not (acceptPropositionOperand rightWithAny)
          then Left $ "Right operand of ∧ must be a proposition, got " ++ show rightType
          else Right ()
    "∨" -> do
      if not (acceptPropositionOperand leftWithAny)
        then Left $ "Left operand of ∨ must be a proposition, got " ++ show leftType
        else if not (acceptPropositionOperand rightWithAny)
          then Left $ "Right operand of ∨ must be a proposition, got " ++ show rightType
          else Right ()
    "¬" -> do
      if not (acceptPropositionOperand rightWithAny)
        then Left $ "Operand of ¬ must be a proposition, got " ++ show rightType
        else Right ()
    _ -> Right ()