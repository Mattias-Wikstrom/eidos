-- | Lean 4 expression rendering for pipeline axiom bodies.
--
-- This module contains only Lean-specific logic:
--
-- * 'axBodyToLean' converts a backend-agnostic 'PA.AxiomBody' to a 'LeanExpr'.
-- * 'mereoExprToLean' translates an 'IR.MereoExpr' to a 'LeanExpr'.
--
-- The generation logic (which axioms to produce, their names and tags) lives
-- in 'Eidos.Pipeline.IRProcessing.MkAxiomSets'.  The mereological-to-logical translation
-- of user-written propositions is performed by 'Eidos.Pipeline.FromSyntax.FromSyntax' before
-- the backend sees them; backends receive 'IR.MereoExpr' values via
-- 'IR.factMereoExpr' and should not re-parse 'IR.ResolvedPropExpr' directly.
module Eidos.Pipeline.Targets.LeanProps.MkAxiomSets
  ( -- * Re-exports from the pipeline
    theoryBlocks
    -- * Lean rendering
  , axBodyToLean
  , mereoExprToLean
  ) where

import qualified Eidos.Pipeline.FromSyntax.IR as IR
import qualified Eidos.Pipeline.IRProcessing.AxiomSet as PA
import           Eidos.Pipeline.IRProcessing.MkAxiomSets (theoryBlocks)
import           Eidos.Pipeline.Targets.LeanProps.LeanExpr

-- ---------------------------------------------------------------------------
-- Name-resolution helpers (Lean naming conventions)
-- ---------------------------------------------------------------------------

sanitizeName :: String -> String
sanitizeName = map (\c -> if c == '#' then '_' else c)

-- | Map IR names to their Lean identifiers.
--
-- Sort limit objects already carry names like @\"ℙ_Min\"@ / @\"𝕌_Max\"@ after
-- the naming convention change in 'FromSyntax', so no suffix mangling is
-- needed here.  'sanitizeName' still replaces any remaining @\'#\'@ characters
-- (e.g. in function-internal names like @\"f#res\"@, @\"f#1\"@) with @\'_\'@.
resolveName :: String -> String
resolveName = sanitizeName

-- ---------------------------------------------------------------------------
-- AxiomBody → LeanExpr
-- ---------------------------------------------------------------------------

-- | Convert a backend-agnostic 'PA.AxiomBody' to a 'LeanExpr'.
--
-- * 'PA.ABDeclProp'   → @Prop@
-- * 'PA.ABDeclFunc' n → @Prop → … → Prop@ (n arrows)
-- * 'PA.ABMereo' e    → see 'mereoExprToLean'
-- * 'PA.ABFuncEq' l r → @l = r@ (using 'LEq', not 'LBicond')
axBodyToLean :: PA.AxiomBody -> LeanExpr
axBodyToLean PA.ABDeclProp       = LProp
axBodyToLean (PA.ABDeclFunc 0)   = LProp
axBodyToLean (PA.ABDeclFunc n)   = LImpl LProp (axBodyToLean (PA.ABDeclFunc (n - 1)))
axBodyToLean (PA.ABMereo e)      = mereoExprToLean e
axBodyToLean (PA.ABFuncEq l r)   = LEq (LVar l) (LVar r)

-- ---------------------------------------------------------------------------
-- MereoExpr → LeanExpr
-- ---------------------------------------------------------------------------

-- | Translate a 'IR.MereoExpr' to a 'LeanExpr'.
--
-- Mereological operations map to propositional connectives:
--   MSum     → LConj   (+ = ∧)
--   MProd    → LDisj   (× = ∨)
--   MDiff    → LImpl   (a - b = b → a)
--   MRevDiff → LImpl   (a ⇒ b = a → b)
--   MSymDiff → LBicond (a ∸ b = a ↔ b)
--   MZero    → True    (absolute lattice bottom = propositional truth)
--   MVar n   → LVar (resolveName n)
--   MAbbrevApp → LApp
--   MBoundedSum → bounded universal quantification
--
-- Note: 'IR.MZero' translates to Lean's @True@, not to @ℙ_Min@.
-- @ℙ_Min@ is the minimum of the ℙ sort and must be referenced explicitly
-- via @MVar \"ℙ_Min\"@.  Using 'MZero' to represent @ℙ_Min@ is incorrect.
-- | Select the appropriate Lean bounded-quantifier constructor based on
-- the @isExists@ and @isIndividual@ flags from 'IR.MBoundedSum'.
mkLeanBoundedQuantifier
  :: Bool  -- ^ isExists
  -> Bool  -- ^ isIndividual
  -> String -> String -> String -> LeanExpr -> LeanExpr
mkLeanBoundedQuantifier False False = LBoundedForall
mkLeanBoundedQuantifier False True  = LForallIndividuals
mkLeanBoundedQuantifier True  False = LBoundedExists
mkLeanBoundedQuantifier True  True  = LExistsIndividuals

mereoExprToLean :: IR.MereoExpr -> LeanExpr
mereoExprToLean (IR.MSum a b)     = LConj   (mereoExprToLean a) (mereoExprToLean b)
mereoExprToLean (IR.MProd a b)    = LDisj   (mereoExprToLean a) (mereoExprToLean b)
mereoExprToLean (IR.MDiff a b)    = LImpl   (mereoExprToLean b) (mereoExprToLean a)
mereoExprToLean (IR.MRevDiff a b) = LImpl   (mereoExprToLean a) (mereoExprToLean b)
mereoExprToLean (IR.MSymDiff a b) = LBicond (mereoExprToLean a) (mereoExprToLean b)
mereoExprToLean (IR.MVar n)       = LVar (resolveName n)
mereoExprToLean IR.MZero          = LTop
mereoExprToLean (IR.MAbbrevApp "ProjectIntoInterval" [x, lo, hi]) =
  LProjectIntoInterval (mereoExprToLean x) (mereoExprToLean lo) (mereoExprToLean hi)
mereoExprToLean (IR.MAbbrevApp name args) =
  LApp (LVar name) (map mereoExprToLean args)
mereoExprToLean (IR.MBoundedSum var lo hi body) =
  case (lo, hi) of
    (IR.MVar loName, IR.MVar hiName) ->
      let lo' = resolveName loName
          hi' = resolveName hiName
          b   = mereoExprToLean body
      in LBoundedForall var lo' hi' b
    _ ->
      LForallKw var LProp
           (LImpl (LApp (LVar "IsWithinBounds") [mereoExprToLean lo, mereoExprToLean hi, LVar var])
                      (mereoExprToLean body))
mereoExprToLean (IR.MBoundedProduct var lo hi body) =
  case (lo, hi) of
    (IR.MVar loName, IR.MVar hiName) ->
      let lo' = resolveName loName
          hi' = resolveName hiName
          b   = mereoExprToLean body
      in LBoundedExists var lo' hi' b
    _ ->
      LExists var LProp
           (LImpl (LApp (LVar "IsWithinBounds") [mereoExprToLean lo, mereoExprToLean hi, LVar var])
                      (mereoExprToLean body))
mereoExprToLean (IR.MSumOfIndividuals var lo hi body) =
  case (lo, hi) of
    (IR.MVar loName, IR.MVar hiName) ->
      let lo' = resolveName loName
          hi' = resolveName hiName
          b   = mereoExprToLean body
      in LForallIndividuals var lo' hi' b
    _ ->
      LForallKw var LProp
           (LImpl (LApp (LVar "IsIndividual") [mereoExprToLean lo, mereoExprToLean hi, LVar var])
                      (mereoExprToLean body))
mereoExprToLean (IR.MProductOfIndividuals var lo hi body) =
  case (lo, hi) of
    (IR.MVar loName, IR.MVar hiName) ->
      let lo' = resolveName loName
          hi' = resolveName hiName
          b   = mereoExprToLean body
      in LExistsIndividuals var lo' hi' b
    _ ->
      LExists var LProp
           (LImpl (LApp (LVar "IsIndividual") [mereoExprToLean lo, mereoExprToLean hi, LVar var])
                      (mereoExprToLean body))