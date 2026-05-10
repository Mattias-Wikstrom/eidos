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

minSuffix, maxSuffix :: String
minSuffix = "_Min"
maxSuffix = "_Max"

sanitizeName :: String -> String
sanitizeName = map (\c -> if c == '#' then '_' else c)

-- | Map IR-internal symbolic names to their Lean identifiers.
--
-- This is the only place in the Lean backend that knows about the IR naming
-- conventions (e.g. @\"ℙ#min\"@ → @\"ℙ_Min\"@).  The rest of the backend
-- works with opaque 'LeanExpr' values.
resolveName :: String -> String
resolveName n = case n of
  "⊤"     -> "ℙ_Min"
  "⊥"     -> "ℙ_Max"
  "ℙ#min" -> "ℙ_Min"
  "ℙ#max" -> "ℙ_Max"
  "𝕌#min" -> "𝕌_Min"
  "𝕌#max" -> "𝕌_Max"
  other
    | Just base <- stripSuffix "#min" other -> sanitizeName base ++ minSuffix
    | Just base <- stripSuffix "#max" other -> sanitizeName base ++ maxSuffix
    | otherwise -> sanitizeName other
  where
    stripSuffix suffix str =
      let (front, back) = splitAt (length str - length suffix) str
      in if back == suffix then Just front else Nothing

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
-- via @MVar \"ℙ#min\"@.  Using 'MZero' to represent @ℙ_Min@ is incorrect.
mereoExprToLean :: IR.MereoExpr -> LeanExpr
mereoExprToLean (IR.MSum a b)     = LConj   (mereoExprToLean a) (mereoExprToLean b)
mereoExprToLean (IR.MProd a b)    = LDisj   (mereoExprToLean a) (mereoExprToLean b)
mereoExprToLean (IR.MDiff a b)    = LImpl   (mereoExprToLean b) (mereoExprToLean a)
mereoExprToLean (IR.MRevDiff a b) = LImpl   (mereoExprToLean a) (mereoExprToLean b)
mereoExprToLean (IR.MSymDiff a b) = LBicond (mereoExprToLean a) (mereoExprToLean b)
mereoExprToLean (IR.MVar n)       = LVar (resolveName n)
mereoExprToLean IR.MZero          = LVar "True"
mereoExprToLean (IR.MAbbrevApp "ProjectIntoInterval" [x, lo, hi]) =
  LProjectIntoInterval (mereoExprToLean x) (mereoExprToLean lo) (mereoExprToLean hi)
mereoExprToLean (IR.MAbbrevApp name args) =
  LApp (LVar name) (map mereoExprToLean args)
mereoExprToLean (IR.MBoundedSum var lo hi body) =
  case (lo, hi) of
    (IR.MVar loName, IR.MVar hiName) ->
      LBoundedForall var (resolveName loName) (resolveName hiName) (mereoExprToLean body)
    _ ->
      LForallKw var LProp
        (LImpl (LApp (LVar "IsWithinBounds") [mereoExprToLean lo, mereoExprToLean hi, LVar var])
               (mereoExprToLean body))
