-- | Coq expression rendering for pipeline axiom bodies.
--
-- Mirrors 'Eidos.Pipeline.Targets.LeanProps.MkAxiomSets' for Coq output.
--
-- * 'axBodyToCoq' converts a backend-agnostic 'PA.AxiomBody' to a 'CoqExpr'.
-- * 'mereoExprToCoq' translates an 'IR.MereoExpr' to a 'CoqExpr'.
module Eidos.Pipeline.Targets.CoqProps.MkAxiomSets
  ( -- * Re-exports from the pipeline
    theoryBlocks
    -- * Coq rendering
  , axBodyToCoq
  , mereoExprToCoq
  ) where

import           Data.Char (isAlphaNum)
import qualified Eidos.Pipeline.FromSyntax.IR as IR
import qualified Eidos.Pipeline.IRProcessing.AxiomSet as PA
import           Eidos.Pipeline.IRProcessing.MkAxiomSets (theoryBlocks)
import           Eidos.Pipeline.Targets.CoqProps.CoqExpr

-- ---------------------------------------------------------------------------
-- Name-resolution helpers (Coq naming conventions)
-- ---------------------------------------------------------------------------

minSuffix, maxSuffix :: String
minSuffix = "_Min"
maxSuffix = "_Max"

-- | Sanitize an IR name for use as a Coq identifier.
--
-- Coq accepts Unicode /letters/ (categories L*, M*) but not math-symbol
-- characters (Sm, So, …).  'isAlphaNum' respects Unicode categories, so
-- @ℙ@\/@𝕌@\/@𝔻@ (Lo) pass through unchanged.  Known operator symbols are
-- expanded to alphabetic names to avoid collisions; anything else becomes @_@.
sanitizeName :: String -> String
sanitizeName = concatMap sanitizeChar
  where
    sanitizeChar c
      | isAlphaNum c || c `elem` "_'" = [c]
      | otherwise = case c of
          '+'  -> "Plus"
          '×'  -> "Times"
          '\x2212' -> "Minus"   -- U+2212 MINUS SIGN (−)
          '-'  -> "Minus"
          '⇒'  -> "Arrow"
          '∸'  -> "SDiff"
          '→'  -> "To"
          '∧'  -> "And"
          '∨'  -> "Or"
          '↔'  -> "Iff"
          '∀'  -> "Forall"
          '∃'  -> "Exists"
          '⊤'  -> "Top"
          '⊥'  -> "Bot"
          _    -> "_"

-- | Map IR-internal symbolic names to their Coq identifiers.
resolveName :: String -> String
resolveName n = case n of
  other
    | Just base <- stripSuffix "#min" other -> sanitizeName base ++ minSuffix
    | Just base <- stripSuffix "#max" other -> sanitizeName base ++ maxSuffix
    | otherwise -> sanitizeName other
  where
    stripSuffix suffix str =
      let (front, back) = splitAt (length str - length suffix) str
      in if back == suffix then Just front else Nothing

-- ---------------------------------------------------------------------------
-- AxiomBody → CoqExpr
-- ---------------------------------------------------------------------------

-- | Convert a backend-agnostic 'PA.AxiomBody' to a 'CoqExpr'.
axBodyToCoq :: PA.AxiomBody -> CoqExpr
axBodyToCoq PA.ABDeclProp       = CProp
axBodyToCoq (PA.ABDeclFunc 0)   = CProp
axBodyToCoq (PA.ABDeclFunc n)   = CImpl CProp (axBodyToCoq (PA.ABDeclFunc (n - 1)))
axBodyToCoq (PA.ABMereo e)      = mereoExprToCoq e
axBodyToCoq (PA.ABFuncEq l r)   = CEq (CVar (resolveName l)) (CVar (resolveName r))

-- ---------------------------------------------------------------------------
-- MereoExpr → CoqExpr
-- ---------------------------------------------------------------------------

-- | Translate a 'IR.MereoExpr' to a 'CoqExpr'.
--
-- Mereological operations map to propositional connectives:
--   MSum     → CConj   (+ = /\)
--   MProd    → CDisj   (× = \/)
--   MDiff    → CImpl   (a - b = b -> a)
--   MRevDiff → CImpl   (a ⇒ b = a -> b)
--   MSymDiff → CBicond (a ∸ b = a <-> b)
--   MZero    → True
--   MVar n   → CVar (resolveName n)
--   MAbbrevApp → CApp
--   MBoundedSum → bounded universal quantification
mereoExprToCoq :: IR.MereoExpr -> CoqExpr
mereoExprToCoq (IR.MSum a b)     = CConj   (mereoExprToCoq a) (mereoExprToCoq b)
mereoExprToCoq (IR.MProd a b)    = CDisj   (mereoExprToCoq a) (mereoExprToCoq b)
mereoExprToCoq (IR.MDiff a b)    = CImpl   (mereoExprToCoq b) (mereoExprToCoq a)
mereoExprToCoq (IR.MRevDiff a b) = CImpl   (mereoExprToCoq a) (mereoExprToCoq b)
mereoExprToCoq (IR.MSymDiff a b) = CBicond (mereoExprToCoq a) (mereoExprToCoq b)
mereoExprToCoq (IR.MVar n)       = CVar (resolveName n)
mereoExprToCoq IR.MZero          = CVar "True"
mereoExprToCoq (IR.MAbbrevApp name args) =
  CApp (CVar name) (map mereoExprToCoq args)
mereoExprToCoq (IR.MBoundedSum var lo hi body) =
  CForall var CProp
    (CImpl (CApp (CVar "IsWithinBounds") [mereoExprToCoq lo, mereoExprToCoq hi, CVar var])
           (mereoExprToCoq body))
