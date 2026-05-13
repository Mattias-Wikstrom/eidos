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

-- | Map IR names to their Coq identifiers.
--
-- Sort limit objects already carry names like @\"ℙ_Min\"@ / @\"𝕌_Max\"@ after
-- the naming convention change in 'FromSyntax', so no suffix mangling is
-- needed here.  'sanitizeName' still replaces remaining non-alphanumeric
-- characters (e.g. @\'#\'@ in @\"f#res\"@) with underscores or expansions.
resolveName :: String -> String
resolveName = sanitizeName

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
-- | Select the appropriate Coq bounded-quantifier constructor based on
-- the @isExists@ and @isIndividual@ flags from 'IR.MBoundedSum'.
mkCoqBoundedQuantifier
  :: Bool  -- ^ isExists
  -> Bool  -- ^ isIndividual
  -> String -> String -> String -> CoqExpr -> CoqExpr
mkCoqBoundedQuantifier False False = CBoundedForall
mkCoqBoundedQuantifier False True  = CForallIndividuals
mkCoqBoundedQuantifier True  False = CBoundedExists
mkCoqBoundedQuantifier True  True  = CExistsIndividuals

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
mereoExprToCoq (IR.MBoundedSum isEx isInd var lo hi body) =
  case (lo, hi) of
    (IR.MVar loName, IR.MVar hiName) ->
      let lo' = resolveName loName
          hi' = resolveName hiName
          b   = mereoExprToCoq body
      in mkCoqBoundedQuantifier isEx isInd var lo' hi' b
    _ ->
      let boundAbbrev = if isInd then "IsIndividual" else "IsWithinBounds"
          kw          = if isEx  then CExists else CForall
      in kw var CProp
           (CImpl (CApp (CVar boundAbbrev) [mereoExprToCoq lo, mereoExprToCoq hi, CVar var])
                  (mereoExprToCoq body))
