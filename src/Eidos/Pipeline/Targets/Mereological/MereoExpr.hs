-- | Core expression types for Mereological output.
--
-- Mirrors 'Eidos.Pipeline.Targets.LeanProps.LeanExpr' and
-- 'Eidos.Pipeline.Targets.CoqProps.CoqExpr' for the Mereological output format.
--
-- The 'MereoExpr' type lets the backend work with mereological expressions at
-- an abstract level, independently of both the IR ('IR.MereoExpr') and the
-- final rendered string.  This makes the expression language testable in
-- isolation and gives precise structural nodes for the compiler-internal
-- abbreviations 'IsWithinBounds', 'IsIndividual', and 'ProjectIntoInterval'.
module Eidos.Pipeline.Targets.Mereological.MereoExpr
  ( -- * Expression language
    MereoExpr (..)
    -- * Rendering
  , renderMereoExpr
    -- * Abbreviation collection
  , collectUsedAbbrevNames
  ) where

import Data.List (intercalate, nub)
import qualified Eidos.Pipeline.FromSyntax.IR as IR

-- ---------------------------------------------------------------------------
-- Expression language
-- ---------------------------------------------------------------------------

-- | A mereological expression in the output format.
--
-- Variables ('MVar') already carry their final output names — name rewriting
-- from IR internal names (e.g. @\"ℙ_Min\"@ → @\"Pr_Min\"@) is done during
-- the IR→'MereoExpr' translation in 'MkAxiomSets', not during rendering.
data MereoExpr
  = MSum MereoExpr MereoExpr
    -- ^ @(a + b)@  (mereological sum / propositional conjunction)
  | MProd MereoExpr MereoExpr
    -- ^ @(a × b)@  (mereological product / propositional disjunction)
  | MDiff MereoExpr MereoExpr
    -- ^ @(a - b)@  (mereological difference / reverse implication)
  | MRevDiff MereoExpr MereoExpr
    -- ^ @(a ⇒ b)@  (reverse difference / implication)
  | MSymDiff MereoExpr MereoExpr
    -- ^ @(a ∸ b)@  (symmetric difference / biconditional)
  | MVar String
    -- ^ Atomic name (already rewritten to output form).
  | MZero
    -- ^ @0@  (lattice bottom / propositional truth)
  | MAbbrevApp String [MereoExpr]
    -- ^ Abbreviation application: @name(arg1, arg2, …)@
  | MIsWithinBounds String String String
    -- ^ @MIsWithinBounds lo var hi@ renders as @IsWithinBounds(lo, hi, var)@.
    --   All three fields are variable /names/ (already rewritten), kept as
    --   'String' because 'IsWithinBounds' is always applied to atomic names.
  | MIsIndividual String String String
    -- ^ @MIsIndividual lo var hi@ renders as @IsIndividual(lo, hi, var)@.
    --   Guards first-order (individual) quantification.
  | MBoundedSum String String String MereoExpr
    -- ^ @MBoundedSum var lo hi body@ — universal quantification over a set variable.
    --   Renders as @Σ var : 𝕌 (IsWithinBounds(lo, hi, var) ⇒ body)@.
  | MSumOfIndividuals String String String MereoExpr
    -- ^ @MSumOfIndividuals var lo hi body@ — universal quantification over an individual.
    --   Renders as @Σ var : 𝕌 (IsIndividual(lo, hi, var) ⇒ body)@.
  | MBoundedProduct String String String MereoExpr
    -- ^ @MBoundedProduct var lo hi body@ — existential quantification over a set variable.
    --   Renders as @Π var : 𝕌 (IsWithinBounds(lo, hi, var) + body)@.
  | MProductOfIndividuals String String String MereoExpr
    -- ^ @MProductOfIndividuals var lo hi body@ — existential quantification over an individual.
    --   Renders as @Π var : 𝕌 (IsIndividual(lo, hi, var) + body)@.
  | MUnboundedSum String MereoExpr
    -- ^ @MUnboundedSum var body@ — universal quantification over a set variable with no bounds guard.
    --   Renders as @Σ var : 𝕌 (body)@.
  | MProjectIntoInterval MereoExpr MereoExpr MereoExpr
    -- ^ @ProjectIntoInterval(x, lo, hi)@
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Rendering
-- ---------------------------------------------------------------------------

-- | Collect the names of compiler-internal abbreviations used anywhere in the
-- expression.  Only names present in 'IR.allAbbrevDefs' are returned, plus the
-- abbreviations implied by the structural nodes ('MIsWithinBounds',
-- 'MIsIndividual', 'MBoundedSum', 'MSumOfIndividuals', 'MBoundedProduct',
-- 'MProductOfIndividuals', 'MProjectIntoInterval').
-- The result is de-duplicated.
collectUsedAbbrevNames :: MereoExpr -> [String]
collectUsedAbbrevNames e = nub (go e)
  where
    knownAbbrevs = map IR.abbrevName IR.allAbbrevDefs

    go (MSum a b)                   = go a ++ go b
    go (MProd a b)                  = go a ++ go b
    go (MDiff a b)                  = go a ++ go b
    go (MRevDiff a b)               = go a ++ go b
    go (MSymDiff a b)               = go a ++ go b
    go (MVar _)                     = []
    go MZero                        = []
    go (MAbbrevApp n args)
      | n `elem` knownAbbrevs       = n : concatMap go args
      | otherwise                   = concatMap go args
    go (MIsWithinBounds _ _ _)      = ["IsWithinBounds"]
    go (MIsIndividual _ _ _)        = ["IsIndividual"]
    go (MBoundedSum        _ _ _ body) = "IsWithinBounds"  : go body
    go (MSumOfIndividuals  _ _ _ body) = "IsIndividual"    : go body
    go (MBoundedProduct    _ _ _ body) = "IsWithinBounds"  : go body
    go (MProductOfIndividuals _ _ _ body) = "IsIndividual" : go body
    go (MUnboundedSum _ body) = go body
    go (MProjectIntoInterval x lo hi) =
      "ProjectIntoInterval" : go x ++ go lo ++ go hi

-- | Render a 'MereoExpr' to the mereological output syntax.
renderMereoExpr :: MereoExpr -> String
renderMereoExpr = go
  where
    go (MSum a b)     = "(" ++ go a ++ " + "  ++ go b ++ ")"
    go (MProd a b)    = "(" ++ go a ++ " × "  ++ go b ++ ")"
    go (MDiff a b)    = "(" ++ go a ++ " - "  ++ go b ++ ")"
    go (MRevDiff a b) = "(" ++ go a ++ " ⇒ "  ++ go b ++ ")"
    go (MSymDiff a b) = "(" ++ go a ++ " ∸ "  ++ go b ++ ")"
    go (MVar n)       = n
    go MZero          = "0"
    go (MAbbrevApp n args) =
      n ++ "(" ++ intercalate ", " (map go args) ++ ")"
    go (MIsWithinBounds lo var hi) =
      "IsWithinBounds(" ++ lo ++ ", " ++ hi ++ ", " ++ var ++ ")"
    go (MIsIndividual lo var hi) =
      "IsIndividual(" ++ lo ++ ", " ++ hi ++ ", " ++ var ++ ")"
    go (MBoundedSum var lo hi body) =
      "Σ " ++ var ++ " : 𝕌 (" ++ go (MIsWithinBounds lo var hi) ++ " ⇒ " ++ go body ++ ")"
    go (MSumOfIndividuals var lo hi body) =
      "Σ " ++ var ++ " : 𝕌 (" ++ go (MIsIndividual lo var hi)   ++ " ⇒ " ++ go body ++ ")"
    go (MBoundedProduct var lo hi body) =
      "Π " ++ var ++ " : 𝕌 (" ++ go (MIsWithinBounds lo var hi) ++ " + " ++ go body ++ ")"
    go (MProductOfIndividuals var lo hi body) =
      "Π " ++ var ++ " : 𝕌 (" ++ go (MIsIndividual lo var hi)   ++ " + " ++ go body ++ ")"
    go (MUnboundedSum var body) =
      "Σ " ++ var ++ " : 𝕌 (" ++ go body ++ ")"
    go (MProjectIntoInterval x lo hi) =
      "ProjectIntoInterval(" ++ go x ++ ", " ++ go lo ++ ", " ++ go hi ++ ")"
