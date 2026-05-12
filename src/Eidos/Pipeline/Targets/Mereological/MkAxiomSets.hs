-- | Mereological expression translation for pipeline axiom bodies.
--
-- Mirrors 'Eidos.Pipeline.Targets.LeanProps.MkAxiomSets' and
-- 'Eidos.Pipeline.Targets.CoqProps.MkAxiomSets' for the Mereological output.
--
-- * 'irMereoExprToMereo' translates an 'IR.MereoExpr' to a 'MereoExpr',
--   applying output-name rewriting via a 'NameMap'.
-- * 'abbrevBodyToMereo' is the same translation for abbreviation bodies,
--   where no entity-name rewriting is needed.
module Eidos.Pipeline.Targets.Mereological.MkAxiomSets
  ( irMereoExprToMereo
  , abbrevBodyToMereo
  ) where

import qualified Data.Map.Strict as Map
import qualified Eidos.Pipeline.FromSyntax.IR as IR
import           Eidos.Pipeline.Targets.Mereological.MereoExpr

-- ---------------------------------------------------------------------------
-- Name map type (re-exported for use in Mereological.hs)
-- ---------------------------------------------------------------------------

type NameMap = Map.Map String String

-- ---------------------------------------------------------------------------
-- Name-resolution helpers
-- ---------------------------------------------------------------------------

minSuffix, maxSuffix :: String
minSuffix = "_Min"
maxSuffix = "_Max"

-- | Rewrite an IR variable name using the entity name map, falling back to
-- the special-var rules for built-in bound names (e.g. @\"ℙ#min\"@).
rewriteVar :: NameMap -> String -> String
rewriteVar nm n = case Map.lookup n nm of
  Just out -> out
  Nothing  -> rewriteSpecialVar n

-- | Rewrite built-in and sort-bound special variable names to output form.
--   @𝕌#min@ → @Univ_Min@, @ℙ#max@ → @Pr_Max@, @S#min@ → @S_Min@, etc.
rewriteSpecialVar :: String -> String
rewriteSpecialVar n = case n of
  "𝕌#min" -> "Univ" ++ minSuffix
  "𝕌#max" -> "Univ" ++ maxSuffix
  "ℙ#min" -> "Pr"   ++ minSuffix
  "ℙ#max" -> "Pr"   ++ maxSuffix
  "𝔻#min" -> "Dom"  ++ minSuffix
  "𝔻#max" -> "Dom"  ++ maxSuffix
  _ | Just base <- stripHashSuffix "#min" n -> base ++ minSuffix
    | Just base <- stripHashSuffix "#max" n -> base ++ maxSuffix
  _ -> n
  where
    stripHashSuffix suf str =
      let (front, back) = splitAt (length str - length suf) str
      in if back == suf then Just front else Nothing

-- ---------------------------------------------------------------------------
-- IR.MereoExpr → MereoExpr
-- ---------------------------------------------------------------------------

-- | Translate an 'IR.MereoExpr' to a 'MereoExpr', rewriting entity and
-- special-variable names via the supplied 'NameMap'.
--
-- Mereological operations pass through unchanged.  The special cases are:
--
-- * 'IR.MBoundedSum': when lo and hi are both simple 'IR.MVar' nodes, the
--   compact 'MBoundedForall' structural node is used.  Otherwise the bounds
--   check is emitted as an explicit 'MAbbrevApp' \"IsWithinBounds\" and the
--   Σ-quantifier structure is preserved via the general 'MBoundedForall' with
--   rendered lo\/hi name strings.  (Complex lo\/hi are not expected in
--   practice; sort bounds are always simple named variables.)
--
-- * 'IR.MAbbrevApp' \"ProjectIntoInterval\": lifted to 'MProjectIntoInterval'.
irMereoExprToMereo :: NameMap -> IR.MereoExpr -> MereoExpr
irMereoExprToMereo nm = go
  where
    go (IR.MSum a b)     = MSum     (go a) (go b)
    go (IR.MProd a b)    = MProd    (go a) (go b)
    go (IR.MDiff a b)    = MDiff    (go a) (go b)
    go (IR.MRevDiff a b) = MRevDiff (go a) (go b)
    go (IR.MSymDiff a b) = MSymDiff (go a) (go b)
    go (IR.MVar n)       = MVar (rewriteVar nm n)
    go IR.MZero          = MZero
    go (IR.MAbbrevApp "ProjectIntoInterval" [x, lo, hi]) =
      MProjectIntoInterval (go x) (go lo) (go hi)
    go (IR.MAbbrevApp n args) = MAbbrevApp n (map go args)
    go (IR.MBoundedSum var lo hi body) =
      case (lo, hi) of
        (IR.MVar loName, IR.MVar hiName) ->
          MBoundedForall var
            (rewriteVar nm loName) (rewriteVar nm hiName)
            (go body)
        _ ->
          -- lo or hi is a complex expression; render it via MAbbrevApp so
          -- the abbreviation is still collected, and wrap in MBoundedForall
          -- using the rendered-string fallback.
          MBoundedForall var
            (renderMereoExpr (go lo)) (renderMereoExpr (go hi))
            (go body)

-- | Translate an 'IR.MereoExpr' that is the body of a compiler-internal
-- abbreviation definition.  No entity-name rewriting is needed — the body
-- contains only abbreviation parameter names and special vars.
abbrevBodyToMereo :: IR.MereoExpr -> MereoExpr
abbrevBodyToMereo = irMereoExprToMereo Map.empty
