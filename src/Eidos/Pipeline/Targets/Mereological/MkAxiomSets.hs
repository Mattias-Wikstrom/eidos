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

import           Data.Char (isLower)
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
-- the special-var rules for built-in bound names (e.g. @\"ℙ_Min\"@).
rewriteVar :: NameMap -> String -> String
rewriteVar nm n = case Map.lookup n nm of
  Just out -> out
  Nothing  -> rewriteSpecialVar n

-- | Rewrite built-in and sort-bound special variable names to output form.
--
-- The built-in sort limits are mapped to their ASCII output names:
--   @𝕌_Min@ → @Univ_Min@, @𝕌_Max@ → @Univ_Max@,
--   @ℙ_Min@ → @Pr_Min@,   @ℙ_Max@ → @Pr_Max@,
--   @𝔻_Min@ → @Dom_Min@,  @𝔻_Max@ → @Dom_Max@.
-- User-sort limits (e.g. @MySort_Min@) start with an uppercase letter and
-- fall through to the identity case.
--
-- Unrecognised names that start with a lowercase ASCII letter AND contain no
-- underscores are prefixed with @Var_@ (e.g. @x@ → @Var_x@) to satisfy the
-- Eidos syntax requirement that object names begin with an uppercase letter.
-- Names that contain underscores (e.g. function-domain sort limits like
-- @f_dom_Min@) pass through unchanged since they are already in output form.
rewriteSpecialVar :: String -> String
rewriteSpecialVar n = case n of
  "𝕌_Min" -> "Univ_Min"
  "𝕌_Max" -> "Univ_Max"
  "ℙ_Min" -> "Pr_Min"
  "ℙ_Max" -> "Pr_Max"
  "𝔻_Min" -> "Dom_Min"
  "𝔻_Max" -> "Dom_Max"
  (c:_) | isLower c, '_' `notElem` n -> "Var_" ++ n
  _ -> n

-- ---------------------------------------------------------------------------
-- Quantifier constructor selector
-- ---------------------------------------------------------------------------

-- | Select the appropriate 'MereoExpr' bounded-quantifier constructor based on
-- the @isExists@ and @isIndividual@ flags from 'IR.MBoundedSum'.
mkBoundedQuantifier
  :: Bool   -- ^ isExists
  -> Bool   -- ^ isIndividual
  -> String -> String -> String -> MereoExpr -> MereoExpr
mkBoundedQuantifier False False = MBoundedSum
mkBoundedQuantifier False True  = MSumOfIndividuals
mkBoundedQuantifier True  False = MBoundedProduct
mkBoundedQuantifier True  True  = MProductOfIndividuals

-- ---------------------------------------------------------------------------
-- IR.MereoExpr → MereoExpr
-- ---------------------------------------------------------------------------

-- | Translate an 'IR.MereoExpr' to a 'MereoExpr', rewriting entity and
-- special-variable names via the supplied 'NameMap'.
--
-- Mereological operations pass through unchanged.  The special cases are:
--
-- * 'IR.MBoundedSum': the @isExists@ and @isIndividual@ flags select one of
--   'MBoundedSum', 'MSumOfIndividuals', 'MBoundedProduct', or
--   'MProductOfIndividuals'.  When lo and hi are both simple 'IR.MVar' nodes
--   names are kept as strings; otherwise lo\/hi are rendered eagerly as a
--   string fallback.  (Complex lo\/hi are not expected in practice.)
--
-- * Lowercase bound-variable names (individuals) are automatically prefixed
--   with @Var_@ via 'rewriteSpecialVar' so the output is valid Eidos syntax.
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
    go (IR.MBoundedSum isEx isInd var lo hi body) =
      let var'  = rewriteSpecialVar var  -- applies Var_ prefix for lowercase names
          mk    = mkBoundedQuantifier isEx isInd
          body' = go body
      in case (lo, hi) of
        (IR.MVar loName, IR.MVar hiName) ->
          mk var' (rewriteVar nm loName) (rewriteVar nm hiName) body'
        _ ->
          mk var' (renderMereoExpr (go lo)) (renderMereoExpr (go hi)) body'

-- | Translate an 'IR.MereoExpr' that is the body of a compiler-internal
-- abbreviation definition.  No entity-name rewriting is needed — the body
-- contains only abbreviation parameter names and special vars.
abbrevBodyToMereo :: IR.MereoExpr -> MereoExpr
abbrevBodyToMereo = irMereoExprToMereo Map.empty
