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
  , abbrevBodyToLean
  , renderAbbrevDef
  , renderLeanDoc
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

-- | Translate a 'IR.MereoExpr' to a 'LeanExpr', parameterised over a
-- name-resolution function.
--
-- Pass 'resolveName' for theory axiom bodies (theory-specific names need
-- sanitisation) or 'id' for abbreviation bodies (parameter names like
-- @"lo"@, @"hi"@ are kept verbatim).
--
-- Note: the 'IR.MAbbrevApp' @"ProjectIntoInterval"@ special case is NOT
-- included here; it is added on top by 'mereoExprToLean' so that
-- 'abbrevBodyToLean' keeps the generic 'LApp' rendering for abbreviation
-- definitions.
-- | Convert an abbreviation application to a 'LeanExpr'.
-- Receives the abbreviation name and already-translated arguments.
type AbbrevHandler = String -> [LeanExpr] -> LeanExpr

-- | Generic handler: keep every abbreviation as a plain 'LApp'.
genericAbbrev :: AbbrevHandler
genericAbbrev name args = LApp (LVar name) args

-- | Expanding handler: unfold known abbreviations into dedicated constructors.
expandingAbbrev :: AbbrevHandler
expandingAbbrev "ProjectIntoInterval" [x, lo, hi] = LProjectIntoInterval x lo hi
expandingAbbrev name args                          = LApp (LVar name) args

mereoExprToLean' :: AbbrevHandler -> (String -> String) -> IR.MereoExpr -> LeanExpr
mereoExprToLean' abbrevHandler resolve = go
  where
    go (IR.MSum a b)     = LConj   (go a) (go b)
    go (IR.MProd a b)    = LDisj   (go a) (go b)
    go (IR.MDiff a b)    = LImpl   (go b) (go a)
    go (IR.MRevDiff a b) = LImpl   (go a) (go b)
    go (IR.MSymDiff a b) = LBicond (go a) (go b)
    go (IR.MVar n)       = LVar (resolve n)
    go IR.MZero          = LTop
    go (IR.MAbbrevApp name args) =
      abbrevHandler name (map go args)
    go (IR.MBoundedSum var lo hi body) =
      case (lo, hi) of
        (IR.MVar loName, IR.MVar hiName) ->
          LBoundedForall var (resolve loName) (resolve hiName) (go body)
        _ ->
          LForallKw var LProp
               (LImpl (LApp (LVar "IsWithinBounds") [go lo, go hi, LVar var])
                          (go body))
    go (IR.MBoundedProduct var lo hi body) =
      case (lo, hi) of
        (IR.MVar loName, IR.MVar hiName) ->
          LBoundedExists var (resolve loName) (resolve hiName) (go body)
        _ ->
          LExists var LProp
               (LImpl (LApp (LVar "IsWithinBounds") [go lo, go hi, LVar var])
                          (go body))
    go (IR.MSumOfIndividuals var lo hi body) =
      case (lo, hi) of
        (IR.MVar loName, IR.MVar hiName) ->
          LForallIndividuals var (resolve loName) (resolve hiName) (go body)
        _ ->
          LForallKw var LProp
               (LImpl (LApp (LVar "IsIndividual") [go lo, go hi, LVar var])
                          (go body))
    go (IR.MProductOfIndividuals var lo hi body) =
      case (lo, hi) of
        (IR.MVar loName, IR.MVar hiName) ->
          LExistsIndividuals var (resolve loName) (resolve hiName) (go body)
        _ ->
          LExists var LProp
               (LImpl (LApp (LVar "IsIndividual") [go lo, go hi, LVar var])
                          (go body))

mereoExprToLean :: IR.MereoExpr -> LeanExpr
mereoExprToLean = mereoExprToLean' expandingAbbrev resolveName

abbrevBodyToLean :: IR.MereoExpr -> LeanExpr
abbrevBodyToLean = mereoExprToLean' genericAbbrev id

renderAbbrevDef :: IR.AbbrevDef -> String
renderAbbrevDef ad =
  "def " ++ IR.abbrevName ad
  ++ " " ++ unwords [ "(" ++ p ++ " : Prop)" | p <- IR.abbrevParams ad ]
  ++ " : Prop := " ++ renderLeanExpr (abbrevBodyToLean (IR.abbrevBody ad))

renderLeanDoc :: LeanDoc -> String
renderLeanDoc = renderLeanDocWith renderAbbrevDef