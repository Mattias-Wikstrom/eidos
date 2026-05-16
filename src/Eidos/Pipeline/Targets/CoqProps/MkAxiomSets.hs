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
  , abbrevBodyToCoq
  , renderAbbrevDef
  , renderCoqDoc
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
      | isAlphaNum c || c `elem` "_'." = [c]
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

-- | Translate a 'IR.MereoExpr' to a 'CoqExpr', parameterised over a
-- name-resolution function.
--
-- Pass 'resolveName' for theory axiom bodies (theory-specific names need
-- sanitisation) or 'id' for abbreviation bodies (parameter names like
-- @"lo"@, @"hi"@ are kept verbatim).
type CoqAbbrevHandler = String -> [CoqExpr] -> CoqExpr

genericCoqAbbrev :: CoqAbbrevHandler
genericCoqAbbrev name args = CApp (CVar name) args

expandingCoqAbbrev :: CoqAbbrevHandler
expandingCoqAbbrev "ProjectIntoInterval" [x, lo, hi] = CProjectIntoInterval x lo hi
expandingCoqAbbrev name args                          = CApp (CVar name) args

mereoExprToCoq' :: CoqAbbrevHandler -> (String -> String) -> IR.MereoExpr -> CoqExpr
mereoExprToCoq' abbrevHandler resolve = go
  where
    go (IR.MSum a b)     = CConj   (go a) (go b)
    go (IR.MProd a b)    = CDisj   (go a) (go b)
    go (IR.MDiff a b)    = CImpl   (go b) (go a)
    go (IR.MRevDiff a b) = CImpl   (go a) (go b)
    go (IR.MSymDiff a b) = CBicond (go a) (go b)
    go (IR.MVar n)       = CVar (resolve n)
    go IR.MZero          = CTop
    go (IR.MAbbrevApp name args) =
      abbrevHandler name (map go args)
    go (IR.MFOLApp name args) =
      CApp (CVar (resolve name)) (map go args)
    go (IR.MProductOfIndividuals var lo hi body) =
      case (lo, hi) of
        (IR.MVar loName, IR.MVar hiName) ->
          CExistsIndividuals var (resolve loName) (resolve hiName) (go body)
        _ ->
          CExists var CProp
               (CConj (CApp (CVar "IsIndividual") [go lo, go hi, CVar var])
                      (go body))
    go (IR.MBoundedSum var lo hi body) =
      case (lo, hi) of
        (IR.MVar loName, IR.MVar hiName) ->
          CBoundedForall var (resolve loName) (resolve hiName) (go body)
        _ ->
          CForall var CProp
               (CImpl (CApp (CVar "IsWithinBounds") [go lo, go hi, CVar var])
                      (go body))
    go (IR.MSumOfIndividuals var lo hi body) =
      case (lo, hi) of
        (IR.MVar loName, IR.MVar hiName) ->
          CForallIndividuals var (resolve loName) (resolve hiName) (go body)
        _ ->
          CForall var CProp
               (CImpl (CApp (CVar "IsIndividual") [go lo, go hi, CVar var])
                      (go body))
    go (IR.MBoundedProduct var lo hi body) =
      case (lo, hi) of
        (IR.MVar loName, IR.MVar hiName) ->
          CBoundedExists var (resolve loName) (resolve hiName) (go body)
        _ ->
          CExists var CProp
               (CConj (CApp (CVar "IsWithinBounds") [go lo, go hi, CVar var])
                      (go body))

mereoExprToCoq :: IR.MereoExpr -> CoqExpr
mereoExprToCoq = mereoExprToCoq' expandingCoqAbbrev resolveName

abbrevBodyToCoq :: IR.MereoExpr -> CoqExpr
abbrevBodyToCoq = mereoExprToCoq' genericCoqAbbrev id

renderAbbrevDef :: IR.AbbrevDef -> String
renderAbbrevDef ad =
  "Definition " ++ IR.abbrevName ad
  ++ " " ++ unwords [ "(" ++ p ++ " : Prop)" | p <- IR.abbrevParams ad ]
  ++ " : Prop := " ++ renderCoqExpr (abbrevBodyToCoq (IR.abbrevBody ad)) ++ "."

renderCoqDoc :: CoqDoc -> String
renderCoqDoc = renderCoqDocWith renderAbbrevDef
