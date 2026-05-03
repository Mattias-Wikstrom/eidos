-- | Export an Eidos theory to Lean 4 using the "all Props" strategy.
--
-- The pipeline has three stages:
--
--   1. 'mkAxiomSets' (from 'Eidos.Export.MkAxiomSets') builds a normalized
--      list of tagged 'AxiomSet' values from the 'IR.Theory'.
--
--   2. 'renderAxiomSetsToDecls' maps those sets to 'LeanDecl' values (with
--      optional grouping/sorting rewrites controlled by 'LeanPropsOptions').
--
--   3. 'renderLeanDoc' pretty-prints the resulting 'LeanDoc' to Lean 4 source.
--
-- == Encoding conventions
--
-- * A 𝕌-kinded object @P@ gets bounds axioms @P → U_Min@ and @U_Max → P@.
-- * A ℙ-kinded object @P@ gets bounds axioms @P → P_Min@ and @P_Max → P@.
-- * A 𝔻-kinded set @S@ gets bounds axioms @S → D_Min@ and @D_Max → S@.
-- * A user-sort set @S ⊆ T@ gets bounds axioms @S → T_Min@ and @T_Max → S@.
-- * @A - B@ (mereological difference) renders as @B → A@.
-- * @+, ×, ∸@ map to @∧, ∨, ↔@.
-- * Assertions are wrapped with @P_Min@; metafacts with @U_Min@.
module Eidos.Export.LeanProps
  ( -- * Internal representation (re-exported from Eidos.Export.LeanExpr)
    LeanDoc (..)
  , LeanDecl (..)
  , LeanAxiom (..)
  , LeanExpr (..)
    -- * Pipeline stages
  , theoryToLeanDoc
  , renderLeanDoc
  , renderLeanExpr
    -- * Convenience entry point
  , LeanPropsOptions (..)
  , defaultLeanPropsOptions
  , exportToLeanPropsWithOptions
  , exportToLeanProps
  ) where

import qualified Eidos.IR as IR
import Eidos.Export.LeanExpr
import Data.List (intercalate, sortOn)
import qualified Data.Set as Set
import Eidos.Export.MkAxiomSets (mkAxiomSets)
import Eidos.Export.LeanAxiomSet

-- ---------------------------------------------------------------------------
-- Stage 1 – Theory → LeanDoc
-- ---------------------------------------------------------------------------

-- | Convert an Eidos 'IR.Theory' into a structured 'LeanDoc'.
theoryToLeanDoc :: IR.Theory -> LeanDoc
theoryToLeanDoc theory =
  let axiomSets = mkAxiomSets theory
  in LeanDoc
      { leanDocTheoryName = IR.theoryFullyQualifiedName theory
      , leanDocDecls = renderAxiomSetsToDecls defaultLeanPropsOptions axiomSets
      }

-- ---------------------------------------------------------------------------
-- Convenience entry point
-- ---------------------------------------------------------------------------

-- | Convert an Eidos theory directly to Lean 4 source (combines both stages).
exportToLeanPropsWithOptions :: LeanPropsOptions -> IR.Theory -> String
exportToLeanPropsWithOptions opts theory =
  let axiomSets0 = mkAxiomSets theory
      axiomSets1 = if optUseSortingAxioms opts
                   then map collapseSortingSet axiomSets0
                   else axiomSets0
      axiomSets2 = if optGroupByEntity opts then sortOn asPath axiomSets1 else axiomSets1
      doc = LeanDoc
        { leanDocTheoryName = IR.theoryFullyQualifiedName theory
        , leanDocDecls = renderAxiomSetsToDecls opts axiomSets2
        }
      header =
        if optUseBoundedForallSyntax opts
        then unlines
          [ "macro \"bforall \" x:ident \" in \" lo:term \"..\" hi:term \", \" body:term : term =>"
          , "  `(forall $x : Prop, (IsWithinBounds $lo $hi $x) → $body)"
          , ""
          ]
        else ""
  in header ++ renderLeanDoc doc

exportToLeanProps :: IR.Theory -> String
exportToLeanProps = exportToLeanPropsWithOptions defaultLeanPropsOptions

renderAxiomSetsToDecls :: LeanPropsOptions -> [AxiomSet] -> [LeanDecl]
renderAxiomSetsToDecls opts = concatMap renderOne
  where
    renderOne as_ =
      let commentDecls = if optAddGroupComments opts
                         then [DeclComment (subjectPathComment (asPath as_))]
                         else []
          tagDecls = if optAddTagComments opts
                     then [DeclComment (tagSetComment (asTags as_))]
                     else []
          axDecls = map (DeclAxiom . mapAxiom) (asAxioms as_)
      in DeclBlankLine : commentDecls ++ tagDecls ++ axDecls

    mapAxiom ax = ax { axiomType = rewriteBounded (axiomType ax) }

    rewriteBounded (LBoundedForall var lo hi body)
      | optUseBoundedForallSyntax opts =
          LApp (LVar "bforall")
            [ LVar var, LVar lo, LVar hi, rewriteBounded body ]
      | otherwise = LBoundedForall var lo hi (rewriteBounded body)
    rewriteBounded (LImpl a b) = LImpl (rewriteBounded a) (rewriteBounded b)
    rewriteBounded (LConj a b) = LConj (rewriteBounded a) (rewriteBounded b)
    rewriteBounded (LDisj a b) = LDisj (rewriteBounded a) (rewriteBounded b)
    rewriteBounded (LBicond a b) = LBicond (rewriteBounded a) (rewriteBounded b)
    rewriteBounded (LForall x ty b) = LForall x (rewriteBounded ty) (rewriteBounded b)
    rewriteBounded (LForallKw x ty b) = LForallKw x (rewriteBounded ty) (rewriteBounded b)
    rewriteBounded (LExists x ty b) = LExists x (rewriteBounded ty) (rewriteBounded b)
    rewriteBounded (LEq a b) = LEq (rewriteBounded a) (rewriteBounded b)
    rewriteBounded (LApp f args) = LApp (rewriteBounded f) (map rewriteBounded args)
    rewriteBounded (LProjectIntoInterval x lo hi) =
      LProjectIntoInterval (rewriteBounded x) (rewriteBounded lo) (rewriteBounded hi)
    rewriteBounded x = x  -- LVar, LIsWithinBounds, LIsIndividual, LProp are leaves

subjectPathComment :: SubjectPath -> String
subjectPathComment = unwords . map show

collapseSortingSet :: AxiomSet -> AxiomSet
collapseSortingSet as_
  | not (hasTag TagSorting as_) = as_
  | otherwise =
      case asAxioms as_ of
        [LeanAxiom nMin (LImpl _ (LImpl (LVar obj1) (LVar lo))),
         LeanAxiom nMax (LImpl _ (LImpl (LVar hi) (LVar obj2)))]
          | obj1 == obj2
          , stripSuffix "_min" nMin == Just obj1
          , stripSuffix "_max" nMax == Just obj1
          -> as_ { asAxioms = [LeanAxiom (obj1 ++ "_sorting") (LIsWithinBounds lo obj1 hi)] }
        [LeanAxiom nMin (LImpl (LVar obj1) (LVar lo)),
         LeanAxiom nMax (LImpl (LVar hi) (LVar obj2))]
          | obj1 == obj2
          , stripSuffix "_min" nMin == Just obj1
          , stripSuffix "_max" nMax == Just obj1
          -> as_ { asAxioms = [LeanAxiom (obj1 ++ "_sorting") (LIsWithinBounds lo obj1 hi)] }
        _ -> as_
  where
    stripSuffix suffix str =
      let n = length str - length suffix
      in if n >= 0 && drop n str == suffix then Just (take n str) else Nothing
data LeanPropsOptions = LeanPropsOptions
  { optGroupByEntity      :: Bool
  , optUseSortingAxioms   :: Bool
  , optAddGroupComments   :: Bool
  , optUseBoundedForallSyntax :: Bool
  , optAddTagComments      :: Bool
  } deriving (Eq, Show)

defaultLeanPropsOptions :: LeanPropsOptions
defaultLeanPropsOptions = LeanPropsOptions
  { optGroupByEntity = False
  , optUseSortingAxioms = False
  , optAddGroupComments = False
  , optUseBoundedForallSyntax = False
  , optAddTagComments = False
  }


tagSetComment :: TagSet -> String
tagSetComment ts = "tags: " ++ intercalate ", " (map show (Set.toAscList ts))
