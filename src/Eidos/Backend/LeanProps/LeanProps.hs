-- | Export an Eidos theory to Lean 4 using the "all Props" strategy.
--
-- The pipeline has three stages:
--
--   1. 'theoryBlocks' (from 'Eidos.Pipeline.MkAxiomSets') builds a
--      normalized list of tagged 'AxiomSet' values from the 'IR.Theory'.
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
module Eidos.Backend.LeanProps.LeanProps
  ( -- * Internal representation (re-exported from Eidos.Export.LeanExpr)
    LeanDoc (..)
  , LeanBlock (..)
  , LeanDecl (..)
  , LeanAxiom (..)
  , LeanExpr (..)
    -- * Pipeline stages
  , renderLeanDoc
  , renderLeanExpr
  , renderAxiomSetsToDecls
    -- * Convenience entry point
  , LeanPropsOptions (..)
  , defaultLeanPropsOptions
  , exportToLeanPropsWithOptions
  , exportToLeanProps
  ) where

import qualified Eidos.IR as IR
import qualified Eidos.Pipeline as PL
import           Eidos.Pipeline.AxiomSet
import           Eidos.Backend.LeanProps.LeanExpr
import           Eidos.Backend.LeanProps.MkAxiomSets (theoryBlocks, axBodyToLean)
import           Data.List (intercalate, sortOn)
import qualified Data.Set as Set

-- ---------------------------------------------------------------------------
-- Convenience entry point
-- ---------------------------------------------------------------------------

-- | Convert an Eidos theory directly to Lean 4 source (combines all stages).
exportToLeanPropsWithOptions :: LeanPropsOptions -> IR.Theory -> String
exportToLeanPropsWithOptions opts theory =
  let pipeOpts = PL.PipelineOptions { PL.pipeCollapseSortBounds = optUseSortingAxioms opts }
      prepared = PL.prepareTheory pipeOpts theory
      render (ns, as_) =
        let as1 = if optGroupByEntity opts then sortOn asPath as_ else as_
        in LeanBlock ns (renderAxiomSetsToDecls opts as1)
      blocks = map render (theoryBlocks prepared)
      doc = LeanDoc
        { leanDocTheoryName = IR.theoryFullyQualifiedName theory
        , leanDocBlocks     = blocks
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
          axDecls = map (DeclAxiom . renderAxiom as_) (asAxioms as_)
      in DeclBlankLine : commentDecls ++ tagDecls ++ axDecls

    renderAxiom as_ (name, body) =
      let lean      = axBodyToLean body
          rewritten = rewriteBounded lean
      in LeanAxiom name rewritten

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
    rewriteBounded x = x

subjectPathComment :: SubjectPath -> String
subjectPathComment = unwords . map show

data LeanPropsOptions = LeanPropsOptions
  { optGroupByEntity          :: Bool
  , optUseSortingAxioms       :: Bool
  , optAddGroupComments       :: Bool
  , optUseBoundedForallSyntax :: Bool
  , optAddTagComments         :: Bool
  } deriving (Eq, Show)

defaultLeanPropsOptions :: LeanPropsOptions
defaultLeanPropsOptions = LeanPropsOptions
  { optGroupByEntity          = False
  , optUseSortingAxioms       = False
  , optAddGroupComments       = False
  , optUseBoundedForallSyntax = False
  , optAddTagComments         = False
  }

tagSetComment :: TagSet -> String
tagSetComment ts = "tags: " ++ intercalate ", " (map show (Set.toAscList ts))
