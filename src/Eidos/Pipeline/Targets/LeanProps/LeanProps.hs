-- | Export an Eidos theory to Lean 4 using the "all Props" strategy.
--
-- The pipeline has three stages:
--
--   1. 'theoryBlocks' (from 'Eidos.Pipeline.IRProcessing.MkAxiomSets') builds a
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
module Eidos.Pipeline.Targets.LeanProps.LeanProps
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
  ) where

import qualified Eidos.Pipeline.FromSyntax.IR as IR         
import           Eidos.Pipeline.IRProcessing.AxiomSet
import           Eidos.Pipeline.Targets.LeanProps.LeanExpr
import           Eidos.Pipeline.Targets.LeanProps.MkAxiomSets (theoryBlocks, axBodyToLean, mereoExprToLean)
import           Data.List (intercalate, sortOn)
import qualified Data.Set as Set

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
          axDecls = map (renderOneDecl as_) (asAxioms as_)
      in DeclBlankLine : commentDecls ++ tagDecls ++ axDecls

    -- | Render a single (name, body) pair as either a DeclDef or DeclAxiom.
    renderOneDecl as_ (name, ABDef params mereoBody) =
      DeclDef $ LeanDef name params (rewriteBounded (mereoExprToLean mereoBody))
    renderOneDecl as_ (name, body) =
      DeclAxiom (renderAxiom as_ (name, body))

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
subjectPathComment = unwords . map prettySubjectNode

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
