-- | Export an Eidos theory to Coq using the "all Props" strategy.
--
-- Mirrors 'Eidos.Pipeline.Targets.LeanProps.LeanProps' for Coq output.
--
-- The pipeline has three stages:
--
--   1. 'theoryBlocks' builds a normalized list of tagged 'AxiomSet' values.
--
--   2. 'renderAxiomSetsToDecls' maps those sets to 'CoqDecl' values (with
--      optional grouping/sorting controlled by 'CoqPropsOptions').
--
--   3. 'renderCoqDoc' pretty-prints the resulting 'CoqDoc' to Coq source.
--
-- == Encoding conventions
--
-- * @→@ renders as @->@; @∧@ as @/\@; @∨@ as @\/@; @↔@ as @<->@.
-- * Subtheory scopes use flat @Module@\/@End@ blocks (dots in FQNs become @_@).
-- * Assertions are wrapped with @ℙ_Min@; metafacts with @𝕌_Min@.
module Eidos.Pipeline.Targets.CoqProps.CoqProps
  ( -- * Internal representation (re-exported from CoqExpr)
    CoqDoc (..)
  , CoqBlock (..)
  , CoqDecl (..)
  , CoqAxiom (..)
  , CoqExpr (..)
    -- * Pipeline stages
  , renderCoqDoc
  , renderCoqExpr
  , renderAxiomSetsToDecls
    -- * Convenience entry point
  , CoqPropsOptions (..)
  , defaultCoqPropsOptions
  ) where

import           Eidos.Pipeline.IRProcessing.AxiomSet
import           Eidos.Pipeline.Targets.CoqProps.CoqExpr
import           Eidos.Pipeline.Targets.CoqProps.MkAxiomSets (axBodyToCoq)
import           Data.List (intercalate)
import qualified Data.Set as Set

renderAxiomSetsToDecls :: CoqPropsOptions -> [AxiomSet] -> [CoqDecl]
renderAxiomSetsToDecls opts = concatMap renderOne
  where
    renderOne as_ =
      let commentDecls = [ DeclComment (subjectPathComment (asPath as_)) | optAddGroupComments opts ]
          tagDecls     = [ DeclComment (tagSetComment (asTags as_))      | optAddTagComments opts ]
          axDecls      = map (DeclAxiom . renderAxiom) (asAxioms as_)
      in DeclBlankLine : commentDecls ++ tagDecls ++ axDecls

    renderAxiom (name, body) = CoqAxiom name (axBodyToCoq body)

subjectPathComment :: SubjectPath -> String
subjectPathComment = unwords . map prettySubjectNode

data CoqPropsOptions = CoqPropsOptions
  { optGroupByEntity    :: Bool
  , optUseSortingAxioms :: Bool
  , optAddGroupComments :: Bool
  , optAddTagComments   :: Bool
  } deriving (Eq, Show)

defaultCoqPropsOptions :: CoqPropsOptions
defaultCoqPropsOptions = CoqPropsOptions
  { optGroupByEntity    = False
  , optUseSortingAxioms = False
  , optAddGroupComments = False
  , optAddTagComments   = False
  }

tagSetComment :: TagSet -> String
tagSetComment ts = "tags: " ++ intercalate ", " (map show (Set.toAscList ts))
