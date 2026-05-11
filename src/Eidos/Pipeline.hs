-- | Backend-agnostic compilation pipeline.
--
-- This module sits between the IR and any backend.  It owns the options and
-- transformations that apply regardless of the output target (Lean, Coq, …).
--
-- A backend calls 'prepareTheory' once on the top-level theory, then uses the
-- resulting 'PreparedTheory' as its input.  Recursive subtheory calls should
-- use 'prepareTheory (ptOptions pt) sub' to keep the same options in play.
module Eidos.Pipeline
  ( PipelineOptions (..)
  , defaultPipelineOptions
  , PreparedTheory (..)
  , prepareTheory
  ) where

import qualified Eidos.IR as IR
import qualified Eidos.Pipeline.SortBounds as SB
import qualified Eidos.Pipeline.FunctionFacts as FF
import qualified Eidos.Pipeline.MereologicalOpDefs as MOD

-- ---------------------------------------------------------------------------
-- Options
-- ---------------------------------------------------------------------------

-- | Options that apply across all backends.
data PipelineOptions = PipelineOptions
  { pipeCollapseSortBounds :: Bool
    -- ^ Collapse each pair of sort-bound axioms into a single
    --   @IsWithinBounds lo obj hi@ axiom (--sorting-axioms).
    --   'False' (default): emit separate @_min@ / @_max@ implications.
  } deriving (Show, Eq)

defaultPipelineOptions :: PipelineOptions
defaultPipelineOptions = PipelineOptions
  { pipeCollapseSortBounds = False
  }

-- ---------------------------------------------------------------------------
-- PreparedTheory
-- ---------------------------------------------------------------------------

-- | A theory together with all pre-computed, backend-agnostic derived data.
--
-- Backends receive a 'PreparedTheory' rather than a raw 'IR.Theory' so that
-- the pipeline-level transformations (sort-bound computation, future passes)
-- are performed exactly once, outside the backend.
data PreparedTheory = PreparedTheory
  { ptOptions            :: PipelineOptions
  , ptTheory             :: IR.Theory
  , ptSortBounds         :: [SB.SortBoundEntry]
  , ptSortOrder          :: [SB.SortOrderEntry]
  , ptFunctionFacts      :: [FF.FunctionFactEntry]
  , ptMereologicalOpDefs :: [MOD.MereoOpDefEntry]
    -- ^ Per-theory definitions of +, ×, −, ⇒, ∸ relativized to the
    --   theory's universe.  Backends emit these as @def@\/@Definition@.
  , ptUserAbbrevDefs :: [IR.AbbrevDef]
    -- ^ User-defined abbreviations from @abbreviations { }@ sections.
    --   Backends emit these as @def@\/@Definition@.
  } deriving (Show)

-- | Run all pipeline-level passes for one theory.
-- Call this once per theory (including each subtheory).
prepareTheory :: PipelineOptions -> IR.Theory -> PreparedTheory
prepareTheory opts theory = PreparedTheory
  { ptOptions            = opts
  , ptTheory             = theory
  , ptSortBounds         = SB.theorySortBoundEntries sbOpts theory
  , ptSortOrder          = SB.theorySortOrderEntries theory
  , ptFunctionFacts      = FF.theoryFunctionFactEntries theory
  , ptMereologicalOpDefs = MOD.theoryMereoOpDefEntries theory
  , ptUserAbbrevDefs     = IR.theoryUserAbbrevDefs theory
  }
  where
    sbOpts = SB.SortBoundOptions { SB.sboCollapse = pipeCollapseSortBounds opts }
