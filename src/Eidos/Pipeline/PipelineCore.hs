module Eidos.Pipeline.PipelineCore
  ( PipelineOptions (..)
  , defaultPipelineOptions
  , PreparedTheory (..)
  , prepareTheory
  ) where

import qualified Eidos.Pipeline.FromSyntax.IR as IR
import qualified Eidos.Pipeline.IRProcessing.FunctionFacts as FF
import qualified Eidos.Pipeline.IRProcessing.MereologicalOpDefs as MOD

data PipelineOptions = PipelineOptions
  { pipeCollapseSortBounds :: Bool
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
-- the pipeline-level transformations are performed exactly once, outside the backend.
data PreparedTheory = PreparedTheory
  { ptOptions            :: PipelineOptions
  , ptTheory             :: IR.Theory
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
  , ptFunctionFacts      = FF.theoryFunctionFactEntries theory
  , ptMereologicalOpDefs = MOD.theoryMereoOpDefEntries theory
  , ptUserAbbrevDefs     = IR.theoryUserAbbrevDefs theory
  }
