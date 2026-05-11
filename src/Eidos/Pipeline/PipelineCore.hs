module Eidos.Pipeline.PipelineCore
  ( PipelineOptions (..)
  , defaultPipelineOptions
  , PreparedTheory (..)
  , prepareTheory
  ) where

import qualified Eidos.Pipeline.FromSyntax.IR as IR
import qualified Eidos.Pipeline.IRProcessing.SortBounds as SB
import qualified Eidos.Pipeline.IRProcessing.FunctionFacts as FF
import qualified Eidos.Pipeline.IRProcessing.MereologicalOpDefs as MOD

data PipelineOptions = PipelineOptions
  { pipeCollapseSortBounds :: Bool
  } deriving (Show, Eq)

defaultPipelineOptions :: PipelineOptions
defaultPipelineOptions = PipelineOptions
  { pipeCollapseSortBounds = False
  }

data PreparedTheory = PreparedTheory
  { ptOptions       :: PipelineOptions
  , ptTheory        :: IR.Theory
  , ptSortBounds    :: [SB.SortBoundEntry]
  , ptSortOrder     :: [SB.SortOrderEntry]
  , ptFunctionFacts :: [FF.FunctionFactEntry]
  , ptMereologicalOpDefs :: [MOD.MereoOpDefEntry]
  } deriving (Show)

prepareTheory :: PipelineOptions -> IR.Theory -> PreparedTheory
prepareTheory opts theory = PreparedTheory
  { ptOptions       = opts
  , ptTheory        = theory
  , ptSortBounds    = SB.theorySortBoundEntries sbOpts theory
  , ptSortOrder     = SB.theorySortOrderEntries theory
  , ptFunctionFacts = FF.theoryFunctionFactEntries theory
  , ptMereologicalOpDefs = MOD.theoryMereoOpDefEntries theory
  }
  where
    sbOpts = SB.SortBoundOptions { SB.sboCollapse = pipeCollapseSortBounds opts }
