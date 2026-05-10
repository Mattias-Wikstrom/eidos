-- | Backend-agnostic compilation pipeline.
--
-- This module sits between the IR and any backend.  It owns the options and
-- transformations that apply regardless of the output target (Lean, Coq, …).
--
-- A backend calls 'prepareTheory' once on the top-level theory, then uses the
-- resulting 'PreparedTheory' as its input.  Recursive subtheory calls should
-- use 'prepareTheory (ptOptions pt) sub' to keep the same options in play.
module Eidos.Pipeline.InvokePipeline
  ( PipelineOptions (..)
  , defaultPipelineOptions
  , PreparedTheory (..)
  , prepareTheory
  , PipelineTarget (..)
  , TargetOptions (..)
  , defaultTargetOptions
  , invokePipeline
  ) where

import qualified Eidos.Pipeline.FromSyntax.IR as IR
import qualified Eidos.Pipeline.IRProcessing.SortBounds as SB
import qualified Eidos.Pipeline.IRProcessing.FunctionFacts as FF
import           Eidos.Pipeline.IRProcessing.AxiomSet (asPath)
import qualified Eidos.Pipeline.Targets.CoqProps.CoqProps as CoqProps
import qualified Eidos.Pipeline.Targets.CoqProps.MkAxiomSets as CoqPropsMk
import qualified Eidos.Pipeline.Targets.Lean.Lean as Lean
import qualified Eidos.Pipeline.Targets.LeanProps.LeanProps as LeanProps
import qualified Eidos.Pipeline.Targets.LeanProps.MkAxiomSets as LeanPropsMk
import           Data.List (sortOn)

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
  { ptOptions       :: PipelineOptions
  , ptTheory        :: IR.Theory
  , ptSortBounds    :: [SB.SortBoundEntry]
  , ptSortOrder     :: [SB.SortOrderEntry]
  , ptFunctionFacts :: [FF.FunctionFactEntry]
  } deriving (Show)

-- | Run all pipeline-level passes for one theory.
-- Call this once per theory (including each subtheory).
prepareTheory :: PipelineOptions -> IR.Theory -> PreparedTheory
prepareTheory opts theory = PreparedTheory
  { ptOptions       = opts
  , ptTheory        = theory
  , ptSortBounds    = SB.theorySortBoundEntries sbOpts theory
  , ptSortOrder     = SB.theorySortOrderEntries theory
  , ptFunctionFacts = FF.theoryFunctionFactEntries theory
  }
  where
    sbOpts = SB.SortBoundOptions { SB.sboCollapse = pipeCollapseSortBounds opts }

data PipelineTarget = TargetLean | TargetLeanProps | TargetCoqProps
  deriving (Show, Eq)

data TargetOptions = TargetOptions
  { toGroupByEntity          :: Bool
  , toUseSortingAxioms       :: Bool
  , toAddGroupComments       :: Bool
  , toUseBoundedForallSyntax :: Bool
  , toAddTagComments         :: Bool
  } deriving (Show, Eq)

defaultTargetOptions :: TargetOptions
defaultTargetOptions = TargetOptions
  { toGroupByEntity = False
  , toUseSortingAxioms = False
  , toAddGroupComments = False
  , toUseBoundedForallSyntax = False
  , toAddTagComments = False
  }

invokePipeline :: PipelineTarget -> TargetOptions -> IR.Theory -> String
invokePipeline target opts theory =
  case target of
    TargetLean -> Lean.exportToLean theory
    TargetLeanProps ->
      let pipeOpts = PipelineOptions { pipeCollapseSortBounds = toUseSortingAxioms opts }
          prepared = prepareTheory pipeOpts theory
          render (ns, as_) =
            let as1 = if toGroupByEntity opts then sortOn asPath as_ else as_
            in LeanProps.LeanBlock ns (LeanProps.renderAxiomSetsToDecls leanOpts as1)
          blocks = map render (LeanPropsMk.theoryBlocks prepared)
          doc = LeanProps.LeanDoc
            { LeanProps.leanDocTheoryName = IR.theoryFullyQualifiedName theory
            , LeanProps.leanDocBlocks = blocks
            }
          header =
            if toUseBoundedForallSyntax opts
            then unlines
              [ "macro \"bforall \" x:ident \" in \" lo:term \"..\" hi:term \", \" body:term : term =>"
              , "  `(forall $x : Prop, (IsWithinBounds $lo $hi $x) → $body)"
              , ""
              ]
            else ""
      in header ++ LeanProps.renderLeanDoc doc
    TargetCoqProps ->
      let pipeOpts = PipelineOptions { pipeCollapseSortBounds = toUseSortingAxioms opts }
          prepared = prepareTheory pipeOpts theory
          render (ns, as_) =
            let as1 = if toGroupByEntity opts then sortOn asPath as_ else as_
            in CoqProps.CoqBlock ns (CoqProps.renderAxiomSetsToDecls coqOpts as1)
          blocks = map render (CoqPropsMk.theoryBlocks prepared)
          doc = CoqProps.CoqDoc
            { CoqProps.coqDocTheoryName = IR.theoryFullyQualifiedName theory
            , CoqProps.coqDocBlocks = blocks
            }
      in CoqProps.renderCoqDoc doc
  where
    leanOpts = LeanProps.defaultLeanPropsOptions
      { LeanProps.optGroupByEntity = toGroupByEntity opts
      , LeanProps.optUseSortingAxioms = toUseSortingAxioms opts
      , LeanProps.optAddGroupComments = toAddGroupComments opts
      , LeanProps.optUseBoundedForallSyntax = toUseBoundedForallSyntax opts
      , LeanProps.optAddTagComments = toAddTagComments opts
      }
    coqOpts = CoqProps.defaultCoqPropsOptions
      { CoqProps.optGroupByEntity = toGroupByEntity opts
      , CoqProps.optUseSortingAxioms = toUseSortingAxioms opts
      , CoqProps.optAddGroupComments = toAddGroupComments opts
      , CoqProps.optAddTagComments = toAddTagComments opts
      }
