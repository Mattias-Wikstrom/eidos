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
import           Eidos.Pipeline.PipelineCore
import           Eidos.Pipeline.IRProcessing.AxiomSet (asPath)
import qualified Eidos.Pipeline.Targets.CoqProps.CoqProps as CoqProps
import qualified Eidos.Pipeline.Targets.CoqProps.MkAxiomSets as CoqPropsMk
import qualified Eidos.Pipeline.Targets.Lean.Lean as Lean
import qualified Eidos.Pipeline.Targets.LeanProps.LeanProps as LeanProps
import qualified Eidos.Pipeline.Targets.LeanProps.MkAxiomSets as LeanPropsMk
import qualified Eidos.Pipeline.Targets.Mereological.Mereological as Mereological
import           Data.List (intercalate, sortOn)

data PipelineTarget = TargetLean | TargetLeanProps | TargetCoqProps | TargetMereological
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
            in (ns, CoqProps.renderAxiomSetsToDecls coqOpts as1)
          flatBlocks = map render (CoqPropsMk.theoryBlocks prepared)
          doc = CoqProps.CoqDoc
            { CoqProps.coqDocTheoryName = IR.theoryFullyQualifiedName theory
            , CoqProps.coqDocBlocks = nestCoqBlocks flatBlocks
            }
      in CoqProps.renderCoqDoc doc
    TargetMereological ->
      let prepared = prepareTheory defaultPipelineOptions theory
      in Mereological.exportToMereological prepared
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

-- | Convert a flat post-ordered list of @(fqn, decls)@ pairs into a nested
-- 'CoqProps.CoqBlock' tree.  Children (entries whose FQN has a longer prefix
-- matching a parent's FQN) are placed in 'CoqProps.blockChildren' of their
-- parent, preserving the original order.
nestCoqBlocks :: [(String, [CoqProps.CoqDecl])] -> [CoqProps.CoqBlock]
nestCoqBlocks flatBlocks = buildForest ""
  where
    buildForest parentFqn =
      [ CoqProps.CoqBlock (localName fqn) (buildForest fqn) decls
      | (fqn, decls) <- flatBlocks
      , parentOf fqn == parentFqn
      ]

    parentOf fqn = case reverse (splitOnDot fqn) of
      (_:rest) -> intercalate "." (reverse rest)
      []       -> ""

    localName fqn = case reverse (splitOnDot fqn) of
      (x:_) -> x
      []    -> fqn

    splitOnDot s = case break (== '.') s of
      (h, [])     -> [h]
      (h, _:rest) -> h : splitOnDot rest
