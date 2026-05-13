-- | Core expression and document types for Lean 4 export.
--
-- This module is imported by both 'Eidos.Export.LeanAxiomSet' and
-- 'Eidos.Export.LeanProps'.  Keeping it separate avoids a circular
-- dependency and makes the expression language easy to test in isolation.
--
-- == Document model
--
-- A 'LeanDoc' is a sequence of 'LeanBlock' values.  Each block corresponds
-- to exactly one Lean 4 @namespace … end@ region (or the file-level scope
-- for the root theory, which uses the reserved name @__main__@).  Blocks are
-- always emitted flat — subtheories are never nested inside their parent's
-- @namespace@ block.  Blocks must be ordered so that dependencies are
-- declared before their dependents (post-order over the subtheory tree,
-- i.e. children before parents).
module Eidos.Pipeline.Targets.LeanProps.LeanExpr
  ( -- * Document structure
    LeanDoc (..)
  , LeanBlock (..)
  , LeanDecl (..)
    -- * Definitions
  , LeanDef (..)
    -- * Axioms
  , LeanAxiom (..)
    -- * Expression language
  , LeanExpr (..)
    -- * Rendering
  , renderLeanDocWith
  , renderLeanExpr
  , collectUsedAbbrevNames
  ) where

import Data.List (nub)
import qualified Eidos.Pipeline.FromSyntax.IR as IR

-- ---------------------------------------------------------------------------
-- Document structure
-- ---------------------------------------------------------------------------

-- | A complete Lean 4 document ready to be printed.
--
-- 'leanDocBlocks' is ordered: blocks appear in the order they are emitted
-- (children before parents, so that cross-namespace references are valid).
data LeanDoc = LeanDoc
  { leanDocTheoryName :: String
  , leanDocBlocks     :: [LeanBlock]
  } deriving (Eq, Show)

-- | One flat @namespace … end@ region in the output.
--
-- 'blockNamespace' is the Lean 4 namespace identifier for this block.
-- Every theory — including the root — uses its 'IR.theoryFullyQualifiedName'
-- so all blocks get a @namespace@\/@end@ wrapper.  The reserved name
-- @\"__main__\"@ is recognised by 'renderBlock' as "render at file scope"
-- and is only used by test helpers that bypass 'theoryBlocks'.
-- Namespace identifiers may contain dots
-- (e.g. @\"lattice.lower_semi_lattice.preorder\"@); Lean 4 treats a dotted
-- name as a single flat namespace identifier, not a nested path.
data LeanBlock = LeanBlock
  { blockNamespace :: String      -- ^ @\"__main__\"@ or a dotted FQN
  , blockDecls     :: [LeanDecl]  -- ^ declarations inside this namespace
  } deriving (Eq, Show)

-- | A single item inside a 'LeanBlock'.
data LeanDecl
  = DeclComment  String    -- ^ @-- comment@
  | DeclBlankLine           -- ^ empty line
  | DeclAxiom    LeanAxiom -- ^ @axiom name : body@
  | DeclDef      LeanDef   -- ^ @def name (p : Prop) … : Prop := body@
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Definitions
-- ---------------------------------------------------------------------------

-- | A @def@ statement: a named function with all-@Prop@ parameters and body.
data LeanDef = LeanDef
  { leanDefName   :: String
  , leanDefParams :: [String]   -- ^ Parameter names; each has type @Prop@.
  , leanDefBody   :: LeanExpr
  } deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Axioms
-- ---------------------------------------------------------------------------

-- | An @axiom@ statement with a name and a type expression.
data LeanAxiom = LeanAxiom
  { axiomName :: String
  , axiomType :: LeanExpr
  } deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Expression language
-- ---------------------------------------------------------------------------

-- | A Lean 4 proposition (the expression language we need).
data LeanExpr
  = LProp
    -- ^ @Prop@
  | LVar String
    -- ^ Atomic name.  May contain dots for cross-namespace references,
    --   e.g. @\"lattice.lower_semi_lattice.preorder.D_Min\"@.
    --   Dots pass through 'sanitizeName' unchanged.
  | LApp LeanExpr [LeanExpr]
    -- ^ Function application.
  | LImpl LeanExpr LeanExpr
    -- ^ @A → B@
  | LConj LeanExpr LeanExpr
    -- ^ @A ∧ B@
  | LDisj LeanExpr LeanExpr
    -- ^ @A ∨ B@
  | LTop
    -- ^ ⊤
  | LBot
    -- ^ ⊥
  | LBicond LeanExpr LeanExpr
    -- ^ @A ↔ B@
  | LForall String LeanExpr LeanExpr
    -- ^ @∀ x : T, body@  (symbol style)
  | LForallKw String LeanExpr LeanExpr
    -- ^ @forall x : T, body@  (keyword style)
  | LExists String LeanExpr LeanExpr
    -- ^ @∃ x : T, body@
  | LEq LeanExpr LeanExpr
    -- ^ @A = B@
  | LIsWithinBounds String String String
    -- ^ @LIsWithinBounds lo var hi@ renders as
    --   @(IsWithinBounds lo hi var)@.
    --   All three fields are variable /names/ (not expressions), kept as
    --   'String' because 'IsWithinBounds' is always applied to atomic names
    --   in our encoding.  Names may be dotted cross-namespace references.
  | LIsIndividual String String String
    -- ^ @LIsIndividual lo var hi@ renders as @(IsIndividual lo hi var)@.
    --   Guards first-order (individual) quantification.
  | LBoundedForall String String String LeanExpr
    -- ^ @LBoundedForall var lo hi body@ renders as
    --   @forall var : Prop, (IsWithinBounds lo hi var) → body@.
    --   Universal quantification over a set variable.
  | LForallIndividuals String String String LeanExpr
    -- ^ @LForallIndividuals var lo hi body@ renders as
    --   @forall var : Prop, (IsIndividual lo hi var) → body@.
    --   Universal quantification over an individual.
  | LBoundedExists String String String LeanExpr
    -- ^ @LBoundedExists var lo hi body@ renders as
    --   @exists var : Prop, (IsWithinBounds lo hi var) → body@.
    --   Existential quantification over a set variable.
  | LExistsIndividuals String String String LeanExpr
    -- ^ @LExistsIndividuals var lo hi body@ renders as
    --   @exists var : Prop, (IsIndividual lo hi var) → body@.
    --   Existential quantification over an individual.
  | LProjectIntoInterval LeanExpr LeanExpr LeanExpr
    -- ^ @ProjectIntoInterval x lo hi@
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Rendering
-- ---------------------------------------------------------------------------

-- | Collect the names of compiler-internal abbreviations used anywhere in the
-- document.  Only names from the known set {"IsWithinBounds", "IsIndividual",
-- "ProjectIntoInterval"} are returned.  The result is de-duplicated.
collectUsedAbbrevNames :: LeanDoc -> [String]
collectUsedAbbrevNames doc =
  nub [ n | blk  <- leanDocBlocks doc
           , decl <- blockDecls blk
           , n   <- declAbbrevs decl ]
  where
    declAbbrevs (DeclAxiom ax) = exprAbbrevs (axiomType ax)
    declAbbrevs (DeclDef   df) = exprAbbrevs (leanDefBody df)
    declAbbrevs _              = []
    knownAbbrevs :: [String]
    knownAbbrevs = map IR.abbrevName IR.allAbbrevDefs

    exprAbbrevs :: LeanExpr -> [String]
    exprAbbrevs (LImpl a b)           = exprAbbrevs a ++ exprAbbrevs b
    exprAbbrevs (LConj a b)           = exprAbbrevs a ++ exprAbbrevs b
    exprAbbrevs (LDisj a b)           = exprAbbrevs a ++ exprAbbrevs b
    exprAbbrevs (LBicond a b)         = exprAbbrevs a ++ exprAbbrevs b
    exprAbbrevs (LEq a b)             = exprAbbrevs a ++ exprAbbrevs b
    exprAbbrevs (LForall _ _ b)       = exprAbbrevs b
    exprAbbrevs (LForallKw _ _ b)     = exprAbbrevs b
    exprAbbrevs (LExists _ _ b)       = exprAbbrevs b
    exprAbbrevs (LApp f args)         = exprAbbrevs f ++ concatMap exprAbbrevs args
    exprAbbrevs (LVar n)
      | n `elem` knownAbbrevs         = [n]
      | otherwise                     = []
    exprAbbrevs (LBoundedForall      _ _ _ b) = "IsWithinBounds" : exprAbbrevs b
    exprAbbrevs (LForallIndividuals  _ _ _ b) = "IsIndividual"   : exprAbbrevs b
    exprAbbrevs (LBoundedExists      _ _ _ b) = "IsWithinBounds" : exprAbbrevs b
    exprAbbrevs (LExistsIndividuals  _ _ _ b) = "IsIndividual"   : exprAbbrevs b
    exprAbbrevs (LIsWithinBounds _ _ _)  = ["IsWithinBounds"]
    exprAbbrevs (LIsIndividual _ _ _)    = ["IsIndividual"]
    exprAbbrevs (LProjectIntoInterval x lo hi) =
      "ProjectIntoInterval" : concatMap exprAbbrevs [x, lo, hi]
    exprAbbrevs _                     = []  -- LProp, LVar (non-abbrev)

-- | Render a 'LeanDoc' to Lean 4 source text, using the supplied function
-- to render each compiler-internal abbreviation definition.
--
-- Emits the file-level preamble (helper definitions) followed by each
-- 'LeanBlock'.  Every block is wrapped in @namespace <name> … end <name>@
-- except for the reserved name @\"__main__\"@, which renders at file scope
-- (used only by test helpers; 'theoryBlocks' no longer emits it).
-- Only abbreviation @def@s that are actually referenced in the document
-- are emitted.
renderLeanDocWith :: (IR.AbbrevDef -> String) -> LeanDoc -> String
renderLeanDocWith renderAbbrev doc =
  let used       = collectUsedAbbrevNames doc
      abbrevLines = [ renderAbbrev ad
                    | ad <- IR.allAbbrevDefs
                    , IR.abbrevName ad `elem` used ]
      preamble    =
        [ "-- Generated by Eidos compiler"
        , "-- Theory: " ++ leanDocTheoryName doc
        , ""
        ] ++ abbrevLines ++ [ "" | not (null abbrevLines) ]
  in unlines preamble
  ++ concatMap renderBlock (leanDocBlocks doc)

renderBlock :: LeanBlock -> String
renderBlock blk
  | blockNamespace blk == "__main__" =
      unlines (map renderDecl (blockDecls blk))
  | otherwise =
      unlines
        (  [ "namespace " ++ blockNamespace blk ]
        ++ map renderDecl (blockDecls blk)
        ++ [ "end " ++ blockNamespace blk
           , ""    -- blank line after each namespace for readability
           ]
        )

renderDecl :: LeanDecl -> String
renderDecl DeclBlankLine    = ""
renderDecl (DeclComment c)  = "-- " ++ c
renderDecl (DeclAxiom ax)   = renderAxiom ax
renderDecl (DeclDef    df)  = renderLeanDef df

renderLeanDef :: LeanDef -> String
renderLeanDef (LeanDef name params body) =
  "def " ++ name
  ++ " " ++ unwords [ "(" ++ p ++ " : Prop)" | p <- params ]
  ++ " : Prop := " ++ renderLeanExpr body

renderAxiom :: LeanAxiom -> String
renderAxiom (LeanAxiom name ty) =
  "axiom " ++ name ++ ": " ++ renderLeanExpr ty

-- | Wrap a 'LeanExpr' in parentheses when used as a function argument.
-- Expressions that already render with outer brackets are left alone;
-- binders (forall/exists) and bare equality need an explicit wrapper.
parenArg :: LeanExpr -> String
parenArg e = case e of
  LForall    {} -> "(" ++ renderLeanExpr e ++ ")"
  LForallKw  {} -> "(" ++ renderLeanExpr e ++ ")"
  LExists    {} -> "(" ++ renderLeanExpr e ++ ")"
  LEq        {} -> "(" ++ renderLeanExpr e ++ ")"
  LBoundedForall{}     -> "(" ++ renderLeanExpr e ++ ")"
  LForallIndividuals{} -> "(" ++ renderLeanExpr e ++ ")"
  LBoundedExists{}     -> "(" ++ renderLeanExpr e ++ ")"
  LExistsIndividuals{} -> "(" ++ renderLeanExpr e ++ ")"
  _              -> renderLeanExpr e

-- | Render a 'LeanExpr' to a Lean 4 string.
renderLeanExpr :: LeanExpr -> String
renderLeanExpr LProp =
  "Prop"
renderLeanExpr (LVar n) =
  n
renderLeanExpr (LApp f args) =
  "(" ++ renderLeanExpr f ++ " " ++ unwords (map parenArg args) ++ ")"
renderLeanExpr (LImpl a b) =
  "(" ++ renderLeanExpr a ++ " → " ++ renderLeanExpr b ++ ")"
renderLeanExpr (LConj a b) =
  "(" ++ renderLeanExpr a ++ " ∧ " ++ renderLeanExpr b ++ ")"
renderLeanExpr (LDisj a b) =
  "(" ++ renderLeanExpr a ++ " ∨ " ++ renderLeanExpr b ++ ")"
renderLeanExpr (LBicond a b) =
  "(" ++ renderLeanExpr a ++ " ↔ " ++ renderLeanExpr b ++ ")"
renderLeanExpr (LForall x ty body) =
  "∀ " ++ x ++ " : " ++ renderLeanExpr ty ++ ", " ++ renderLeanExpr body
renderLeanExpr (LForallKw x ty body) =
  "forall " ++ x ++ " : " ++ renderLeanExpr ty ++ ", " ++ renderLeanExpr body
renderLeanExpr (LExists x ty body) =
  "∃ " ++ x ++ " : " ++ renderLeanExpr ty ++ ", " ++ renderLeanExpr body
renderLeanExpr (LEq a b) =
  renderLeanExpr a ++ " = " ++ renderLeanExpr b
renderLeanExpr (LIsWithinBounds lo v hi) =
  "(IsWithinBounds " ++ lo ++ " " ++ hi ++ " " ++ v ++ ")"
renderLeanExpr (LIsIndividual lo v hi) =
  "(IsIndividual " ++ lo ++ " " ++ hi ++ " " ++ v ++ ")"
renderLeanExpr (LBoundedForall var lo hi body) =
  "forall " ++ var ++ " : Prop, "
    ++ renderLeanExpr (LIsWithinBounds lo var hi) ++ " → " ++ renderLeanExpr body
renderLeanExpr (LForallIndividuals var lo hi body) =
  "forall " ++ var ++ " : Prop, "
    ++ renderLeanExpr (LIsIndividual lo var hi) ++ " → " ++ renderLeanExpr body
renderLeanExpr (LBoundedExists var lo hi body) =
  "exists " ++ var ++ " : Prop, "
    ++ renderLeanExpr (LIsWithinBounds lo var hi) ++ " → " ++ renderLeanExpr body
renderLeanExpr (LExistsIndividuals var lo hi body) =
  "exists " ++ var ++ " : Prop, "
    ++ renderLeanExpr (LIsIndividual lo var hi) ++ " → " ++ renderLeanExpr body
renderLeanExpr (LProjectIntoInterval x lo hi) =
  "(ProjectIntoInterval "
    ++ renderLeanExpr x ++ " "
    ++ renderLeanExpr lo ++ " "
    ++ renderLeanExpr hi ++ ")"
