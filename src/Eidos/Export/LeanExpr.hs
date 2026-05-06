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
module Eidos.Export.LeanExpr
  ( -- * Document structure
    LeanDoc (..)
  , LeanBlock (..)
  , LeanDecl (..)
    -- * Axioms
  , LeanAxiom (..)
    -- * Expression language
  , LeanExpr (..)
    -- * Rendering
  , renderLeanDoc
  , renderLeanExpr
  ) where

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
-- The root theory uses the reserved name @\"__main__\"@, which is rendered
-- at file scope (no @namespace@\/@end@ wrapper).  All other theories use
-- their 'IR.theoryFullyQualifiedName', which may contain dots
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
  deriving (Eq, Show)

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
  | LProjectIntoInterval LeanExpr LeanExpr LeanExpr
    -- ^ @ProjectIntoInterval x lo hi@
  | LFactWrapper LeanExpr
    -- ^ Plain fact wrapper: @(P_Min ∧ body) ↔ P_Min@.
  | LAssertionWrapper LeanExpr
    -- ^ Assertion wrapper: @(P_Min ∧ (P_Max ∨ body)) ↔ P_Min@.
  | LMetafactWrapper LeanExpr
    -- ^ Metafact wrapper: @(U_Min ∧ body) ↔ U_Min@.
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Rendering
-- ---------------------------------------------------------------------------

-- | Render a 'LeanDoc' to Lean 4 source text.
--
-- Emits the file-level preamble (helper definitions) followed by each
-- 'LeanBlock'.  The @__main__@ block is rendered without an explicit
-- @namespace@\/@end@ wrapper — its declarations appear at file scope.
-- All other blocks are wrapped in @namespace <name> … end <name>@.
renderLeanDoc :: LeanDoc -> String
renderLeanDoc doc =
  unlines
    [ "-- Generated by Eidos compiler"
    , "-- Theory: " ++ leanDocTheoryName doc
    , ""
    , "def IsWithinBounds (lo hi x : Prop) : Prop := (hi → x) ∧ (x → lo)"
    , "def ProjectIntoInterval (x lo hi : Prop) : Prop := (x ∧ lo) ∨ hi"
    , "def IsIndividual (lo hi x : Prop) : Prop := True"
    , ""
    ]
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

renderAxiom :: LeanAxiom -> String
renderAxiom (LeanAxiom name ty) =
  "axiom " ++ name ++ ": " ++ renderLeanExpr ty

-- | Render a 'LeanExpr' to a Lean 4 string.
renderLeanExpr :: LeanExpr -> String
renderLeanExpr LProp =
  "Prop"
renderLeanExpr (LVar n) =
  n
renderLeanExpr (LApp f args) =
  "(" ++ renderLeanExpr f ++ " " ++ unwords (map renderLeanExpr args) ++ ")"
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
    ++ renderLeanExpr (LIsWithinBounds lo var hi)
    ++ " → " ++ renderLeanExpr body
renderLeanExpr (LProjectIntoInterval x lo hi) =
  "(ProjectIntoInterval "
    ++ renderLeanExpr x ++ " "
    ++ renderLeanExpr lo ++ " "
    ++ renderLeanExpr hi ++ ")"
renderLeanExpr (LFactWrapper body) =
  renderLeanExpr (LBicond (LConj (LVar "ℙ_Min") body) (LVar "ℙ_Min"))
renderLeanExpr (LAssertionWrapper body) =
  renderLeanExpr (LBicond (LConj (LVar "ℙ_Min") (LDisj (LVar "ℙ_Max") body)) (LVar "ℙ_Min"))
renderLeanExpr (LMetafactWrapper body) =
  renderLeanExpr (LBicond (LConj (LVar "𝕌_Min") body) (LVar "𝕌_Min"))
