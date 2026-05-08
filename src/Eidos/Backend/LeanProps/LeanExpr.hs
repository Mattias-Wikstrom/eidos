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
module Eidos.Backend.LeanProps.LeanExpr
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
  , collectUsedAbbrevNames
  ) where

import Data.List (nub)
import qualified Eidos.IR as IR

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
  | LMetafactWrapper LeanExpr
    -- ^ Metafact wrapper: @(U_Min ∧ body) ↔ U_Min@.
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
           , DeclAxiom ax <- [decl]
           , n <- exprAbbrevs (axiomType ax) ]
  where
    knownAbbrevs :: [String]
    knownAbbrevs = ["IsWithinBounds", "IsIndividual", "ProjectIntoInterval"]

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
    exprAbbrevs (LBoundedForall _ _ _ b) = "IsWithinBounds" : exprAbbrevs b
    exprAbbrevs (LIsWithinBounds _ _ _)  = ["IsWithinBounds"]
    exprAbbrevs (LIsIndividual _ _ _)    = ["IsIndividual"]
    exprAbbrevs (LProjectIntoInterval x lo hi) =
      "ProjectIntoInterval" : concatMap exprAbbrevs [x, lo, hi]
    exprAbbrevs (LMetafactWrapper b)  = exprAbbrevs b
    exprAbbrevs _                     = []  -- LProp, LVar (non-abbrev)

-- | Render a 'LeanDoc' to Lean 4 source text.
--
-- Emits the file-level preamble (helper definitions) followed by each
-- 'LeanBlock'.  The @__main__@ block is rendered without an explicit
-- @namespace@\/@end@ wrapper — its declarations appear at file scope.
-- All other blocks are wrapped in @namespace <name> … end <name>@.
-- Only abbreviation @def@s that are actually referenced in the document
-- are emitted.
renderLeanDoc :: LeanDoc -> String
renderLeanDoc doc =
  let used       = collectUsedAbbrevNames doc
      abbrevLines = [ renderAbbrevDef ad
                    | ad <- IR.allAbbrevDefs
                    , IR.abbrevName ad `elem` used ]
      preamble    =
        [ "-- Generated by Eidos compiler"
        , "-- Theory: " ++ leanDocTheoryName doc
        , ""
        ] ++ abbrevLines ++ [ "" | not (null abbrevLines) ]
  in unlines preamble
  ++ concatMap renderBlock (leanDocBlocks doc)

-- | Render one compiler-internal abbreviation as a Lean 4 @def@.
-- The body is obtained by translating 'IR.abbrevBody' with 'abbrevBodyToLean'.
renderAbbrevDef :: IR.AbbrevDef -> String
renderAbbrevDef ad =
  "def " ++ IR.abbrevName ad
  ++ " " ++ unwords [ "(" ++ p ++ " : Prop)" | p <- IR.abbrevParams ad ]
  ++ " : Prop := " ++ renderLeanExpr (abbrevBodyToLean (IR.abbrevBody ad))

-- | Translate a 'IR.MereoExpr' that forms the body of a compiler-internal
-- abbreviation definition into a 'LeanExpr'.
--
-- This differs from the fact-body translator in 'MkAxiomSets' in two ways:
--   * 'MVar' names are kept verbatim (they are abbreviation parameters such as
--     @"lo"@, @"hi"@, @"x"@, not theory-specific sort-bound names).
--   * 'MZero' renders as Lean's @True@ rather than @ℙ_Min@, because here we
--     are building a standalone Lean definition, not a theory assertion.
abbrevBodyToLean :: IR.MereoExpr -> LeanExpr
abbrevBodyToLean (IR.MSum a b)     = LConj   (abbrevBodyToLean a) (abbrevBodyToLean b)
abbrevBodyToLean (IR.MProd a b)    = LDisj   (abbrevBodyToLean a) (abbrevBodyToLean b)
abbrevBodyToLean (IR.MDiff a b)    = LImpl   (abbrevBodyToLean b) (abbrevBodyToLean a)
abbrevBodyToLean (IR.MRevDiff a b) = LImpl   (abbrevBodyToLean a) (abbrevBodyToLean b)
abbrevBodyToLean (IR.MSymDiff a b) = LBicond (abbrevBodyToLean a) (abbrevBodyToLean b)
abbrevBodyToLean (IR.MVar n)       = LVar n
abbrevBodyToLean IR.MZero          = LVar "True"
abbrevBodyToLean (IR.MAbbrevApp name args) =
  LApp (LVar name) (map abbrevBodyToLean args)
abbrevBodyToLean (IR.MBoundedSum var lo hi body) =
  LForallKw var LProp
    (LImpl (LApp (LVar "IsWithinBounds") [abbrevBodyToLean lo, abbrevBodyToLean hi, LVar var])
           (abbrevBodyToLean body))

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
renderLeanExpr (LMetafactWrapper body) =
  renderLeanExpr (LBicond (LConj (LVar "𝕌_Min") body) (LVar "𝕌_Min"))
