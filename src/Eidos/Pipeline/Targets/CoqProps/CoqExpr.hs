-- | Core expression and document types for Coq export.
--
-- Mirrors 'Eidos.Pipeline.Targets.LeanProps.LeanExpr' for Coq output.
--
-- == Document model
--
-- A 'CoqDoc' is a tree of 'CoqBlock' values.  Each block corresponds to one
-- Coq @Module … End@ region; child subtheories are nested inside their
-- parent's block via 'blockChildren'.  The reserved name @__main__@ renders
-- at file scope and is only used by test helpers.  Within each block,
-- children are rendered before the block's own declarations (post-order:
-- dependencies before dependents).
module Eidos.Pipeline.Targets.CoqProps.CoqExpr
  ( -- * Document structure
    CoqDoc (..)
  , CoqBlock (..)
  , CoqDecl (..)
    -- * Definitions
  , CoqDef (..)
    -- * Axioms
  , CoqAxiom (..)
    -- * Expression language
  , CoqExpr (..)
    -- * Rendering
  , renderCoqDocWith
  , renderCoqExpr
  , collectUsedAbbrevNames
  ) where

import Data.Char (isAlphaNum)
import Data.List (nub)
import qualified Eidos.Pipeline.FromSyntax.IR as IR

-- ---------------------------------------------------------------------------
-- Document structure
-- ---------------------------------------------------------------------------

data CoqDoc = CoqDoc
  { coqDocTheoryName :: String
  , coqDocBlocks     :: [CoqBlock]
  } deriving (Eq, Show)

-- | One @Module … End@ region in the output, optionally containing nested
-- child modules.
--
-- 'blockModule' is the local Coq module identifier (no dots — just the last
-- component of the FQN).  The reserved name @\"__main__\"@ is recognised by
-- 'renderBlock' as "render at file scope" and is only used by test helpers.
--
-- 'blockChildren' are rendered inside the @Module … End@ block, before the
-- block's own declarations (preserving post-order: children before parents).
data CoqBlock = CoqBlock
  { blockModule   :: String      -- ^ local module name (or @\"__main__\"@)
  , blockChildren :: [CoqBlock]  -- ^ nested sub-modules
  , blockDecls    :: [CoqDecl]
  } deriving (Eq, Show)

data CoqDecl
  = DeclComment  String    -- ^ @(* comment *)@
  | DeclBlankLine           -- ^ empty line
  | DeclAxiom    CoqAxiom  -- ^ @Axiom name : body.@
  | DeclDef      CoqDef    -- ^ @Definition name (p : Prop) … : Prop := body.@
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Definitions
-- ---------------------------------------------------------------------------

-- | A @Definition@ statement: a named function with all-@Prop@ parameters and body.
data CoqDef = CoqDef
  { coqDefName   :: String
  , coqDefParams :: [String]   -- ^ Parameter names; each has type @Prop@.
  , coqDefBody   :: CoqExpr
  } deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Axioms
-- ---------------------------------------------------------------------------

data CoqAxiom = CoqAxiom
  { axiomName :: String
  , axiomType :: CoqExpr
  } deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Expression language
-- ---------------------------------------------------------------------------

data CoqExpr
  = CProp
    -- ^ @Prop@
  | CVar String
    -- ^ Atomic name.
  | CApp CoqExpr [CoqExpr]
    -- ^ Function application.
  | CImpl CoqExpr CoqExpr
    -- ^ @A -> B@
  | CConj CoqExpr CoqExpr
    -- ^ @A /\ B@
  | CDisj CoqExpr CoqExpr
    -- ^ @A \/ B@
  | CTop
    -- ^ ⊤
  | CBot
    -- ^ ⊥
  | CBicond CoqExpr CoqExpr
    -- ^ @A <-> B@
  | CForall String CoqExpr CoqExpr
    -- ^ @forall x : T, body@
  | CExists String CoqExpr CoqExpr
    -- ^ @exists x : T, body@
  | CEq CoqExpr CoqExpr
    -- ^ @A = B@
  | CIsWithinBounds String String String
    -- ^ @CIsWithinBounds lo var hi@ renders as @(IsWithinBounds lo hi var)@.
  | CIsIndividual String String String
    -- ^ @CIsIndividual lo var hi@ renders as @(IsIndividual lo hi var)@.
  | CBoundedForall String String String CoqExpr
    -- ^ @CBoundedForall var lo hi body@ renders as
    --   @forall var : Prop, (IsWithinBounds lo hi var) -> body@.
    --   Universal quantification over a set variable.
  | CForallIndividuals String String String CoqExpr
    -- ^ @CForallIndividuals var lo hi body@ renders as
    --   @forall var : Prop, (IsIndividual lo hi var) -> body@.
    --   Universal quantification over an individual.
  | CBoundedExists String String String CoqExpr
    -- ^ @CBoundedExists var lo hi body@ renders as
    --   @exists var : Prop, (IsWithinBounds lo hi var) -> body@.
    --   Existential quantification over a set variable.
  | CExistsIndividuals String String String CoqExpr
    -- ^ @CExistsIndividuals var lo hi body@ renders as
    --   @exists var : Prop, (IsIndividual lo hi var) -> body@.
    --   Existential quantification over an individual.
  | CProjectIntoInterval CoqExpr CoqExpr CoqExpr
    -- ^ @ProjectIntoInterval x lo hi@
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Rendering
-- ---------------------------------------------------------------------------

collectUsedAbbrevNames :: CoqDoc -> [String]
collectUsedAbbrevNames doc =
  nub (concatMap collectFromBlock (coqDocBlocks doc))
  where
    collectFromBlock blk =
      concatMap declAbbrevs (blockDecls blk)
      ++ concatMap collectFromBlock (blockChildren blk)

    declAbbrevs (DeclAxiom ax) = exprAbbrevs (axiomType ax)
    declAbbrevs (DeclDef   df) = exprAbbrevs (coqDefBody df)
    declAbbrevs _              = []
    knownAbbrevs :: [String]
    knownAbbrevs = map IR.abbrevName IR.allAbbrevDefs

    exprAbbrevs :: CoqExpr -> [String]
    exprAbbrevs (CImpl a b)           = exprAbbrevs a ++ exprAbbrevs b
    exprAbbrevs (CConj a b)           = exprAbbrevs a ++ exprAbbrevs b
    exprAbbrevs (CDisj a b)           = exprAbbrevs a ++ exprAbbrevs b
    exprAbbrevs (CBicond a b)         = exprAbbrevs a ++ exprAbbrevs b
    exprAbbrevs (CEq a b)             = exprAbbrevs a ++ exprAbbrevs b
    exprAbbrevs (CForall _ _ b)       = exprAbbrevs b
    exprAbbrevs (CExists _ _ b)       = exprAbbrevs b
    exprAbbrevs (CApp f args)         = exprAbbrevs f ++ concatMap exprAbbrevs args
    exprAbbrevs (CVar n)
      | n `elem` knownAbbrevs         = [n]
      | otherwise                     = []
    exprAbbrevs (CBoundedForall      _ _ _ b) = "IsWithinBounds" : exprAbbrevs b
    exprAbbrevs (CForallIndividuals  _ _ _ b) = "IsIndividual"   : exprAbbrevs b
    exprAbbrevs (CBoundedExists      _ _ _ b) = "IsWithinBounds" : exprAbbrevs b
    exprAbbrevs (CExistsIndividuals  _ _ _ b) = "IsIndividual"   : exprAbbrevs b
    exprAbbrevs (CIsWithinBounds _ _ _)  = ["IsWithinBounds"]
    exprAbbrevs (CIsIndividual _ _ _)    = ["IsIndividual"]
    exprAbbrevs (CProjectIntoInterval x lo hi) =
      "ProjectIntoInterval" : concatMap exprAbbrevs [x, lo, hi]
    exprAbbrevs _                     = []

renderCoqDocWith :: (IR.AbbrevDef -> String) -> CoqDoc -> String
renderCoqDocWith renderAbbrev doc =
  let used        = collectUsedAbbrevNames doc
      abbrevLines = [ renderAbbrev ad
                    | ad <- IR.allAbbrevDefs
                    , IR.abbrevName ad `elem` used ]
      preamble    =
        [ "(* Generated by Eidos compiler *)"
        , "(* Theory: " ++ coqDocTheoryName doc ++ " *)"
        , ""
        , "Require Import EidosRuntime."
        , ""
        ] ++ abbrevLines ++ [ "" | not (null abbrevLines) ]
  in unlines preamble
  ++ concatMap renderBlock (coqDocBlocks doc)

-- | Sanitize a dotted FQN to a valid flat Coq module identifier.
sanitizeModuleName :: String -> String
sanitizeModuleName = map (\c -> if isAlphaNum c || c `elem` "_'" then c else '_')

renderBlock :: CoqBlock -> String
renderBlock blk
  | blockModule blk == "__main__" =
      concatMap renderBlock (blockChildren blk)
      ++ unlines (map renderDecl (blockDecls blk))
  | otherwise =
      let modName  = sanitizeModuleName (blockModule blk)
          children = concatMap renderBlock (blockChildren blk)
          decls    = unlines (map renderDecl (blockDecls blk))
      in "Module " ++ modName ++ ".\n"
         ++ children
         ++ decls
         ++ "End " ++ modName ++ ".\n\n"

renderDecl :: CoqDecl -> String
renderDecl DeclBlankLine    = ""
renderDecl (DeclComment c)  = "(* " ++ c ++ " *)"
renderDecl (DeclAxiom ax)   = renderAxiom ax
renderDecl (DeclDef    df)  = renderCoqDef df

renderCoqDef :: CoqDef -> String
renderCoqDef (CoqDef name params body) =
  "Definition " ++ name
  ++ " " ++ unwords [ "(" ++ p ++ " : MereologicalObject)" | p <- params ]
  ++ " : MereologicalObject := " ++ renderCoqExpr body ++ "."

renderAxiom :: CoqAxiom -> String
renderAxiom (CoqAxiom name ty) =
  "Axiom " ++ name ++ " : " ++ renderCoqExpr ty ++ "."

parenArg :: CoqExpr -> String
parenArg e = case e of
  CForall        {} -> "(" ++ renderCoqExpr e ++ ")"
  CExists        {} -> "(" ++ renderCoqExpr e ++ ")"
  CEq            {} -> "(" ++ renderCoqExpr e ++ ")"
  CBoundedForall{}     -> "(" ++ renderCoqExpr e ++ ")"
  CForallIndividuals{} -> "(" ++ renderCoqExpr e ++ ")"
  CBoundedExists{}     -> "(" ++ renderCoqExpr e ++ ")"
  CExistsIndividuals{} -> "(" ++ renderCoqExpr e ++ ")"
  _                 -> renderCoqExpr e

renderCoqExpr :: CoqExpr -> String
renderCoqExpr CProp =
  "MereologicalObject"
renderCoqExpr (CVar n) =
  n
renderCoqExpr (CApp f args) =
  "(" ++ renderCoqExpr f ++ " " ++ unwords (map parenArg args) ++ ")"
renderCoqExpr (CImpl a b) =
  "(" ++ renderCoqExpr a ++ " -> " ++ renderCoqExpr b ++ ")"
renderCoqExpr (CConj a b) =
  "(" ++ renderCoqExpr a ++ " /\\ " ++ renderCoqExpr b ++ ")"
renderCoqExpr (CDisj a b) =
  "(" ++ renderCoqExpr a ++ " \\/ " ++ renderCoqExpr b ++ ")"
renderCoqExpr (CBicond a b) =
  "(" ++ renderCoqExpr a ++ " <-> " ++ renderCoqExpr b ++ ")"
renderCoqExpr (CForall x ty body) =
  "forall " ++ x ++ " : " ++ renderCoqExpr ty ++ ", " ++ renderCoqExpr body
renderCoqExpr (CExists x ty body) =
  "exists " ++ x ++ " : " ++ renderCoqExpr ty ++ ", " ++ renderCoqExpr body
renderCoqExpr (CEq a b) =
  renderCoqExpr a ++ " = " ++ renderCoqExpr b
renderCoqExpr (CIsWithinBounds lo v hi) =
  "(IsWithinBounds " ++ lo ++ " " ++ hi ++ " " ++ v ++ ")"
renderCoqExpr (CIsIndividual lo v hi) =
  "(IsIndividual " ++ lo ++ " " ++ hi ++ " " ++ v ++ ")"
renderCoqExpr (CBoundedForall var lo hi body) =
  "forall " ++ var ++ " : MereologicalObject, "
    ++ renderCoqExpr (CIsWithinBounds lo var hi) ++ " -> " ++ renderCoqExpr body
renderCoqExpr (CForallIndividuals var lo hi body) =
  "forall " ++ var ++ " : MereologicalObject, "
    ++ renderCoqExpr (CIsIndividual lo var hi) ++ " -> " ++ renderCoqExpr body
renderCoqExpr (CBoundedExists var lo hi body) =
  "exists " ++ var ++ " : MereologicalObject, "
    ++ renderCoqExpr (CIsWithinBounds lo var hi) ++ " -> " ++ renderCoqExpr body
renderCoqExpr (CExistsIndividuals var lo hi body) =
  "exists " ++ var ++ " : MereologicalObject, "
    ++ renderCoqExpr (CIsIndividual lo var hi) ++ " -> " ++ renderCoqExpr body
renderCoqExpr (CProjectIntoInterval x lo hi) =
  "(ProjectIntoInterval "
    ++ renderCoqExpr x ++ " "
    ++ renderCoqExpr lo ++ " "
    ++ renderCoqExpr hi ++ ")"
renderLeanExpr CTop = "True"
renderLeanExpr CBot = "False"
