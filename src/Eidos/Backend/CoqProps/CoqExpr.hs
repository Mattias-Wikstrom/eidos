-- | Core expression and document types for Coq export.
--
-- Mirrors 'Eidos.Backend.LeanProps.LeanExpr' for Coq output.
--
-- == Document model
--
-- A 'CoqDoc' is a sequence of 'CoqBlock' values.  Each block corresponds to
-- exactly one Coq @Module … End@ region (or the file-level scope for the root
-- theory, which uses the reserved name @__main__@).  Blocks are always emitted
-- flat — subtheories are never nested inside their parent's @Module@ block.
-- Blocks must be ordered so that dependencies are declared before their
-- dependents (post-order over the subtheory tree).
module Eidos.Backend.CoqProps.CoqExpr
  ( -- * Document structure
    CoqDoc (..)
  , CoqBlock (..)
  , CoqDecl (..)
    -- * Axioms
  , CoqAxiom (..)
    -- * Expression language
  , CoqExpr (..)
    -- * Rendering
  , renderCoqDoc
  , renderCoqExpr
  , collectUsedAbbrevNames
  ) where

import Data.Char (isAlphaNum)
import Data.List (nub)
import qualified Eidos.IR as IR

-- ---------------------------------------------------------------------------
-- Document structure
-- ---------------------------------------------------------------------------

data CoqDoc = CoqDoc
  { coqDocTheoryName :: String
  , coqDocBlocks     :: [CoqBlock]
  } deriving (Eq, Show)

-- | One flat @Module … End@ region in the output.
--
-- 'blockModule' is the Coq module identifier.  The root theory uses the
-- reserved name @\"__main__\"@, rendered at file scope with no @Module@\/@End@
-- wrapper.  Dotted namespace names (e.g. @\"lattice.lower\"@) have their dots
-- replaced with underscores to form a valid Coq identifier.
data CoqBlock = CoqBlock
  { blockModule :: String      -- ^ @\"__main__\"@ or a dotted FQN
  , blockDecls  :: [CoqDecl]
  } deriving (Eq, Show)

data CoqDecl
  = DeclComment  String    -- ^ @(* comment *)@
  | DeclBlankLine           -- ^ empty line
  | DeclAxiom    CoqAxiom  -- ^ @Axiom name : body.@
  deriving (Eq, Show)

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
  | CProjectIntoInterval CoqExpr CoqExpr CoqExpr
    -- ^ @ProjectIntoInterval x lo hi@
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Rendering
-- ---------------------------------------------------------------------------

collectUsedAbbrevNames :: CoqDoc -> [String]
collectUsedAbbrevNames doc =
  nub [ n | blk  <- coqDocBlocks doc
           , decl <- blockDecls blk
           , DeclAxiom ax <- [decl]
           , n <- exprAbbrevs (axiomType ax) ]
  where
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
    exprAbbrevs (CBoundedForall _ _ _ b) = "IsWithinBounds" : exprAbbrevs b
    exprAbbrevs (CIsWithinBounds _ _ _)  = ["IsWithinBounds"]
    exprAbbrevs (CIsIndividual _ _ _)    = ["IsIndividual"]
    exprAbbrevs (CProjectIntoInterval x lo hi) =
      "ProjectIntoInterval" : concatMap exprAbbrevs [x, lo, hi]
    exprAbbrevs _                     = []

renderCoqDoc :: CoqDoc -> String
renderCoqDoc doc =
  let used        = collectUsedAbbrevNames doc
      abbrevLines = [ renderAbbrevDef ad
                    | ad <- IR.allAbbrevDefs
                    , IR.abbrevName ad `elem` used ]
      preamble    =
        [ "(* Generated by Eidos compiler *)"
        , "(* Theory: " ++ coqDocTheoryName doc ++ " *)"
        , ""
        ] ++ abbrevLines ++ [ "" | not (null abbrevLines) ]
  in unlines preamble
  ++ concatMap renderBlock (coqDocBlocks doc)

renderAbbrevDef :: IR.AbbrevDef -> String
renderAbbrevDef ad =
  "Definition " ++ IR.abbrevName ad
  ++ " " ++ unwords [ "(" ++ p ++ " : Prop)" | p <- IR.abbrevParams ad ]
  ++ " : Prop := " ++ renderCoqExpr (abbrevBodyToCoq (IR.abbrevBody ad)) ++ "."

abbrevBodyToCoq :: IR.MereoExpr -> CoqExpr
abbrevBodyToCoq (IR.MSum a b)     = CConj   (abbrevBodyToCoq a) (abbrevBodyToCoq b)
abbrevBodyToCoq (IR.MProd a b)    = CDisj   (abbrevBodyToCoq a) (abbrevBodyToCoq b)
abbrevBodyToCoq (IR.MDiff a b)    = CImpl   (abbrevBodyToCoq b) (abbrevBodyToCoq a)
abbrevBodyToCoq (IR.MRevDiff a b) = CImpl   (abbrevBodyToCoq a) (abbrevBodyToCoq b)
abbrevBodyToCoq (IR.MSymDiff a b) = CBicond (abbrevBodyToCoq a) (abbrevBodyToCoq b)
abbrevBodyToCoq (IR.MVar n)       = CVar n
abbrevBodyToCoq IR.MZero          = CVar "True"
abbrevBodyToCoq (IR.MAbbrevApp name args) =
  CApp (CVar name) (map abbrevBodyToCoq args)
abbrevBodyToCoq (IR.MBoundedSum var lo hi body) =
  CForall var CProp
    (CImpl (CApp (CVar "IsWithinBounds") [abbrevBodyToCoq lo, abbrevBodyToCoq hi, CVar var])
           (abbrevBodyToCoq body))

-- | Sanitize a dotted FQN to a valid flat Coq module identifier.
sanitizeModuleName :: String -> String
sanitizeModuleName = map (\c -> if isAlphaNum c || c `elem` "_'" then c else '_')

renderBlock :: CoqBlock -> String
renderBlock blk
  | blockModule blk == "__main__" =
      unlines (map renderDecl (blockDecls blk))
  | otherwise =
      let modName = sanitizeModuleName (blockModule blk)
      in unlines
           (  [ "Module " ++ modName ++ "." ]
           ++ map renderDecl (blockDecls blk)
           ++ [ "End " ++ modName ++ "."
              , ""
              ]
           )

renderDecl :: CoqDecl -> String
renderDecl DeclBlankLine    = ""
renderDecl (DeclComment c)  = "(* " ++ c ++ " *)"
renderDecl (DeclAxiom ax)   = renderAxiom ax

renderAxiom :: CoqAxiom -> String
renderAxiom (CoqAxiom name ty) =
  "Axiom " ++ name ++ " : " ++ renderCoqExpr ty ++ "."

parenArg :: CoqExpr -> String
parenArg e = case e of
  CForall        {} -> "(" ++ renderCoqExpr e ++ ")"
  CExists        {} -> "(" ++ renderCoqExpr e ++ ")"
  CEq            {} -> "(" ++ renderCoqExpr e ++ ")"
  CBoundedForall {} -> "(" ++ renderCoqExpr e ++ ")"
  _                 -> renderCoqExpr e

renderCoqExpr :: CoqExpr -> String
renderCoqExpr CProp =
  "Prop"
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
  "forall " ++ var ++ " : Prop, "
    ++ renderCoqExpr (CIsWithinBounds lo var hi)
    ++ " -> " ++ renderCoqExpr body
renderCoqExpr (CProjectIntoInterval x lo hi) =
  "(ProjectIntoInterval "
    ++ renderCoqExpr x ++ " "
    ++ renderCoqExpr lo ++ " "
    ++ renderCoqExpr hi ++ ")"
