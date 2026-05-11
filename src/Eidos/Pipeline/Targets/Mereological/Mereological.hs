module Eidos.Pipeline.Targets.Mereological.Mereological
  ( exportToMereological
  ) where

import qualified Data.List as L
import qualified Eidos.Pipeline.FromSyntax.IR as IR
import qualified Eidos.Pipeline.IRProcessing.MereologicalOpDefs as MOD
import qualified Eidos.Pipeline.PipelineCore as PC

exportToMereological :: PC.PreparedTheory -> String
exportToMereological prepared =
  unlines $
    [ "{" ]
    ++ abbreviationsSection
    ++ ["", "  axioms {", "    metafacts {"]
    ++ map ("      " ++) metafacts
    ++ ["    }", "  }", "}"]
  where
    defs = PC.ptMereologicalOpDefs prepared
    abbreviationsSection =
      [ "  abbreviations {" ]
      ++ map ("    " ++) (map renderDef defs)
      ++ [ "  }," ]

    metafacts =
      let facts = IR.theoryFacts (PC.ptTheory prepared)
      in case [renderMereoExpr me ++ ";" | f <- facts, Just me <- [IR.factMereoExpr f]] of
           [] -> ["/* no translated mereological facts yet */"]
           xs -> L.nub xs

renderDef :: MOD.MereoOpDefEntry -> String
renderDef def =
  MOD.modOpName def
    ++ "(" ++ L.intercalate ", " (MOD.modParams def) ++ ") := "
    ++ renderMereoExpr (MOD.modBody def)
    ++ ";"

renderMereoExpr :: IR.MereoExpr -> String
renderMereoExpr (IR.MSum a b) = "(" ++ renderMereoExpr a ++ " + " ++ renderMereoExpr b ++ ")"
renderMereoExpr (IR.MProd a b) = "(" ++ renderMereoExpr a ++ " × " ++ renderMereoExpr b ++ ")"
renderMereoExpr (IR.MDiff a b) = "(" ++ renderMereoExpr a ++ " - " ++ renderMereoExpr b ++ ")"
renderMereoExpr (IR.MRevDiff a b) = "(" ++ renderMereoExpr a ++ " ⇒ " ++ renderMereoExpr b ++ ")"
renderMereoExpr (IR.MSymDiff a b) = "(" ++ renderMereoExpr a ++ " ∸ " ++ renderMereoExpr b ++ ")"
renderMereoExpr (IR.MVar x) = x
renderMereoExpr IR.MZero = "0"
renderMereoExpr (IR.MAbbrevApp n args) = n ++ "(" ++ L.intercalate ", " (map renderMereoExpr args) ++ ")"
renderMereoExpr (IR.MBoundedSum v lo hi body) =
  "Σ " ++ v ++ " ∈ [" ++ renderMereoExpr lo ++ ", " ++ renderMereoExpr hi ++ "]. " ++ renderMereoExpr body
