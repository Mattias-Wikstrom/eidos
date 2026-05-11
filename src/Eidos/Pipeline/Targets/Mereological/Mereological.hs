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
    baseAbbrevs = usedBaseAbbrevDefs prepared defs
    abbreviationsSection =
      [ "  abbreviations {" ]
      ++ map ("    " ++) (map renderBaseAbbrevDef baseAbbrevs)
      ++ map ("    " ++) (map renderDef defs)
      ++ [ "  }," ]

    metafacts =
      let facts = IR.theoryFacts (PC.ptTheory prepared)
      in case [renderMereoExpr me ++ ";" | f <- facts, Just me <- [IR.factMereoExpr f]] of
           [] -> ["/* no translated mereological facts yet */"]
           xs -> L.nub xs

usedBaseAbbrevDefs :: PC.PreparedTheory -> [MOD.MereoOpDefEntry] -> [IR.AbbrevDef]
usedBaseAbbrevDefs prepared defs =
  [ ad
  | ad <- IR.allAbbrevDefs
  , IR.abbrevName ad `elem` closure
  ]
  where
    facts = IR.theoryFacts (PC.ptTheory prepared)
    seedNames =
      concatMap (IR.collectUsedAbbrevNames . MOD.modBody) defs
      ++ concat [ IR.collectUsedAbbrevNames me | f <- facts, Just me <- [IR.factMereoExpr f] ]
    closure = closeOverAbbrevDeps (L.nub seedNames)

closeOverAbbrevDeps :: [String] -> [String]
closeOverAbbrevDeps seed = go (L.nub seed)
  where
    go acc =
      let next =
            L.nub
              [ n
              | ad <- IR.allAbbrevDefs
              , IR.abbrevName ad `elem` acc
              , n <- IR.collectUsedAbbrevNames (IR.abbrevBody ad)
              ]
          acc' = L.nub (acc ++ next)
      in if length acc' == length acc then acc else go acc'

renderBaseAbbrevDef :: IR.AbbrevDef -> String
renderBaseAbbrevDef ad =
  IR.abbrevName ad
    ++ "(" ++ L.intercalate ", " (IR.abbrevParams ad) ++ ") := "
    ++ renderMereoExpr (IR.abbrevBody ad)
    ++ ";"

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
