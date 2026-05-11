module Eidos.Pipeline.Targets.Mereological.Mereological
  ( exportToMereological
  ) where

import qualified Data.List as L
import qualified Eidos.Pipeline.FromSyntax.IR as IR
import qualified Eidos.Pipeline.IRProcessing.MereologicalOpDefs as MOD
import qualified Eidos.Pipeline.PipelineCore as PC
import qualified Eidos.Pipeline.IRProcessing.SortBounds as SB

univPrefix, propPrefix, minSuffix, maxSuffix :: String
univPrefix = "Univ"
propPrefix = "Pr"
minSuffix = "_Min"
maxSuffix = "_Max"

exportToMereological :: PC.PreparedTheory -> String
exportToMereological prepared =
  unlines $
    [ "{" ]
    ++ signatureSection
    ++ [","]
    ++ abbreviationsSection
    ++ ["", "  axioms {", "    metafacts {"]
    ++ map ("      " ++) metafacts
    ++ ["    }", "  }", "}"]
  where
    th = PC.ptTheory prepared
    defs = PC.ptMereologicalOpDefs prepared
    baseAbbrevs = usedBaseAbbrevDefs prepared defs
    signatureSection =
      [ "  signature {"
      , "    " ++ univPrefix ++ minSuffix ++ " : 𝕌;"
      , "    " ++ univPrefix ++ maxSuffix ++ " : 𝕌;"
      , "    " ++ propPrefix ++ minSuffix ++ " : 𝕌;"
      , "    " ++ propPrefix ++ maxSuffix ++ " : 𝕌;"
      ]
      ++ map (\n -> "    " ++ n ++ " : 𝕌;") (userObjectNames th)
      ++ [ "  }" ]
    abbreviationsSection =
      [ "  abbreviations {" ]
      ++ map ("    " ++) (map renderBaseAbbrevDef baseAbbrevs)
      ++ map ("    " ++) (map renderDef defs)
      ++ [ "  }," ]

    metafacts =
      let facts = IR.theoryFacts (PC.ptTheory prepared)
          translated = [renderMereoExpr me ++ ";" | f <- facts, Just me <- [IR.factMereoExpr f]]
          sortBoundFacts = [ rewriteAxiomName nm ++ " : " ++ renderMereoExpr me ++ ";"
                           | e <- PC.ptSortBounds prepared, (nm, me) <- SB.sbeAxioms e ]
          sortOrderFacts = [ rewriteAxiomName nm ++ " : " ++ renderMereoExpr me ++ ";"
                           | e <- PC.ptSortOrder prepared, (nm, me) <- SB.soeAxioms e ]
          allMetafacts = L.nub (sortBoundFacts ++ sortOrderFacts ++ translated)
      in case allMetafacts of
           [] -> ["/* no translated mereological facts yet */"]
           xs -> xs

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
renderMereoExpr (IR.MVar x) = rewriteSpecialVar x
renderMereoExpr IR.MZero = "0"
renderMereoExpr (IR.MAbbrevApp n args) = n ++ "(" ++ L.intercalate ", " (map renderMereoExpr args) ++ ")"
renderMereoExpr (IR.MBoundedSum v lo hi body) =
  "Σ " ++ v ++ " ∈ [" ++ renderMereoExpr lo ++ ", " ++ renderMereoExpr hi ++ "]. " ++ renderMereoExpr body

rewriteSpecialVar :: String -> String
rewriteSpecialVar n = case n of
  "𝕌#min" -> univPrefix ++ minSuffix
  "𝕌#max" -> univPrefix ++ maxSuffix
  "ℙ#min" -> propPrefix ++ minSuffix
  "ℙ#max" -> propPrefix ++ maxSuffix
  _       -> n

rewriteAxiomName :: String -> String
rewriteAxiomName n = case n of
  "𝕌_ordering" -> univPrefix ++ "_ordering"
  "ℙ_upper"    -> propPrefix ++ "_upper"
  "ℙ_ordering" -> propPrefix ++ "_ordering"
  "ℙ_lower"    -> propPrefix ++ "_lower"
  _            -> n

userObjectNames :: IR.Theory -> [String]
userObjectNames th =
  L.nub
    [ IR.mereoName m
    | IR.EntityMereological m <- IR.theoryObjects th
    , IR.mereoOrigin m == IR.FromSignature
    , IR.mereoKind m == IR.MereologicalEntityKindProposition
        || IR.mereoKind m == IR.MereologicalEntityKindIndividual
        || IR.mereoKind m == IR.MereologicalEntityKindSet
    ]
