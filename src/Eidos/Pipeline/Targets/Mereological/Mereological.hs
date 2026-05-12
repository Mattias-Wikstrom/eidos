module Eidos.Pipeline.Targets.Mereological.Mereological
  ( exportToMereological
  ) where

import qualified Data.List as L
import qualified Data.Map.Strict as Map
import qualified Eidos.Pipeline.FromSyntax.IR as IR
import qualified Eidos.Pipeline.IRProcessing.MereologicalOpDefs as MOD
import qualified Eidos.Pipeline.PipelineCore as PC
import qualified Eidos.Pipeline.IRProcessing.SortBounds as SB
import           Eidos.Pipeline.Targets.Mereological.MereoExpr
import           Eidos.Pipeline.Targets.Mereological.MkAxiomSets
                   (irMereoExprToMereo, abbrevBodyToMereo)

-- ---------------------------------------------------------------------------
-- Name-prefix constants
-- ---------------------------------------------------------------------------

-- | Replaces @𝕌@ in output names (the universe sort changes identity).
univPrefix :: String
univPrefix = "Univ"

-- | Replaces @ℙ@ in output names.
propPrefix :: String
propPrefix = "Pr"

-- | Replaces @𝔻@ in output names.
domPrefix :: String
domPrefix = "Dom"

-- | Prefix applied to all function and relation declarations.
-- Needed because the mereological output uses 𝕌-typed SOL functions
-- for everything, so lowercase FOL names must be uppercased, and
-- all names need to be syntactically distinguishable from objects.
fnPrefix :: String
fnPrefix = "Fn_"

-- | Prefix applied to all mereological object declarations.
-- Guarantees that names of sort 𝕌 start with an uppercase letter,
-- as required by Eidos syntax.
obPrefix :: String
obPrefix = "Ob_"

minSuffix, maxSuffix :: String
minSuffix = "_Min"
maxSuffix = "_Max"

-- ---------------------------------------------------------------------------
-- Entity name map
-- ---------------------------------------------------------------------------

-- | Maps internal entity names to their mereological output names.
-- Functions and relations receive 'fnPrefix'; mereological objects receive
-- 'obPrefix'.  Special bound variables (@𝕌#min@ etc.) are handled
-- separately by 'MkAxiomSets.rewriteSpecialVar'.
type NameMap = Map.Map String String

buildNameMap :: IR.Theory -> NameMap
buildNameMap th = Map.fromList $
  -- User-declared FOL and SOL functions
  [ (IR.funcName f, fnPrefix ++ IR.funcName f)
  | IR.EntityFunction f <- IR.theoryObjects th
  , IR.funcOrigin f == IR.FromSignature
  , IR.funcKind f `elem` [ IR.FunctionKindFOLFunctionFromTheory
                          , IR.FunctionKindSOLFunctionFromTheory ]
  ] ++
  -- User-declared relations
  [ (IR.relName r, fnPrefix ++ IR.relName r)
  | IR.EntityRelation r <- IR.theoryObjects th
  , IR.relOrigin r == IR.FromSignature
  ] ++
  -- User-declared mereological objects (𝕌, ℙ, individual, set)
  [ (IR.mereoName m, obPrefix ++ IR.mereoName m)
  | IR.EntityMereological m <- IR.theoryObjects th
  , IR.mereoOrigin m == IR.FromSignature
  , IR.mereoKind m `elem` [ IR.MereologicalEntityKindMereological
                           , IR.MereologicalEntityKindProposition
                           , IR.MereologicalEntityKindIndividual
                           , IR.MereologicalEntityKindSet ]
  ]

-- ---------------------------------------------------------------------------
-- Export entry point
-- ---------------------------------------------------------------------------

exportToMereological :: PC.PreparedTheory -> String
exportToMereological prepared =
  unlines $
    [ "{" ]
    ++ mkSignatureSection th nameMap
    ++ [","]
    ++ mkAbbreviationsSection prepared nameMap defs
    ++ [","]
    ++ mkAxiomsSection prepared nameMap
    ++ ["}"]
  where
    th      = PC.ptTheory prepared
    defs    = PC.ptMereologicalOpDefs prepared
    nameMap = buildNameMap th

-- ---------------------------------------------------------------------------
-- Signature section
-- ---------------------------------------------------------------------------

mkSignatureSection :: IR.Theory -> NameMap -> [String]
mkSignatureSection th _nameMap =
  [ "  signature {" ]
  -- Built-in universe bounds (𝕌_Min / 𝕌_Max → Univ_Min / Univ_Max)
  ++ [ "    " ++ univPrefix ++ minSuffix ++ " : 𝕌;" ]
  ++ [ "    " ++ univPrefix ++ maxSuffix ++ " : 𝕌;" ]
  -- Built-in proposition bounds (ℙ_Min / ℙ_Max → Pr_Min / Pr_Max)
  ++ [ "    " ++ propPrefix ++ minSuffix ++ " : 𝕌;" ]
  ++ [ "    " ++ propPrefix ++ maxSuffix ++ " : 𝕌;" ]
  -- Domain sort bounds (𝔻_Min / 𝔻_Max → Dom_Min / Dom_Max), if used
  ++ [ "    " ++ domPrefix ++ minSuffix ++ " : 𝕌;" | IR.theoryUsesDomain th ]
  ++ [ "    " ++ domPrefix ++ maxSuffix ++ " : 𝕌;" | IR.theoryUsesDomain th ]
  -- User sort bounds: S_Min, S_Max  (already uppercase, no prefix needed)
  ++ concatMap mkSortLimits userSorts
  -- Functions: Fn_f : 𝕌 → … → 𝕌  (one 𝕌 per argument plus one for result)
  ++ map mkFunctionDecl userFunctions
  -- Relations: Fn_R : 𝕌 → … → 𝕌
  ++ map mkRelationDecl userRelations
  -- Mereological objects: Ob_X : 𝕌
  ++ map mkObjectDecl userObjects
  ++ [ "  }" ]
  where
    userSorts =
      [ s | IR.EntitySort s <- IR.theoryObjects th
          , IR.sortKind s == IR.SortKindFromSignature ]

    userFunctions =
      [ f | IR.EntityFunction f <- IR.theoryObjects th
          , IR.funcOrigin f == IR.FromSignature
          , IR.funcKind f `elem` [ IR.FunctionKindFOLFunctionFromTheory
                                 , IR.FunctionKindSOLFunctionFromTheory ] ]

    userRelations =
      [ r | IR.EntityRelation r <- IR.theoryObjects th
          , IR.relOrigin r == IR.FromSignature ]

    userObjects =
      [ m | IR.EntityMereological m <- IR.theoryObjects th
          , IR.mereoOrigin m == IR.FromSignature
          , IR.mereoKind m `elem` [ IR.MereologicalEntityKindMereological
                                  , IR.MereologicalEntityKindProposition
                                  , IR.MereologicalEntityKindIndividual
                                  , IR.MereologicalEntityKindSet ] ]

    mkSortLimits s =
      [ "    " ++ IR.sortName s ++ minSuffix ++ " : 𝕌;"
      , "    " ++ IR.sortName s ++ maxSuffix ++ " : 𝕌;"
      ]

    mkFunctionDecl f =
      let arity = length (IR.funcArgSorts f)
      in "    " ++ fnPrefix ++ IR.funcName f ++ " : "
           ++ L.intercalate " → " (replicate (arity + 1) "𝕌") ++ ";"

    mkRelationDecl r =
      let arity = length (IR.relArgSorts r)
      in "    " ++ fnPrefix ++ IR.relName r ++ " : "
           ++ L.intercalate " → " (replicate (arity + 1) "𝕌") ++ ";"

    mkObjectDecl m =
      "    " ++ obPrefix ++ IR.mereoName m ++ " : 𝕌;"

-- ---------------------------------------------------------------------------
-- Abbreviations section
-- ---------------------------------------------------------------------------

mkAbbreviationsSection :: PC.PreparedTheory -> NameMap -> [MOD.MereoOpDefEntry] -> [String]
mkAbbreviationsSection prepared nameMap defs =
  [ "  abbreviations {" ]
  ++ map ("    " ++) (map renderBaseAbbrevDef baseAbbrevs)
  ++ map ("    " ++) (map renderDef defs)
  ++ [ "  }" ]
  where
    baseAbbrevs = usedBaseAbbrevDefs prepared nameMap defs

-- ---------------------------------------------------------------------------
-- Axioms section
-- ---------------------------------------------------------------------------

mkAxiomsSection :: PC.PreparedTheory -> NameMap -> [String]
mkAxiomsSection prepared nameMap =
  [ "  axioms {" ]
  ++ metafactBlock
  ++ [ "  }" ]
  where
    facts = IR.theoryFacts (PC.ptTheory prepared)

    userTranslatedFacts =
      [ f | f <- facts
          , IR.factCategory (IR.factKind f) == IR.FCMereologicalTranslation
          , IR.factSubkind  (IR.factKind f) `elem`
              [ IR.FSTranslationOfFact
              , IR.FSTranslationOfAssertion
              , IR.FSTranslationOfMetafact ] ]
    metafactUserLines =
      [ "mf" ++ show idx ++ " : "
          ++ renderMereoExpr (irMereoExprToMereo nameMap me) ++ ";"
      | (idx, f) <- zip [1 :: Int ..] userTranslatedFacts
      , Just me <- [IR.factMereoExpr f] ]

    sortBoundLines =
      [ rewriteAxiomName nm ++ " : "
          ++ renderMereoExpr (irMereoExprToMereo nameMap me) ++ ";"
      | e <- PC.ptSortBounds prepared
      , (nm, me) <- SB.sbeAxioms e ]

    sortOrderLines =
      [ rewriteAxiomName nm ++ " : "
          ++ renderMereoExpr (irMereoExprToMereo nameMap me) ++ ";"
      | e <- PC.ptSortOrder prepared
      , (nm, me) <- SB.soeAxioms e ]

    allMetafactLines = L.nub (sortBoundLines ++ sortOrderLines ++ metafactUserLines)

    metafactBlock =
      [ "    metafacts {" ]
      ++ (if null allMetafactLines
          then [ "      /* no metafacts */" ]
          else map ("      " ++) allMetafactLines)
      ++ [ "    }" ]

-- ---------------------------------------------------------------------------
-- Used base abbreviation definitions
-- ---------------------------------------------------------------------------

usedBaseAbbrevDefs :: PC.PreparedTheory -> NameMap -> [MOD.MereoOpDefEntry] -> [IR.AbbrevDef]
usedBaseAbbrevDefs prepared nameMap defs =
  [ ad
  | ad <- IR.allAbbrevDefs
  , IR.abbrevName ad `elem` closure
  ]
  where
    facts = IR.theoryFacts (PC.ptTheory prepared)
    seedNames =
      -- Abbreviations used in per-theory op definitions
      concatMap (collectUsedAbbrevNames . abbrevBodyToMereo . MOD.modBody) defs
      -- Abbreviations used in translated facts (structural nodes included)
      ++ concat [ collectUsedAbbrevNames (irMereoExprToMereo nameMap me)
                | f <- facts
                , Just me <- [IR.factMereoExpr f] ]
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
              , n <- collectUsedAbbrevNames (abbrevBodyToMereo (IR.abbrevBody ad))
              ]
          acc' = L.nub (acc ++ next)
      in if length acc' == length acc then acc else go acc'

-- ---------------------------------------------------------------------------
-- Rendering abbreviation definitions
-- ---------------------------------------------------------------------------

renderBaseAbbrevDef :: IR.AbbrevDef -> String
renderBaseAbbrevDef ad =
  IR.abbrevName ad
    ++ "(" ++ L.intercalate ", " (IR.abbrevParams ad) ++ ") := "
    ++ renderMereoExpr (abbrevBodyToMereo (IR.abbrevBody ad))
    ++ ";"

renderDef :: MOD.MereoOpDefEntry -> String
renderDef def =
  MOD.modOpName def
    ++ "(" ++ L.intercalate ", " (MOD.modParams def) ++ ") := "
    ++ renderMereoExpr (abbrevBodyToMereo (MOD.modBody def))
    ++ ";"

-- ---------------------------------------------------------------------------
-- Axiom name rewriting
-- ---------------------------------------------------------------------------

-- | Rewrite Unicode-prefixed axiom names to ASCII output form.
rewriteAxiomName :: String -> String
rewriteAxiomName n
  | Just rest <- L.stripPrefix "𝕌" n = univPrefix ++ rest
  | Just rest <- L.stripPrefix "ℙ" n = propPrefix ++ rest
  | Just rest <- L.stripPrefix "𝔻" n = domPrefix  ++ rest
  | otherwise                         = n
