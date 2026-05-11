module Eidos.Pipeline.Targets.Mereological.Mereological
  ( exportToMereological
  ) where

import qualified Data.List as L
import qualified Data.Map.Strict as Map
import qualified Eidos.Pipeline.FromSyntax.IR as IR
import qualified Eidos.Pipeline.IRProcessing.MereologicalOpDefs as MOD
import qualified Eidos.Pipeline.PipelineCore as PC
import qualified Eidos.Pipeline.IRProcessing.SortBounds as SB

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
-- separately by 'rewriteSpecialVar'.
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
    ++ mkAbbreviationsSection prepared defs
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
  -- Note: multi-argument functions produce a curried arrow type here.
  -- Eidos SOL functions are single-argument; multi-arg is a known limitation.
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

    -- Emit one 𝕌 per argument plus one for the result.
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

mkAbbreviationsSection :: PC.PreparedTheory -> [MOD.MereoOpDefEntry] -> [String]
mkAbbreviationsSection prepared defs =
  [ "  abbreviations {" ]
  ++ map ("    " ++) (map renderBaseAbbrevDef baseAbbrevs)
  ++ map ("    " ++) (map renderDef defs)
  ++ [ "  }" ]
  where
    baseAbbrevs = usedBaseAbbrevDefs prepared defs

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

    -- All user-written facts (assertions, plain facts, and metafacts in the
    -- input) all become metafacts in the mereological output, just as they
    -- all become axioms in the Lean/Coq output.
    userTranslatedFacts =
      [ f | f <- facts
          , IR.factCategory (IR.factKind f) == IR.FCMereologicalTranslation
          , IR.factSubkind  (IR.factKind f) `elem`
              [ IR.FSTranslationOfFact
              , IR.FSTranslationOfAssertion
              , IR.FSTranslationOfMetafact ] ]
    metafactUserLines =
      [ "mf" ++ show idx ++ " : " ++ renderMereoExprWith nameMap me ++ ";"
      | (idx, f) <- zip [1 :: Int ..] userTranslatedFacts
      , Just me <- [IR.factMereoExpr f] ]

    -- Sort bounds
    sortBoundLines =
      [ rewriteAxiomName nm ++ " : " ++ renderMereoExprWith nameMap me ++ ";"
      | e <- PC.ptSortBounds prepared
      , (nm, me) <- SB.sbeAxioms e ]

    -- Sort ordering
    sortOrderLines =
      [ rewriteAxiomName nm ++ " : " ++ renderMereoExprWith nameMap me ++ ";"
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
      ++ concat [ IR.collectUsedAbbrevNames me
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
              , n <- IR.collectUsedAbbrevNames (IR.abbrevBody ad)
              ]
          acc' = L.nub (acc ++ next)
      in if length acc' == length acc then acc else go acc'

-- ---------------------------------------------------------------------------
-- Rendering abbreviation definitions
-- ---------------------------------------------------------------------------

-- | Render a compiler-internal abbreviation definition.
-- Bodies use only parameter names and special vars (𝕌#min etc.),
-- never entity names, so no entity name map is needed here.
renderBaseAbbrevDef :: IR.AbbrevDef -> String
renderBaseAbbrevDef ad =
  IR.abbrevName ad
    ++ "(" ++ L.intercalate ", " (IR.abbrevParams ad) ++ ") := "
    ++ renderMereoExpr (IR.abbrevBody ad)
    ++ ";"

-- | Render a per-theory mereological operation definition.
renderDef :: MOD.MereoOpDefEntry -> String
renderDef def =
  MOD.modOpName def
    ++ "(" ++ L.intercalate ", " (MOD.modParams def) ++ ") := "
    ++ renderMereoExpr (MOD.modBody def)
    ++ ";"

-- ---------------------------------------------------------------------------
-- MereoExpr rendering
-- ---------------------------------------------------------------------------

-- | Render a 'IR.MereoExpr' using a theory-level name map for variable
-- rewriting.  Pass 'Map.empty' (or use 'renderMereoExpr') when the
-- expression contains only parameter names and special vars.
renderMereoExprWith :: NameMap -> IR.MereoExpr -> String
renderMereoExprWith nm expr = go expr
  where
    go (IR.MSum a b)     = "(" ++ go a ++ " + " ++ go b ++ ")"
    go (IR.MProd a b)    = "(" ++ go a ++ " × " ++ go b ++ ")"
    go (IR.MDiff a b)    = "(" ++ go a ++ " - " ++ go b ++ ")"
    go (IR.MRevDiff a b) = "(" ++ go a ++ " ⇒ " ++ go b ++ ")"
    go (IR.MSymDiff a b) = "(" ++ go a ++ " ∸ " ++ go b ++ ")"
    go (IR.MVar x)       = rewriteVar nm x
    go IR.MZero          = "0"
    go (IR.MAbbrevApp n args) =
      n ++ "(" ++ L.intercalate ", " (map go args) ++ ")"
    go (IR.MBoundedSum v lo hi body) =
      "Σ " ++ v ++ " ∈ [" ++ go lo ++ ", " ++ go hi ++ "]. " ++ go body

-- | Convenience: render without an entity name map (for abbreviation bodies).
renderMereoExpr :: IR.MereoExpr -> String
renderMereoExpr = renderMereoExprWith Map.empty

-- | Rewrite a variable name: entity name map takes priority, then
-- special-var rules, then the name is left unchanged.
rewriteVar :: NameMap -> String -> String
rewriteVar nameMap n =
  case Map.lookup n nameMap of
    Just newName -> newName
    Nothing      -> rewriteSpecialVar n

-- | Rewrite built-in and sort-bound special variable names.
-- Handles @𝕌#min@ → @Univ_Min@, the general @X#min@ → @X_Min@ pattern,
-- and the Unicode-prefix sorts (@ℙ@, @𝔻@).
rewriteSpecialVar :: String -> String
rewriteSpecialVar n = case n of
  "𝕌#min" -> univPrefix ++ minSuffix
  "𝕌#max" -> univPrefix ++ maxSuffix
  "ℙ#min" -> propPrefix ++ minSuffix
  "ℙ#max" -> propPrefix ++ maxSuffix
  "𝔻#min" -> domPrefix  ++ minSuffix
  "𝔻#max" -> domPrefix  ++ maxSuffix
  _ | Just base <- stripHashSuffix "#min" n -> base ++ minSuffix
    | Just base <- stripHashSuffix "#max" n -> base ++ maxSuffix
  _ -> n
  where
    stripHashSuffix suf str =
      let (front, back) = splitAt (length str - length suf) str
      in if back == suf then Just front else Nothing

-- | Rewrite Unicode-prefixed axiom names.
-- Applies the same Unicode→ASCII prefix substitutions used for variables
-- so that axiom names like @𝕌_ordering@ become @Univ_ordering@.
rewriteAxiomName :: String -> String
rewriteAxiomName n
  | Just rest <- L.stripPrefix "𝕌" n = univPrefix ++ rest
  | Just rest <- L.stripPrefix "ℙ" n = propPrefix ++ rest
  | Just rest <- L.stripPrefix "𝔻" n = domPrefix  ++ rest
  | otherwise                         = n
