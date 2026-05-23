-- | Export an Eidos theory to Coq using the EidosRuntime structures.
--
-- Unlike the 'CoqProps' backend, which flattens everything into bare
-- @MereologicalObject@ axioms, this backend reads the IR's sort, function,
-- and relation objects directly and emits typed EidosRuntime declarations:
--
-- * Universe    → @Axiom univ : EidosUniverse.@ + @Definition 𝕌\/ℙ@
-- * User sorts  → @Axiom S : EidosSort.@ + @OrdinarySortWithinUniverse@
-- * SOL fns     → @Axiom F : SOLFunctionOneArg dom cod.@
-- * FOL 1-arg   → @Axiom f : FOLFunctionOneArg dom cod.@
-- * FOL n-arg   → @Axiom f_dom : EidosSort.@ + @Axiom f : FOLFunction n doms cod f_dom.@
-- * Relations   → @Axiom R_dom : EidosSort.@ + @Axiom R : FOLRelation n doms R_dom.@
-- * Objects     → @Axiom x : MereologicalObjectOfSort S.@ or @IndividualOfSort S@
-- * User facts  → @Axiom ax1 : …@ (mereo expression with @sMin@\/@sMax@ projections)
--
-- Sort-structure facts, function-connection\/adjunction\/decomposition facts,
-- and all other derived axioms emitted by the flat backend are suppressed:
-- their logical content is now encoded in the EidosRuntime structure fields.
module Eidos.Pipeline.Targets.CoqRuntime.CoqRuntime
  ( renderCoqRuntime
  ) where

import qualified Eidos.Pipeline.FromSyntax.IR              as IR
import           Eidos.Pipeline.PipelineCore                (PreparedTheory (..))
import qualified Eidos.Pipeline.IRProcessing.NamingConventions as NC
import qualified Eidos.Pipeline.Targets.CoqProps.CoqExpr   as CE
import           Data.Char   (isAlphaNum)
import           Data.List   (intercalate)
import           Data.Maybe  (fromMaybe, isJust)
import qualified Data.Set    as Set

-- ---------------------------------------------------------------------------
-- Name sanitisation (mirrors CoqProps.MkAxiomSets)
-- ---------------------------------------------------------------------------

sanitize :: String -> String
sanitize = concatMap sc
  where
    sc c
      | isAlphaNum c || c `elem` "_'." = [c]
      | otherwise = case c of
          '#'      -> "_"
          '+'      -> "Plus"
          '×'      -> "Times"
          '\x2212' -> "Minus"
          '-'      -> "Minus"
          '⇒'      -> "Arrow"
          '∸'      -> "SDiff"
          _        -> "_"

-- | Coq identifier for a sort (sanitises the raw IR sort name).
sortId :: IR.Sort -> String
sortId = sanitize . NC.sanitizeHash . IR.sortName

-- ---------------------------------------------------------------------------
-- Runtime name resolver for MereoExpr
-- ---------------------------------------------------------------------------

stripSuffix :: String -> String -> Maybe String
stripSuffix suf s
  | length s > length suf
  , drop (length s - length suf) s == suf
  = Just (take (length s - length suf) s)
  | otherwise = Nothing

-- | Translate sort-limit names to EidosSort projections:
-- @\"S_Min\"@ → @\"(sMin S)\"@, @\"S_Max\"@ → @\"(sMax S)\"@.
-- All other names go through 'sanitize'.
runtimeResolve :: String -> String
runtimeResolve n
  | Just sn <- stripSuffix "_Min" n = "(sMin " ++ sanitize sn ++ ")"
  | Just sn <- stripSuffix "_Max" n = "(sMax " ++ sanitize sn ++ ")"
  | otherwise                       = sanitize n

-- | Translate a 'IR.MereoExpr' to a 'CE.CoqExpr' using the runtime resolver.
mereoToCoq :: IR.MereoExpr -> CE.CoqExpr
mereoToCoq = go
  where
    go (IR.MSum a b)     = CE.CConj   (go a) (go b)
    go (IR.MProd a b)    = CE.CDisj   (go a) (go b)
    go (IR.MDiff a b)    = CE.CImpl   (go b) (go a)
    go (IR.MRevDiff a b) = CE.CImpl   (go a) (go b)
    go (IR.MSymDiff a b) = CE.CBicond (go a) (go b)
    go (IR.MVar n)       = CE.CVar (runtimeResolve n)
    go IR.MZero          = CE.CTop
    go (IR.MAbbrevApp "ProjectIntoInterval" [x, lo, hi]) =
      CE.CProjectIntoInterval (go x) (go lo) (go hi)
    go (IR.MAbbrevApp name args) =
      CE.CApp (CE.CVar name) (map go args)
    go (IR.MFOLApp name args) =
      CE.CApp (CE.CVar (runtimeResolve name)) (map go args)
    go (IR.MUnboundedSum var body) =
      CE.CForall var CE.CProp (go body)
    go (IR.MBoundedSum var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) ->
          CE.CBoundedForall var (runtimeResolve loN) (runtimeResolve hiN) (go body)
        _ ->
          CE.CForall var CE.CProp
            (CE.CImpl (CE.CApp (CE.CVar "IsWithinBounds") [go lo, go hi, CE.CVar var])
                      (go body))
    go (IR.MBoundedProduct var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) ->
          CE.CBoundedExists var (runtimeResolve loN) (runtimeResolve hiN) (go body)
        _ ->
          CE.CExists var CE.CProp
            (CE.CConj (CE.CApp (CE.CVar "IsWithinBounds") [go lo, go hi, CE.CVar var])
                      (go body))
    go (IR.MSumOfIndividuals var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) ->
          CE.CForallIndividuals var (runtimeResolve loN) (runtimeResolve hiN) (go body)
        _ ->
          CE.CForall var CE.CProp
            (CE.CImpl (CE.CApp (CE.CVar "IsIndividual") [go lo, go hi, CE.CVar var])
                      (go body))
    go (IR.MProductOfIndividuals var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) ->
          CE.CExistsIndividuals var (runtimeResolve loN) (runtimeResolve hiN) (go body)
        _ ->
          CE.CExists var CE.CProp
            (CE.CConj (CE.CApp (CE.CVar "IsIndividual") [go lo, go hi, CE.CVar var])
                      (go body))

-- | Render an abbreviation body without name resolution (params are verbatim).
abbrevBodyToCoq :: IR.MereoExpr -> CE.CoqExpr
abbrevBodyToCoq = go
  where
    go (IR.MSum a b)     = CE.CConj   (go a) (go b)
    go (IR.MProd a b)    = CE.CDisj   (go a) (go b)
    go (IR.MDiff a b)    = CE.CImpl   (go b) (go a)
    go (IR.MRevDiff a b) = CE.CImpl   (go a) (go b)
    go (IR.MSymDiff a b) = CE.CBicond (go a) (go b)
    go (IR.MVar n)       = CE.CVar n
    go IR.MZero          = CE.CTop
    go (IR.MAbbrevApp "ProjectIntoInterval" [x, lo, hi]) =
      CE.CProjectIntoInterval (go x) (go lo) (go hi)
    go (IR.MAbbrevApp name args) = CE.CApp (CE.CVar name) (map go args)
    go (IR.MFOLApp name args)    = CE.CApp (CE.CVar name) (map go args)
    go (IR.MUnboundedSum var body) =
      CE.CForall var CE.CProp (go body)
    go (IR.MBoundedSum var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) -> CE.CBoundedForall var loN hiN (go body)
        _ -> CE.CForall var CE.CProp
               (CE.CImpl (CE.CApp (CE.CVar "IsWithinBounds") [go lo, go hi, CE.CVar var]) (go body))
    go (IR.MBoundedProduct var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) -> CE.CBoundedExists var loN hiN (go body)
        _ -> CE.CExists var CE.CProp
               (CE.CConj (CE.CApp (CE.CVar "IsWithinBounds") [go lo, go hi, CE.CVar var]) (go body))
    go (IR.MSumOfIndividuals var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) -> CE.CForallIndividuals var loN hiN (go body)
        _ -> CE.CForall var CE.CProp
               (CE.CImpl (CE.CApp (CE.CVar "IsIndividual") [go lo, go hi, CE.CVar var]) (go body))
    go (IR.MProductOfIndividuals var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) -> CE.CExistsIndividuals var loN hiN (go body)
        _ -> CE.CExists var CE.CProp
               (CE.CConj (CE.CApp (CE.CVar "IsIndividual") [go lo, go hi, CE.CVar var]) (go body))

-- ---------------------------------------------------------------------------
-- Object suppression
-- ---------------------------------------------------------------------------

-- | Names that must not be re-declared in runtime output because they are
-- either built-in constants or owned by a function\/relation structure.
suppressedNames :: IR.Theory -> Set.Set String
suppressedNames theory = Set.fromList (builtins ++ owned)
  where
    builtins =
      ["𝕌_Min", "𝕌_Max", "ℙ_Min", "ℙ_Max", "𝔻_Min", "𝔻_Max", "⊤", "⊥"]
    allFunctions = [f | IR.EntityFunction f <- IR.theoryObjects theory]
    allRelations = [r | IR.EntityRelation r <- IR.theoryObjects theory]
    owned =
      concatMap funOwned allFunctions ++
      concatMap relOwned allRelations
    funOwned f =
      map IR.mereoName (IR.funcArgObjects f)
      ++ foldMap (\o -> [IR.mereoName o]) (IR.funcResObject f)
      ++ foldMap (\o -> [IR.mereoName o]) (IR.funcArgument f)
    relOwned r =
      map IR.mereoName (IR.relArgObjects r)
      ++ [IR.mereoName (IR.relArgument r), IR.mereoName (IR.relAssociatedSet r)]

-- | True for mereological objects that were explicitly declared by the user.
isUserObject :: Set.Set String -> IR.MereologicalObject -> Bool
isUserObject suppressed m =
  IR.mereoKind m `notElem`
    [ IR.MereologicalEntityKindUpperLimitForSort
    , IR.MereologicalEntityKindLowerLimitForSort
    , IR.MereologicalEntityKindResultOfSOLFunction
    , IR.MereologicalEntityKindArgumentOfSOLFunction
    , IR.MereologicalEntityKindRelationFromReflection
    ]
  && IR.mereoName m `Set.notMember` suppressed

-- ---------------------------------------------------------------------------
-- Fin.t sort family
-- ---------------------------------------------------------------------------

-- | Generate @fun (i : Fin.t n) => …@ that selects a sort per Fin index.
finSortFamily :: Int -> [String] -> String
finSortFamily n names
  | allSame names = "fun _ : Fin.t " ++ show n ++ " => " ++ head names
  | otherwise     = "fun i : Fin.t " ++ show n ++ " => " ++ matchExpr names
  where
    allSame []     = True
    allSame (x:xs) = all (== x) xs

    matchExpr ns = "match i with " ++ intercalate " | " (cases ns) ++ " end"

    -- Build match arms; the last arm always uses a wildcard.
    cases [_]      = ["_ => " ++ head names]
    cases [a, b]   = ["Fin.F1 => " ++ a, "_ => " ++ b]
    cases (a:rest) =
      ("Fin.F1 => " ++ a)
      : zipWith (\k s -> finPat k ++ " => " ++ s) [1 .. length rest - 1] (init rest)
      ++ ["_ => " ++ last rest]
    cases [] = []

    finPat 0 = "Fin.F1"
    finPat 1 = "Fin.FS Fin.F1"
    finPat k = "Fin.FS (" ++ finPat (k - 1) ++ ")"

-- ---------------------------------------------------------------------------
-- Main renderer
-- ---------------------------------------------------------------------------

renderCoqRuntime :: PreparedTheory -> String
renderCoqRuntime pt = unlines $ concat
  [ preamble
  , universeDecls
  , if IR.theoryUsesDomain theory then domainDecls else []
  , concatMap renderSort userSorts
  , concatMap renderSOLFn    solFunctions
  , concatMap renderFOL1Fn   folSingleFns
  , concatMap renderFOLNFn   folMultiFns
  , concatMap renderRelation userRelations
  , concatMap renderIdentityRelation identityRelations
  , concatMap renderObject   userObjects
  , concatMap renderUserAbbrev (ptUserAbbrevDefs pt)
  , renderUserFacts userFacts
  ]
  where
    theory     = ptTheory pt
    suppressed = suppressedNames theory

    preamble =
      [ "(* Generated by Eidos compiler *)"
      , "(* Theory: " ++ IR.theoryFullyQualifiedName theory ++ " *)"
      , ""
      , "Require Import EidosRuntime."
      , ""
      ]

    universeDecls =
      [ "Axiom univ : EidosUniverse."
      , "Definition 𝕌 : EidosSort := universeSort univ."
      , "Definition ℙ : EidosSort := propSort univ."
      , "Definition 𝕌_ops : MereologicalOps 𝕌 := canonicalMereologicalOps 𝕌."
      , ""
      ]

    domainDecls =
      [ "Axiom 𝔻 : EidosSort."
      , "Axiom 𝔻_sub_univ : OrdinarySortWithinUniverse 𝔻 univ."
      , ""
      ]

    userSorts =
      [ s | IR.EntitySort s <- IR.theoryObjects theory
          , IR.sortKind s `elem`
              [IR.SortKindFromSignature, IR.SortKindFromReflection] ]

    solFunctions = IR.theorySOLFunctions theory
    allFOL       = IR.theoryFOLFunctions theory
    folSingleFns = filter (\f -> length (IR.funcArgSorts f) == 1) allFOL
    folMultiFns  = filter (\f -> length (IR.funcArgSorts f) >  1) allFOL

    userRelations = [r | IR.EntityRelation r <- IR.theoryObjects theory]
    identityRelations = [(sn, NC.sortIdentity sn) | s <- userSorts, let sn = sortId s]

    userObjects =
      [ m | IR.EntityMereological m <- IR.theoryObjects theory
          , isUserObject suppressed m ]

    -- Only mereological-translation facts (and implicit merges with a mereo
    -- expression) are emitted; sort-structure and function-connection facts
    -- are suppressed because their content lives in the structure fields.
    userFacts =
      filter (isJust . IR.factMereoExpr)
        [ f | f <- IR.theoryFacts theory
            , IR.factCategory (IR.factKind f) `elem`
                [IR.FCMereologicalTranslation, IR.FCImplicitMerge] ]

    -- Sort ------------------------------------------------------------------
    renderSort s =
      let sn = sortId s
      in [ "Axiom " ++ sn ++ " : EidosSort."
         , "Axiom " ++ sn ++ "_sub_univ : OrdinarySortWithinUniverse " ++ sn ++ " univ."
         , ""
         ]

    -- SOL function ----------------------------------------------------------
    renderSOLFn f =
      let fn  = sanitize (IR.funcName f)
          dom = sortId (head (IR.funcArgSorts f))
          cod = sortId (IR.funcResSort f)
      in [ "Axiom " ++ fn ++ " : SOLFunctionOneArg " ++ dom ++ " " ++ cod ++ "."
         , ""
         ]

    -- FOL 1-argument function -----------------------------------------------
    renderFOL1Fn f =
      let fn  = sanitize (IR.funcName f)
          dom = sortId (head (IR.funcArgSorts f))
          cod = sortId (IR.funcResSort f)
      in [ "Axiom " ++ fn ++ " : FOLFunctionOneArg " ++ dom ++ " " ++ cod ++ "."
         , ""
         ]

    -- FOL n-argument function (n > 1) ---------------------------------------
    renderFOLNFn f =
      let fn    = sanitize (IR.funcName f)
          domS  = fromMaybe
                    (error $ "renderFOLNFn: no domain sort for " ++ IR.funcName f)
                    (IR.funcDomain f)
          domSN = sortId domS
          n     = length (IR.funcArgSorts f)
          aNms  = map sortId (IR.funcArgSorts f)
          cod   = sortId (IR.funcResSort f)
      in [ "Axiom " ++ domSN ++ " : EidosSort."
         , "Axiom " ++ domSN ++ "_sub_univ : OrdinarySortWithinUniverse " ++ domSN ++ " univ."
         , "Axiom " ++ fn ++ " : FOLFunction " ++ show n
             ++ " (" ++ finSortFamily n aNms ++ ") " ++ cod ++ " " ++ domSN ++ "."
         , ""
         ]

    -- Relation --------------------------------------------------------------
    renderRelation r =
      let rn    = sanitize (IR.relName r)
          domSN = sortId (IR.relDomain r)
          n     = length (IR.relArgSorts r)
          aNms  = map sortId (IR.relArgSorts r)
      in [ "Axiom " ++ domSN ++ " : EidosSort."
         , "Axiom " ++ domSN ++ "_sub_univ : OrdinarySortWithinUniverse " ++ domSN ++ " univ."
         , "Axiom " ++ rn ++ " : FOLRelation " ++ show n
             ++ " (" ++ finSortFamily n aNms ++ ") " ++ domSN ++ "."
         , ""
         ]

    -- Per-sort identity relations -------------------------------------------
    renderIdentityRelation (sn, rn) =
      [ "Axiom " ++ rn ++ "_dom : EidosSort."
      , "Axiom " ++ rn ++ "_dom_sub_univ : OrdinarySortWithinUniverse " ++ rn ++ "_dom univ."
      , "Axiom " ++ rn ++ " : FOLRelation 2 (fun _ : Fin.t 2 => " ++ sn ++ ") " ++ rn ++ "_dom."
      , ""
      ]

    -- Mereological object / individual --------------------------------------
    renderObject m =
      let mn = sanitize (IR.mereoName m)
          sn = sortId (IR.mereoSort m)
          ty = case IR.mereoKind m of
                 IR.MereologicalEntityKindIndividual -> "IndividualOfSort " ++ sn
                 _                                   -> "MereologicalObjectOfSort " ++ sn
      in [ "Axiom " ++ mn ++ " : " ++ ty ++ "." ]

    -- User abbreviation -----------------------------------------------------
    renderUserAbbrev ad =
      let nm     = IR.abbrevName ad
          params = IR.abbrevParams ad
          expr   = CE.renderCoqExpr (abbrevBodyToCoq (IR.abbrevBody ad))
      in [ "Definition " ++ nm
             ++ " " ++ unwords ["(" ++ p ++ " : MereologicalObject)" | p <- params]
             ++ " : MereologicalObject := " ++ expr ++ "."
         , ""
         ]

    -- User facts ------------------------------------------------------------
    renderUserFacts facts = concatMap renderFact (zip [1 :: Int ..] facts)

    renderFact (idx, f) =
      case IR.factMereoExpr f of
        Nothing -> []
        Just me ->
          let nm   = "ax" ++ show idx
              expr = CE.renderCoqExpr (mereoToCoq me)
          in [ "Axiom " ++ nm ++ " : " ++ expr ++ "." ]
