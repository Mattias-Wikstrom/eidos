-- | Export an Eidos theory to Lean 4 using the EidosRuntime structures.
--
-- Mirrors 'Eidos.Pipeline.Targets.CoqRuntime.CoqRuntime' for Lean 4 output.
-- Sorts, functions, and relations are declared using the typed EidosRuntime
-- structures rather than being flattened into bare @MereologicalObject@ axioms.
-- Sort-limit names in user-fact expressions are translated to dot-projection
-- notation: @\"S_Min\"@ → @\"S.Min\"@, @\"S_Max\"@ → @\"S.Max\"@.
module Eidos.Pipeline.Targets.LeanRuntime.LeanRuntime
  ( renderLeanRuntime
  ) where

import qualified Eidos.Pipeline.FromSyntax.IR              as IR
import           Eidos.Pipeline.PipelineCore                (PreparedTheory (..))
import qualified Eidos.Pipeline.IRProcessing.NamingConventions as NC
import qualified Eidos.Pipeline.Targets.LeanProps.LeanExpr as LE
import           Data.List   (intercalate)
import           Data.Maybe  (fromMaybe, isJust)
import qualified Data.Set    as Set

-- ---------------------------------------------------------------------------
-- Name sanitisation
-- ---------------------------------------------------------------------------

-- | Lean 4 accepts Unicode letters, so we only need to convert @#@ → @_@.
sanitize :: String -> String
sanitize = NC.sanitizeHash

-- | Lean identifier for a sort.
sortId :: IR.Sort -> String
sortId = sanitize . IR.sortName

-- ---------------------------------------------------------------------------
-- Runtime name resolver for MereoExpr
-- ---------------------------------------------------------------------------

stripSuffix :: String -> String -> Maybe String
stripSuffix suf s
  | length s > length suf
  , drop (length s - length suf) s == suf
  = Just (take (length s - length suf) s)
  | otherwise = Nothing

-- | Translate sort-limit names to EidosSort field access:
-- @\"S_Min\"@ → @\"S.Min\"@, @\"S_Max\"@ → @\"S.Max\"@.
-- All other names go through 'sanitize'.
runtimeResolve :: String -> String
runtimeResolve n
  | Just sn <- stripSuffix "_Min" n = sanitize sn ++ ".Min"
  | Just sn <- stripSuffix "_Max" n = sanitize sn ++ ".Max"
  | otherwise                       = sanitize n

-- | Translate a 'IR.MereoExpr' to a 'LE.LeanExpr' using the runtime resolver.
mereoToLean :: IR.MereoExpr -> LE.LeanExpr
mereoToLean = go
  where
    go (IR.MSum a b)     = LE.LConj   (go a) (go b)
    go (IR.MProd a b)    = LE.LDisj   (go a) (go b)
    go (IR.MDiff a b)    = LE.LImpl   (go b) (go a)
    go (IR.MRevDiff a b) = LE.LImpl   (go a) (go b)
    go (IR.MSymDiff a b) = LE.LBicond (go a) (go b)
    go (IR.MVar n)       = LE.LVar (runtimeResolve n)
    go IR.MZero          = LE.LTop
    go (IR.MAbbrevApp "ProjectIntoInterval" [x, lo, hi]) =
      LE.LProjectIntoInterval (go x) (go lo) (go hi)
    go (IR.MAbbrevApp name args) =
      LE.LApp (LE.LVar name) (map go args)
    go (IR.MFOLApp name args) =
      LE.LApp (LE.LVar (runtimeResolve name)) (map go args)
    go (IR.MUnboundedSum var body) =
      LE.LForallKw var LE.LProp (go body)
    go (IR.MBoundedSum var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) ->
          LE.LBoundedForall var (runtimeResolve loN) (runtimeResolve hiN) (go body)
        _ ->
          LE.LForallKw var LE.LProp
            (LE.LImpl (LE.LApp (LE.LVar "IsWithinBounds") [go lo, go hi, LE.LVar var])
                      (go body))
    go (IR.MBoundedProduct var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) ->
          LE.LBoundedExists var (runtimeResolve loN) (runtimeResolve hiN) (go body)
        _ ->
          LE.LExists var LE.LProp
            (LE.LImpl (LE.LApp (LE.LVar "IsWithinBounds") [go lo, go hi, LE.LVar var])
                      (go body))
    go (IR.MSumOfIndividuals var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) ->
          LE.LForallIndividuals var (runtimeResolve loN) (runtimeResolve hiN) (go body)
        _ ->
          LE.LForallKw var LE.LProp
            (LE.LImpl (LE.LApp (LE.LVar "IsIndividual") [go lo, go hi, LE.LVar var])
                      (go body))
    go (IR.MProductOfIndividuals var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) ->
          LE.LExistsIndividuals var (runtimeResolve loN) (runtimeResolve hiN) (go body)
        _ ->
          LE.LExists var LE.LProp
            (LE.LImpl (LE.LApp (LE.LVar "IsIndividual") [go lo, go hi, LE.LVar var])
                      (go body))

-- | Render an abbreviation body without name resolution (params verbatim).
abbrevBodyToLean :: IR.MereoExpr -> LE.LeanExpr
abbrevBodyToLean = go
  where
    go (IR.MSum a b)     = LE.LConj   (go a) (go b)
    go (IR.MProd a b)    = LE.LDisj   (go a) (go b)
    go (IR.MDiff a b)    = LE.LImpl   (go b) (go a)
    go (IR.MRevDiff a b) = LE.LImpl   (go a) (go b)
    go (IR.MSymDiff a b) = LE.LBicond (go a) (go b)
    go (IR.MVar n)       = LE.LVar n
    go IR.MZero          = LE.LTop
    go (IR.MAbbrevApp "ProjectIntoInterval" [x, lo, hi]) =
      LE.LProjectIntoInterval (go x) (go lo) (go hi)
    go (IR.MAbbrevApp name args) = LE.LApp (LE.LVar name) (map go args)
    go (IR.MFOLApp name args)    = LE.LApp (LE.LVar name) (map go args)
    go (IR.MUnboundedSum var body) =
      LE.LForallKw var LE.LProp (go body)
    go (IR.MBoundedSum var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) -> LE.LBoundedForall var loN hiN (go body)
        _ -> LE.LForallKw var LE.LProp
               (LE.LImpl (LE.LApp (LE.LVar "IsWithinBounds") [go lo, go hi, LE.LVar var]) (go body))
    go (IR.MBoundedProduct var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) -> LE.LBoundedExists var loN hiN (go body)
        _ -> LE.LExists var LE.LProp
               (LE.LImpl (LE.LApp (LE.LVar "IsWithinBounds") [go lo, go hi, LE.LVar var]) (go body))
    go (IR.MSumOfIndividuals var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) -> LE.LForallIndividuals var loN hiN (go body)
        _ -> LE.LForallKw var LE.LProp
               (LE.LImpl (LE.LApp (LE.LVar "IsIndividual") [go lo, go hi, LE.LVar var]) (go body))
    go (IR.MProductOfIndividuals var lo hi body) =
      case (lo, hi) of
        (IR.MVar loN, IR.MVar hiN) -> LE.LExistsIndividuals var loN hiN (go body)
        _ -> LE.LExists var LE.LProp
               (LE.LImpl (LE.LApp (LE.LVar "IsIndividual") [go lo, go hi, LE.LVar var]) (go body))

-- ---------------------------------------------------------------------------
-- Object suppression
-- ---------------------------------------------------------------------------

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
-- Fin sort family (Lean 4)
-- ---------------------------------------------------------------------------

-- | Generate @fun i => if i = (k : Fin n) then Sk else …@ chain.
finSortFamily :: Int -> [String] -> String
finSortFamily n names
  | allSame names = "fun _ => " ++ head names
  | otherwise     = "fun i => " ++ chain 0 names
  where
    allSame []     = True
    allSame (x:xs) = all (== x) xs

    chain _ [s]      = s
    chain k (s:rest) =
      "if i = (" ++ show k ++ " : Fin " ++ show n ++ ") then " ++ s
      ++ " else " ++ chain (k + 1) rest
    chain _ [] = "False.elim (by omega)"  -- unreachable

-- ---------------------------------------------------------------------------
-- Main renderer
-- ---------------------------------------------------------------------------

renderLeanRuntime :: PreparedTheory -> String
renderLeanRuntime pt = unlines $ concat
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
      [ "-- Generated by Eidos compiler"
      , "-- Theory: " ++ IR.theoryFullyQualifiedName theory
      , ""
      , "import EidosRuntime"
      , ""
      ]

    universeDecls =
      [ "axiom univ : EidosUniverse"
      , "noncomputable def 𝕌 : EidosSort := univ.universeSort"
      , "noncomputable def ℙ : EidosSort := univ.propSort"
      , "def 𝕌_ops : MereologicalOps 𝕌 := {}"
      , ""
      ]

    domainDecls =
      [ "axiom 𝔻 : EidosSort"
      , "axiom 𝔻_sub_univ : OrdinarySortWithinUniverse 𝔻 univ"
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

    userFacts =
      filter (isJust . IR.factMereoExpr)
        [ f | f <- IR.theoryFacts theory
            , IR.factCategory (IR.factKind f) `elem`
                [IR.FCMereologicalTranslation, IR.FCImplicitMerge] ]

    -- Sort ------------------------------------------------------------------
    renderSort s =
      let sn = sortId s
      in [ "axiom " ++ sn ++ " : EidosSort"
         , "axiom " ++ sn ++ "_sub_univ : OrdinarySortWithinUniverse " ++ sn ++ " univ"
         , ""
         ]

    -- SOL function ----------------------------------------------------------
    renderSOLFn f =
      let fn  = sanitize (IR.funcName f)
          dom = sortId (head (IR.funcArgSorts f))
          cod = sortId (IR.funcResSort f)
      in [ "axiom " ++ fn ++ " : SOLFunctionOneArg " ++ dom ++ " " ++ cod
         , ""
         ]

    -- FOL 1-argument function -----------------------------------------------
    renderFOL1Fn f =
      let fn  = sanitize (IR.funcName f)
          dom = sortId (head (IR.funcArgSorts f))
          cod = sortId (IR.funcResSort f)
      in [ "axiom " ++ fn ++ " : FOLFunctionOneArg " ++ dom ++ " " ++ cod
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
      in [ "axiom " ++ domSN ++ " : EidosSort"
         , "axiom " ++ domSN ++ "_sub_univ : OrdinarySortWithinUniverse " ++ domSN ++ " univ"
         , "axiom " ++ fn ++ " : FOLFunction " ++ show n
             ++ " (" ++ finSortFamily n aNms ++ ") " ++ cod ++ " " ++ domSN
         , ""
         ]

    -- Relation --------------------------------------------------------------
    renderRelation r =
      let rn    = sanitize (IR.relName r)
          domSN = sortId (IR.relDomain r)
          n     = length (IR.relArgSorts r)
          aNms  = map sortId (IR.relArgSorts r)
      in [ "axiom " ++ domSN ++ " : EidosSort"
         , "axiom " ++ domSN ++ "_sub_univ : OrdinarySortWithinUniverse " ++ domSN ++ " univ"
         , "axiom " ++ rn ++ " : FOLRelation " ++ show n
             ++ " (" ++ finSortFamily n aNms ++ ") " ++ domSN
         , ""
         ]

    -- Per-sort identity relations -------------------------------------------
    renderIdentityRelation (sn, rn) =
      [ "axiom " ++ rn ++ "_dom : EidosSort"
      , "axiom " ++ rn ++ "_dom_sub_univ : OrdinarySortWithinUniverse " ++ rn ++ "_dom univ"
      , "axiom " ++ rn ++ " : FOLRelation 2 (fun _ => " ++ sn ++ ") " ++ rn ++ "_dom"
      , ""
      ]

    -- Mereological object / individual --------------------------------------
    renderObject m =
      let mn = sanitize (IR.mereoName m)
          sn = sortId (IR.mereoSort m)
          ty = case IR.mereoKind m of
                 IR.MereologicalEntityKindIndividual -> "IndividualOfSort " ++ sn
                 _                                   -> "MereologicalObjectOfSort " ++ sn
      in [ "axiom " ++ mn ++ " : " ++ ty ]

    -- User abbreviation -----------------------------------------------------
    renderUserAbbrev ad =
      let nm     = IR.abbrevName ad
          params = IR.abbrevParams ad
          expr   = LE.renderLeanExpr (abbrevBodyToLean (IR.abbrevBody ad))
      in [ "def " ++ nm
             ++ " " ++ unwords ["(" ++ p ++ " : MereologicalObject)" | p <- params]
             ++ " : MereologicalObject := " ++ expr
         , ""
         ]

    -- User facts ------------------------------------------------------------
    renderUserFacts facts = concatMap renderFact (zip [1 :: Int ..] facts)

    renderFact (idx, f) =
      case IR.factMereoExpr f of
        Nothing -> []
        Just me ->
          let nm   = "ax" ++ show idx
              expr = LE.renderLeanExpr (mereoToLean me)
          in [ "axiom " ++ nm ++ " : " ++ expr ]
