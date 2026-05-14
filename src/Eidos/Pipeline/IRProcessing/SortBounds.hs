-- | IR-level sort bound and sort ordering facts.
--
-- This module is the single source of truth for:
--
--   * Sort bounds: which entities get bound axioms, what their lo/hi limits
--     are, and whether to collapse to @IsWithinBounds@ (--sorting-axioms).
--   * Sort ordering: the partial order among sort extrema (e.g. U_Max → U_Min,
--     subsort/quotient/subquotient ordering axioms, product-sort and
--     relation-product ordering axioms).
--
-- Backends render the pre-built 'MereoExpr' values without any semantic logic
-- of their own.
module Eidos.Pipeline.IRProcessing.SortBounds
  ( SortBoundOptions (..)
  , defaultSortBoundOptions
  , SortBoundContext (..)
  , SortBoundEntry (..)
  , theorySortBoundEntries
  , SortOrderContext (..)
  , SortOrderEntry (..)
  , theorySortOrderEntries
  ) where

import qualified Eidos.Pipeline.FromSyntax.IR as IR

-- ---------------------------------------------------------------------------
-- Options
-- ---------------------------------------------------------------------------

data SortBoundOptions = SortBoundOptions
  { sboCollapse :: Bool
    -- ^ 'True' (--sorting-axioms): collapse each bound into one
    --   @IsWithinBounds lo obj hi@ axiom.
    --   'False' (default): emit two separate @obj_min@ / @obj_max@ axioms.
  } deriving (Show, Eq)

defaultSortBoundOptions :: SortBoundOptions
defaultSortBoundOptions = SortBoundOptions { sboCollapse = False }

-- ---------------------------------------------------------------------------
-- Context type (for backend path/tag assignment)
-- ---------------------------------------------------------------------------

-- | Organizational context of a sort bound — used by the backend to assign
-- 'SubjectPath' and tag sets.  All semantic decisions live in this module;
-- the backend maps each constructor to the appropriate path + tags.
data SortBoundContext
  = SBCGlobal                          -- [SGlobal], tags [TagSorting]
  | SBCIndividual String               -- [SIndividual n], tags [TagIndividual, TagSorting]
  | SBCSet String                      -- [SSet n], tags [TagSet, TagSorting]
  | SBCFunctionObj String              -- [SFunction fn], tags [TagFunction, TagSorting]
  | SBCFunctionTupleArg String         -- [SFunction fn, STuple, SArgObject 0], tags [TagFunction, TagFOLFunction, TagTuple, TagSorting]
  | SBCFunctionImageArg String         -- [SFunction fn, SImage, SArgObject 1], tags [TagFunction, TagFOLFunction, TagImage, TagSorting]
  | SBCFunctionImageRes String         -- [SFunction fn, SImage, SResObject], tags [TagFunction, TagFOLFunction, TagImage, TagSorting]
  | SBCFunctionInverseArg String       -- [SFunction fn, SInverse, SArgObject 1], tags [TagFunction, TagFOLFunction, TagInverse, TagSorting]
  | SBCFunctionInverseRes String       -- [SFunction fn, SInverse, SResObject], tags [TagFunction, TagFOLFunction, TagInverse, TagSorting]
  | SBCFunctionProjectionArg String Int -- [SFunction fn, SProjection k, SArgObject 1], tags [TagFunction, TagFOLFunction, TagProjection, TagSorting]
  | SBCFunctionProjectionRes String Int -- [SFunction fn, SProjection k, SResObject], tags [TagFunction, TagFOLFunction, TagProjection, TagSorting]
  | SBCRelationObj String              -- [SSet rn], tags [TagSet, TagSorting]
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Entry type
-- ---------------------------------------------------------------------------

-- | A sort bound for a single object.
-- 'sbeAxioms' contains one entry if collapsed, two if expanded.
-- Each entry is @(lean axiom name, mereological expression)@; the backend
-- renders the expression via @mereoExprToLean@ without further branching.
data SortBoundEntry = SortBoundEntry
  { sbeContext :: SortBoundContext
  , sbeAxioms  :: [(String, IR.MereoExpr)]
  } deriving (Show)

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

sanitize :: String -> String
sanitize = map (\c -> if c == '#' then '_' else c)

-- | Build the axiom list for one object given its (IR-level) names.
-- @obj@ is the IR object name (e.g. @\"f#res\"@); @lo@ and @hi@ are IR names
-- for the lower/upper sort bounds (e.g. @\"S_Min\"@, @\"S_Max\"@).
-- The resulting axiom names are Lean-safe (sanitized).
mkAxioms :: SortBoundOptions -> String -> String -> String -> [(String, IR.MereoExpr)]
mkAxioms opts obj lo hi
  | sboCollapse opts =
      [ ( sanitize obj ++ "_sorting"
        , IR.MAbbrevApp "IsWithinBounds" [IR.MVar lo, IR.MVar obj, IR.MVar hi]
        )
      ]
  | otherwise =
      [ (sanitize obj ++ "_min", IR.MRevDiff (IR.MVar obj) (IR.MVar lo))
      , (sanitize obj ++ "_max", IR.MRevDiff (IR.MVar hi) (IR.MVar obj))
      ]

mkEntry :: SortBoundOptions -> String -> String -> String -> SortBoundContext -> SortBoundEntry
mkEntry opts obj lo hi ctx = SortBoundEntry
  { sbeContext = ctx
  , sbeAxioms  = mkAxioms opts obj lo hi
  }

-- | Return the IR names of (min, max) for a sort.
sortMinMaxNames :: IR.Sort -> (String, String)
sortMinMaxNames s =
  ( IR.mereoName (IR.sortMin s)
  , IR.mereoName (IR.sortMax s)
  )

-- ---------------------------------------------------------------------------
-- Main entry point
-- ---------------------------------------------------------------------------

-- | Derive all sort bound entries for a theory.
-- The ordering mirrors the section ordering in 'MkAxiomSets.mkAxiomSets'.
theorySortBoundEntries :: SortBoundOptions -> IR.Theory -> [SortBoundEntry]
theorySortBoundEntries opts theory = concat
  [ mereoBounds
  , individualBounds
  , propBounds
  , dSetBounds
  , userSortSetBounds
  , functionArgResBounds
  , folInverseBounds
  , productArgBounds
  , invImgWitnessBounds
  , projWitnessBounds
  , relArgBounds
  ]
  where
    usesDomain = IR.theoryUsesDomain theory

    solFunctions = IR.theorySOLFunctions theory
    folFunctions = IR.theoryFOLFunctions theory
    userDeclFol  = filter (\f -> IR.funcOrigin f == IR.FromSignature) folFunctions
    folSingleArg = filter (\f -> length (IR.funcArgSorts f) == 1
                              && IR.funcOrigin f == IR.FromSignature) folFunctions
    multiArgFol  = filter (\f -> length (IR.funcArgSorts f) > 1
                              && IR.funcOrigin f == IR.FromSignature) folFunctions

    uniMinName = IR.mereoName (IR.sortMin (IR.theoryUniverse theory))
    uniMaxName = IR.mereoName (IR.sortMax (IR.theoryUniverse theory))
    pMinName   = IR.mereoName (IR.sortMin (IR.theoryProp theory))
    pMaxName   = IR.mereoName (IR.sortMax (IR.theoryProp theory))
    domMinName = IR.mereoName (IR.sortMin (IR.theoryDomain theory))
    domMaxName = IR.mereoName (IR.sortMax (IR.theoryDomain theory))

    -- -----------------------------------------------------------------------
    -- 36. Mereological (𝕌-sorted) object bounds
    -- -----------------------------------------------------------------------
    mereoBounds =
      [ mkEntry opts (IR.mereoName m) uniMinName uniMaxName SBCGlobal
      | IR.EntityMereological m <- IR.theoryObjects theory
      , IR.mereoKind   m == IR.MereologicalEntityKindMereological
      , IR.mereoOrigin m == IR.FromSignature
      , IR.mereoName   m `notElem` [uniMinName, uniMaxName]
      ]

    -- -----------------------------------------------------------------------
    -- 36a. Individual bounds (sort-specific)
    -- -----------------------------------------------------------------------
    individualBounds =
      [ let n          = IR.mereoName m
            (lo, hi)   = sortMinMaxNames (IR.mereoSort m)
        in mkEntry opts n lo hi (SBCIndividual (sanitize n))
      | IR.EntityMereological m <- IR.theoryObjects theory
      , IR.mereoKind   m == IR.MereologicalEntityKindIndividual
      , IR.mereoOrigin m == IR.FromSignature
      , IR.mereoName   m `notElem` [uniMinName, uniMaxName]
      ]

    -- -----------------------------------------------------------------------
    -- 37. Propositional (ℙ-sorted) object bounds
    -- -----------------------------------------------------------------------
    propBounds =
      [ mkEntry opts (IR.mereoName m) pMinName pMaxName SBCGlobal
      | IR.EntityMereological m <- IR.theoryObjects theory
      , IR.mereoKind   m == IR.MereologicalEntityKindProposition
      , IR.mereoOrigin m == IR.FromSignature
      , IR.mereoName   m `notElem` [pMinName, pMaxName, "⊤", "⊥"]
      ]

    -- -----------------------------------------------------------------------
    -- 38. 𝔻-sorted set bounds
    -- -----------------------------------------------------------------------
    dSetBounds
      | not usesDomain = []
      | otherwise =
          [ mkEntry opts (IR.mereoName m) domMinName domMaxName SBCGlobal
          | IR.EntityMereological m <- IR.theoryObjects theory
          , IR.mereoKind   m == IR.MereologicalEntityKindSet
          , IR.mereoOrigin m == IR.FromSignature
          , IR.sortKind  (IR.mereoSort m) == IR.SortKindDomain
          ]

    -- -----------------------------------------------------------------------
    -- 39. User-sort set bounds (sort-specific)
    -- -----------------------------------------------------------------------
    userSortSetBounds =
      [ let n        = IR.mereoName m
            (lo, hi) = sortMinMaxNames (IR.mereoSort m)
        in mkEntry opts n lo hi (SBCSet (sanitize n))
      | IR.EntityMereological m <- IR.theoryObjects theory
      , IR.mereoKind   m == IR.MereologicalEntityKindSet
      , IR.mereoOrigin m == IR.FromSignature
      , IR.sortKind  (IR.mereoSort m) == IR.SortKindFromSignature
      ]

    -- -----------------------------------------------------------------------
    -- 19. Function arg/result object bounds
    -- -----------------------------------------------------------------------
    functionArgResBounds = concatMap mkForFunc (solFunctions ++ userDeclFol)
      where
        mkForFunc f =
          [ let n        = IR.mereoName m
                (lo, hi) = sortMinMaxNames (IR.mereoSort m)
            in mkEntry opts n lo hi (SBCFunctionObj (IR.funcName f))
          | m <- IR.funcArgObjects f ++ [IR.funcResObject f]
          ]

    -- -----------------------------------------------------------------------
    -- 20. FOL inverse arg/res bounds
    -- -----------------------------------------------------------------------
    folInverseBounds = concatMap mkForFunc folSingleArg
      where
        mkForFunc f =
          let fInv  = IR.funcName f ++ "_inv"
              n1    = fInv ++ "_1"
              nr    = fInv ++ "_res"
              (lo1, hi1) = sortMinMaxNames (IR.funcResSort f)
              (lor, hir) = sortMinMaxNames (head (IR.funcArgSorts f))
          in [ mkEntry opts n1 lo1 hi1 (SBCFunctionInverseArg (IR.funcName f))
             , mkEntry opts nr  lor hir (SBCFunctionInverseRes (IR.funcName f))
             ]

    -- -----------------------------------------------------------------------
    -- 13 (sorting). Product tuple argument bounds
    -- -----------------------------------------------------------------------
    productArgBounds = concatMap mkForFunc multiArgFol
      where
        mkForFunc f =
          case IR.funcArgument f of
            Nothing  -> []
            Just arg ->
              let n        = IR.mereoName arg
                  dom      = maybe (error "SortBounds: no domain sort") id (IR.funcDomain f)
                  domMin   = IR.mereoName (IR.sortMin dom)
                  domMax   = IR.mereoName (IR.sortMax dom)
              in [ mkEntry opts n domMin domMax (SBCFunctionTupleArg (IR.funcName f)) ]

    -- -----------------------------------------------------------------------
    -- 15 (sorting). Inverse-image witness bounds
    -- -----------------------------------------------------------------------
    invImgWitnessBounds = concatMap mkForFunc multiArgFol
      where
        mkForFunc f =
          let fN     = IR.funcName f ++ "_inv_img"
              argN   = fN ++ "_arg"
              resN   = fN ++ "_res"
              dom    = maybe (error "SortBounds: no domain sort") id (IR.funcDomain f)
              domMin = IR.mereoName (IR.sortMin dom)
              domMax = IR.mereoName (IR.sortMax dom)
              (rMin, rMax) = sortMinMaxNames (IR.funcResSort f)
          in [ mkEntry opts argN rMin rMax (SBCFunctionImageArg (IR.funcName f))
             , mkEntry opts resN domMin domMax (SBCFunctionImageRes (IR.funcName f))
             ]

    -- -----------------------------------------------------------------------
    -- 21. Projection witness bounds
    -- -----------------------------------------------------------------------
    projWitnessBounds = concatMap mkForFunc multiArgFol
      where
        mkForFunc f =
          let dom    = maybe (error "SortBounds: no domain sort") id (IR.funcDomain f)
              domMin = IR.mereoName (IR.sortMin dom)
              domMax = IR.mereoName (IR.sortMax dom)
          in concatMap (mkOne domMin domMax) (zip [1 ..] (IR.funcArgSorts f))
          where
            mkOne domMin domMax (k, srt) =
              let base = IR.funcName f ++ "_pi_" ++ show k
                  n1   = base ++ "_1"
                  nr   = base ++ "_res"
                  (sMin, sMax) = sortMinMaxNames srt
              in [ mkEntry opts n1 domMin domMax (SBCFunctionProjectionArg (IR.funcName f) k)
                 , mkEntry opts nr  sMin   sMax   (SBCFunctionProjectionRes (IR.funcName f) k)
                 ]

    -- -----------------------------------------------------------------------
    -- Relation argument object bounds
    -- -----------------------------------------------------------------------
    relArgBounds = concatMap mkForRel userRelations
      where
        userRelations =
          [ r | IR.EntityRelation r <- IR.theoryObjects theory
              , IR.relOrigin r == IR.FromSignature ]
        mkForRel r =
          [ let n        = IR.mereoName obj
                (lo, hi) = sortMinMaxNames (IR.mereoSort obj)
            in mkEntry opts n lo hi (SBCRelationObj (IR.relName r))
          | obj <- IR.relArgObjects r
          ]

-- ---------------------------------------------------------------------------
-- Sort ordering context / entry types
-- ---------------------------------------------------------------------------

-- | Organizational context of a sort ordering entry — used by the backend to
-- assign 'SubjectPath' and tag sets.
data SortOrderContext
  = SOCBuiltinSort String          -- [SSort n], tags [TagSort, TagOrdering]
  | SOCUserSort    String          -- [SSort n], tags [TagSort, TagOrdering]
  | SOCProductSort String          -- fn; [SFunction fn, STuple], tags [TagSort, TagFunction, TagFOLFunction, TagTuple, TagOrdering]
  | SOCRelationProductSort String  -- rn; [SSet rn], tags [TagSort, TagSet, TagOrdering]
  deriving (Show, Eq)

-- | A sort ordering entry for a single sort or product sort.
-- 'soeAxioms' is a list of @(lean axiom name, mereological expression)@ pairs.
data SortOrderEntry = SortOrderEntry
  { soeContext :: SortOrderContext
  , soeAxioms  :: [(String, IR.MereoExpr)]
  } deriving (Show)

-- ---------------------------------------------------------------------------
-- Main entry point for sort ordering
-- ---------------------------------------------------------------------------

-- | Derive all sort ordering entries for a theory.
-- Covers sections 40 (builtin + user sort orderings), 41 (product sort
-- orderings), and R7 (relation product sort orderings) from MkAxiomSets.
theorySortOrderEntries :: IR.Theory -> [SortOrderEntry]
theorySortOrderEntries theory = concat
  [ builtinSortOrders
  , userSortOrders
  , productSortOrders
  , relProductSortOrders
  ]
  where
    usesDomain = IR.theoryUsesDomain theory

    uSort = IR.theoryUniverse theory
    pSort = IR.theoryProp    theory
    dSort = IR.theoryDomain  theory

    uSortN = IR.sortName uSort
    pSortN = IR.sortName pSort
    dSortN = IR.sortName dSort

    uMaxN = IR.mereoName (IR.sortMax uSort)
    uMinN = IR.mereoName (IR.sortMin uSort)
    pMaxN = IR.mereoName (IR.sortMax pSort)
    pMinN = IR.mereoName (IR.sortMin pSort)

    userSortsList =
      [ s | IR.EntitySort s <- IR.theoryObjects theory
          , IR.sortKind s == IR.SortKindFromSignature ]

    multiArgFols =
      filter (\f -> length (IR.funcArgSorts f) > 1
                 && IR.funcOrigin f == IR.FromSignature)
             (IR.theoryFOLFunctions theory)

    userRelations =
      [ r | IR.EntityRelation r <- IR.theoryObjects theory
          , IR.relOrigin r == IR.FromSignature ]

    impl a b   = IR.MRevDiff a b
    bicond a b = IR.MSymDiff a b
    var        = IR.MVar

    -- -----------------------------------------------------------------------
    -- 40a. Built-in sort orderings: 𝕌, ℙ, and optionally 𝔻
    -- -----------------------------------------------------------------------
    builtinSortOrders =
      [ SortOrderEntry (SOCBuiltinSort uSortN)
          [ (uSortN ++ "_ordering", impl (var uMaxN) (var uMinN)) ]
      , SortOrderEntry (SOCBuiltinSort pSortN)
          [ (pSortN ++ "_upper",    impl (var uMaxN) (var pMaxN))
          , (pSortN ++ "_ordering", impl (var pMaxN) (var pMinN))
          , (pSortN ++ "_lower",    impl (var pMinN) (var uMinN))
          ]
      ] ++
      if usesDomain
        then let dMaxN = IR.mereoName (IR.sortMax dSort)
                 dMinN = IR.mereoName (IR.sortMin dSort)
             in [ SortOrderEntry (SOCBuiltinSort dSortN)
                    [ (dSortN ++ "_upper",    impl (var uMaxN) (var dMaxN))
                    , (dSortN ++ "_ordering", impl (var dMaxN) (var dMinN))
                    , (dSortN ++ "_lower",    impl (var dMinN) (var pMaxN))
                    ]
                ]
        else []

    -- -----------------------------------------------------------------------
    -- 40b. User sort orderings (subsort / quotient / subquotient / regular)
    -- -----------------------------------------------------------------------
    userSortOrders = map mkOrder userSortsList
      where
        mkOrder s =
          let sN    = IR.sortName s
              sMinN = IR.mereoName (IR.sortMin s)
              sMaxN = IR.mereoName (IR.sortMax s)
          in case (IR.sortRelationship s, IR.sortParent s) of
            (IR.SubSort, Just parent) ->
              let pMinN' = IR.mereoName (IR.sortMin parent)
                  pMaxN' = IR.mereoName (IR.sortMax parent)
              in SortOrderEntry (SOCUserSort sN)
                   [ (sN ++ "_lower",    bicond (var sMinN) (var pMinN'))
                   , (sN ++ "_upper",    impl   (var pMaxN') (var sMaxN))
                   , (sN ++ "_ordering", impl   (var sMaxN) (var sMinN))
                   ]
            (IR.Quotient, Just parent) ->
              let pMinN' = IR.mereoName (IR.sortMin parent)
                  pMaxN' = IR.mereoName (IR.sortMax parent)
              in SortOrderEntry (SOCUserSort sN)
                   [ (sN ++ "_lower",    impl   (var pMinN') (var sMinN))
                   , (sN ++ "_upper",    bicond (var sMaxN) (var pMaxN'))
                   , (sN ++ "_ordering", impl   (var sMaxN) (var sMinN))
                   ]
            (IR.SubQuotient, Just parent) ->
              let pMinN' = IR.mereoName (IR.sortMin parent)
                  pMaxN' = IR.mereoName (IR.sortMax parent)
              in SortOrderEntry (SOCUserSort sN)
                   [ (sN ++ "_lower",    impl (var pMinN') (var sMinN))
                   , (sN ++ "_upper",    impl (var pMaxN') (var sMaxN))
                   , (sN ++ "_ordering", impl (var sMaxN) (var sMinN))
                   ]
            _ ->
              SortOrderEntry (SOCUserSort sN)
                [ (sN ++ "_upper",    impl (var uMaxN) (var sMaxN))
                , (sN ++ "_ordering", impl (var sMaxN) (var sMinN))
                , (sN ++ "_lower",    impl (var sMinN) (var pMaxN))
                ]

    -- -----------------------------------------------------------------------
    -- 41. Product sort orderings (multi-arg FOL functions)
    -- -----------------------------------------------------------------------
    productSortOrders = map mkOrder multiArgFols
      where
        mkOrder f =
          let fN    = IR.funcName f
              dom   = maybe (error "SortBounds: no domain sort") id (IR.funcDomain f)
              dMinN = IR.mereoName (IR.sortMin dom)
              dMaxN = IR.mereoName (IR.sortMax dom)
          in SortOrderEntry (SOCProductSort fN)
               [ (fN ++ "_dom_upper",    impl (var uMaxN) (var dMaxN))
               , (fN ++ "_dom_ordering", impl (var dMaxN) (var dMinN))
               , (fN ++ "_dom_lower",    impl (var dMinN) (var pMaxN))
               ]

    -- -----------------------------------------------------------------------
    -- R7. Relation product sort orderings
    -- -----------------------------------------------------------------------
    relProductSortOrders = map mkOrder userRelations
      where
        mkOrder r =
          let rN    = IR.relName r
              dom   = IR.relDomain r
              dMinN = IR.mereoName (IR.sortMin dom)
              dMaxN = IR.mereoName (IR.sortMax dom)
          in SortOrderEntry (SOCRelationProductSort rN)
               [ (rN ++ "_dom_upper",    impl (var uMaxN) (var dMaxN))
               , (rN ++ "_dom_ordering", impl (var dMaxN) (var dMinN))
               , (rN ++ "_dom_lower",    impl (var dMinN) (var pMaxN))
               ]
