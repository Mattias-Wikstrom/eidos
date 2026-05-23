-- | IR-level function fact entries.
--
-- This module is the single source of truth for the mereological content of
-- function connection, adjunction, decomposition, IR, and relation-bound
-- axioms (sections 22–35 and R6 of MkAxiomSets).
--
-- Each entry is a 'FunctionFactContext' (encoding the SubjectPath and TagSet
-- that the backend will assign) paired with a list of
-- @(lean axiom name, 'IR.MereoExpr')@ pairs.
--
-- 'IR.MAbbrevApp' serves as function application — it renders as
-- @LApp (LVar name) args@ and covers both compiler-internal abbreviations
-- (IsWithinBounds, WrapMetafact) and user-declared functions or relations.
-- 'IR.MBoundedSum' provides bounded universal quantification; the backend
-- may later rewrite it to @bforall@ syntax if that option is chosen.
module Eidos.Pipeline.IRProcessing.FunctionFacts
  ( FunctionFactContext (..)
  , FunctionFactEntry (..)
  , theoryFunctionFactEntries
  ) where

import qualified Eidos.Pipeline.FromSyntax.IR as IR
import qualified Eidos.Pipeline.IRProcessing.NamingConventions as NC

-- ---------------------------------------------------------------------------
-- Context type
-- ---------------------------------------------------------------------------

-- | Organizational context of a function fact entry — used by the backend to
-- assign 'SubjectPath' and tag sets.
data FunctionFactContext
  = FFCFunctionConnection String          -- fn;   [SFunction fn],               [TagFunction, TagConnection]
  | FFCDirImageConnection String          -- fn;   [SFunction fn, SImage],        [TagFunction, TagFOLFunction, TagImage, TagConnection]
  | FFCInvImageConnection String          -- fn;   [SFunction fn, SImage],        [TagFunction, TagFOLFunction, TagImage, TagConnection]
  | FFCImageAdjunction    String          -- fn;   [SFunction fn, SImage],        [TagFunction, TagFOLFunction, TagImage, TagAdjunction]
  | FFCDecomposition      String          -- fn;   [SFunction fn],                [TagFunction, TagFOLFunction, TagDecomposition]
  | FFCTupleConnection    String          -- fn;   [SFunction fn, STuple],        [TagFunction, TagFOLFunction, TagTuple, TagConnection]
  | FFCProjectionConnection  String Int   -- fn k; [SFunction fn, SProjection k], [TagFunction, TagFOLFunction, TagProjection, TagConnection]
  | FFCProjectionAdjunction  String Int   -- fn k; [SFunction fn, SProjection k, SInverse], [TagFunction, TagFOLFunction, TagProjection, TagInverse, TagAdjunction]
  | FFCTupleInvDecomposition String       -- fn;   [SFunction fn, STuple],        [TagFunction, TagFOLFunction, TagTuple, TagInvDecomposition]
  | FFCIRTupleWithProjections String      -- fn;   [SFunction fn, SIR],           [TagFunction, TagFOLFunction, TagIR, TagIRTupleProj]
  | FFCIRProjectionsFromTuple String      -- fn;   [SFunction fn, SIR],           [TagFunction, TagFOLFunction, TagIR, TagIRProjFromTuple]
  | FFCIRSeparates           String       -- fn;   [SFunction fn, SIR],           [TagFunction, TagFOLFunction, TagIR, TagIRSeparates]
  | FFCExtension             String       -- fn;   [SFunction fn],                 [TagFunction, TagFOLFunction, TagExtension]
  | FFCRelBounds             String       -- rn;   [SSet rn],                     [TagSet, TagSorting]
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Entry type
-- ---------------------------------------------------------------------------

-- | A function fact for a single function or relation.
-- 'ffeAxioms' is a list of @(lean axiom name, mereological expression)@ pairs.
data FunctionFactEntry = FunctionFactEntry
  { ffeContext :: FunctionFactContext
  , ffeAxioms  :: [(String, IR.MereoExpr)]
  } deriving (Show)

-- ---------------------------------------------------------------------------
-- Private name helpers
-- ---------------------------------------------------------------------------

dirImgN, invImgN, tupleN, irPredN :: String -> String
dirImgN = NC.funDirImg
invImgN = NC.funInvImg
tupleN  = NC.funTuple
irPredN = NC.irPredicate

piN, piInvN :: String -> Int -> String
piN    = NC.funPi
piInvN = NC.funPiInv

-- ---------------------------------------------------------------------------
-- Private MereoExpr helpers
-- ---------------------------------------------------------------------------

impl, bicond, conj :: IR.MereoExpr -> IR.MereoExpr -> IR.MereoExpr
impl   = IR.MRevDiff
bicond = IR.MSymDiff
conj   = IR.MSum

app :: String -> [IR.MereoExpr] -> IR.MereoExpr
app = IR.MAbbrevApp

var :: String -> IR.MereoExpr
var = IR.MVar

sMin, sMax :: IR.Sort -> IR.MereoExpr
sMin s = IR.MVar (IR.mereoName (IR.sortMin s))
sMax s = IR.MVar (IR.mereoName (IR.sortMax s))

-- TODO: Give this function a better name
bounded :: String -> IR.Sort -> IR.MereoExpr -> IR.MereoExpr
bounded v s body = IR.MBoundedSum v (sMin s) (sMax s) body

domSort :: IR.Function -> IR.Sort
domSort f = maybe (error "FunctionFacts: function has no domain sort") id (IR.funcDomain f)

-- ---------------------------------------------------------------------------
-- Main entry point
-- ---------------------------------------------------------------------------

-- | Derive all function fact entries for a theory.
-- Covers sections 22–35 (function/FOL/image/projection/IR axioms) and
-- R6 (relation bounds) from MkAxiomSets.
theoryFunctionFactEntries :: IR.Theory -> [FunctionFactEntry]
theoryFunctionFactEntries theory = concat
  [ functionConnections
  , dirImageConnections
  , invImageConnections
  , imageAdjunctions
  , decompositions
  , tupleConnections
  , projectionConnections
  , projectionAdjunctions
  , tupleInvDecompositions
  , irTupleWithProjections
  , irProjectionsFromTuple
  , irSeparates
  , extensions
  , relBounds
  ]
  where
    solFunctions   = IR.theorySOLFunctions theory
    folFunctions   = IR.theoryFOLFunctions theory

    isUserOrReflected f = IR.funcOrigin f `elem` [IR.FromSignature, IR.FromReflection]
    userDeclFol    = filter isUserOrReflected folFunctions
    multiArgFol    = filter (\f -> length (IR.funcArgSorts f) > 1 && isUserOrReflected f) folFunctions

    userRelations  = [ r | IR.EntityRelation r <- IR.theoryObjects theory
                         , IR.relOrigin r == IR.FromSignature ]

    -- -----------------------------------------------------------------------
    -- 22. Function connection axioms (SOL + user FOL)
    -- -----------------------------------------------------------------------
    functionConnections = concatMap mkConn (solFunctions ++ userDeclFol)
      where
        mkConn f = case IR.funcResObject f of
          Nothing     -> []
          Just resObj ->
            let fN       = IR.funcName f
                argObjs  = IR.funcArgObjects f
                argCount = length argObjs
                argVarNs = ["X" ++ show i | i <- [1 .. argCount]]
                resVarN  = "X" ++ show (argCount + 1)
                argEqs   = [ bicond (var xi) (var (IR.mereoName obj))
                           | (xi, obj) <- zip argVarNs argObjs ]
                resEq    = bicond (var resVarN) (var (IR.mereoName resObj))
                lhsConj  = case argEqs of
                  []     -> resEq
                  (e:es) -> foldl conj e (es ++ [resEq])
                rhsEq    = bicond (var resVarN) (app fN (map var argVarNs))
                body     = bicond lhsConj rhsEq
                quantified =
                  foldr (\(xi, obj) acc -> bounded xi (IR.mereoSort obj) acc)
                        (bounded resVarN (IR.mereoSort resObj) body)
                        (zip argVarNs argObjs)
            in [FunctionFactEntry (FFCFunctionConnection fN) [(NC.axiomFact fN, quantified)]]

    -- -----------------------------------------------------------------------
    -- 24. Direct image connection axioms
    -- -----------------------------------------------------------------------
    dirImageConnections = concatMap mkDirImgConn multiArgFol
      where
        mkDirImgConn f =
          case IR.funcArgument f of
            Nothing  -> []
            Just arg ->
              let fN      = IR.funcName f
                  dImgN   = dirImgN fN
                  dom     = domSort f
                  resSort = IR.funcResSort f
                  argNm   = IR.mereoName arg
                  resNm   = maybe (IR.funcName f ++ "_res") IR.mereoName (IR.funcResObject f)
                  lhs     = conj (bicond (var "A") (var argNm))
                                 (bicond (var "B") (var resNm))
                  rhs     = bicond (var "B") (app dImgN [var "A"])
                  body    = bicond lhs rhs
                  qB      = bounded "B" resSort body
                  qA      = bounded "A" dom qB
              in [FunctionFactEntry (FFCDirImageConnection fN) [(NC.axiomFact dImgN, qA)]]

    -- -----------------------------------------------------------------------
    -- 25. Inverse image connection axioms
    -- -----------------------------------------------------------------------
    invImageConnections = map mkInvImgConn multiArgFol
      where
        mkInvImgConn f =
          let fN      = IR.funcName f
              iImgN   = invImgN fN
              argNm   = NC.funArg iImgN
              resNm   = NC.funRes iImgN
              dom     = domSort f
              resSort = IR.funcResSort f
              lhs     = conj (bicond (var "A") (var argNm))
                             (bicond (var "B") (var resNm))
              rhs     = bicond (var "B") (app iImgN [var "A"])
              body    = bicond lhs rhs
              qB      = bounded "B" dom body
              qA      = bounded "A" resSort qB
          in FunctionFactEntry (FFCInvImageConnection fN) [(NC.axiomFact iImgN, qA)]

    -- -----------------------------------------------------------------------
    -- 27. Image adjunction axioms
    -- -----------------------------------------------------------------------
    imageAdjunctions = map mkAdj userDeclFol
      where
        mkAdj f =
          let fN      = IR.funcName f
              dom     = domSort f
              resSort = IR.funcResSort f
              lhs     = impl (var "Y") (app (dirImgN fN) [var "X"])
              rhs     = impl (app (invImgN fN) [var "Y"]) (var "X")
              body    = bicond lhs rhs
              qY      = bounded "Y" resSort body
              qX      = bounded "X" dom qY
          in FunctionFactEntry (FFCImageAdjunction fN) [(NC.axiomImageAdjunction fN, qX)]

    -- -----------------------------------------------------------------------
    -- 28. Decomposition axioms: f = f_dir_img ∘ f_tuple
    -- -----------------------------------------------------------------------
    decompositions = map mkDecomp multiArgFol
      where
        mkDecomp f =
          let fN       = IR.funcName f
              argSorts = IR.funcArgSorts f
              varNs    = ["X" ++ show i | i <- [1 .. length argSorts]]
              tupleAp  = app (tupleN fN) (map var varNs)
              body     = bicond (app fN (map var varNs)) (app (dirImgN fN) [tupleAp])
              quantified =
                foldr (\(xi, srt) acc -> bounded xi srt acc)
                      body (zip varNs argSorts)
          in FunctionFactEntry (FFCDecomposition fN) [(NC.axiomDecomposition fN, quantified)]

    -- -----------------------------------------------------------------------
    -- 29. Tuple connection axioms: f_tuple_fact
    -- -----------------------------------------------------------------------
    tupleConnections = concatMap mkTupleConn multiArgFol
      where
        mkTupleConn f =
          case IR.funcArgument f of
            Nothing  -> []
            Just arg ->
              let fN       = IR.funcName f
                  argObjs  = IR.funcArgObjects f
                  argSorts = IR.funcArgSorts f
                  arity    = length argObjs
                  argVars  = ["X" ++ show i | i <- [1 .. arity]]
                  resVar   = "X" ++ show (arity + 1)
                  dom      = domSort f
                  argNm    = IR.mereoName arg
                  argEqs   = [ bicond (var xi) (var (IR.mereoName obj))
                             | (xi, obj) <- zip argVars argObjs ]
                  resEq    = bicond (var resVar) (var argNm)
                  lhsConj  = case argEqs of
                    []     -> resEq
                    (e:es) -> foldl conj e (es ++ [resEq])
                  rhsEq    = bicond (var resVar) (app (tupleN fN) (map var argVars))
                  body     = bicond lhsConj rhsEq
                  quantified =
                    foldr (\(xi, srt) acc -> bounded xi srt acc)
                          (bounded resVar dom body)
                          (zip argVars argSorts)
              in [FunctionFactEntry (FFCTupleConnection fN) [(NC.axiomFact (tupleN fN), quantified)]]

    -- -----------------------------------------------------------------------
    -- 30. Projection connection axioms: f_pi_k_fact
    -- -----------------------------------------------------------------------
    projectionConnections = concatMap mkProjConn multiArgFol
      where
        mkProjConn f =
          let fN  = IR.funcName f
              dom = domSort f
          in [ mkOne fN dom k srt
             | (k, srt) <- zip [1 ..] (IR.funcArgSorts f) ]
          where
            mkOne fN dom k srt =
              let n1   = NC.funArgN (piN fN k) 1
                  nr   = NC.funRes  (piN fN k)
                  lhs  = conj (bicond (var "X1") (var n1))
                              (bicond (var "X2") (var nr))
                  rhs  = bicond (var "X2") (app (piN fN k) [var "X1"])
                  body = bicond lhs rhs
                  qX2  = bounded "X2" srt body
                  qX1  = bounded "X1" dom qX2
              in FunctionFactEntry (FFCProjectionConnection fN k)
                   [(NC.axiomFact (piN fN k), qX1)]

    -- -----------------------------------------------------------------------
    -- 31. Projection adjunction axioms: f_pi_k_adjunction
    -- -----------------------------------------------------------------------
    projectionAdjunctions = concatMap mkProjAdj multiArgFol
      where
        mkProjAdj f =
          let fN  = IR.funcName f
              dom = domSort f
          in [ mkOneAdj fN dom k srt
             | (k, srt) <- zip [1 ..] (IR.funcArgSorts f) ]
          where
            mkOneAdj fN dom k srt =
              let lhs  = impl (var "Y") (app (piN fN k) [var "X"])
                  rhs  = impl (app (piInvN fN k) [var "Y"]) (var "X")
                  body = bicond lhs rhs
                  qY   = bounded "Y" srt body
                  qX   = bounded "X" dom qY
              in FunctionFactEntry (FFCProjectionAdjunction fN k)
                   [(NC.axiomAdjunction (piN fN k), qX)]

    -- -----------------------------------------------------------------------
    -- 32. Tuple inverse decomposition: f_tuple = f_pi_1_inv ∩ f_pi_2_inv ∩ …
    -- -----------------------------------------------------------------------
    tupleInvDecompositions = map mkTupleInvDecomp multiArgFol
      where
        mkTupleInvDecomp f =
          let fN       = IR.funcName f
              argSorts = IR.funcArgSorts f
              varNs    = ["X" ++ show i | i <- [1 .. length argSorts]]
              tupleAp  = app (tupleN fN) (map var varNs)
              meetExpr = foldl1 conj [app (piInvN fN k) [var xk]
                                     | (k, xk) <- zip [1 ..] varNs]
              body     = bicond tupleAp meetExpr
              quantified =
                foldr (\(xi, srt) acc -> bounded xi srt acc)
                      body (zip varNs argSorts)
          in FunctionFactEntry (FFCTupleInvDecomposition fN)
               [(NC.axiomInvDecomposition (tupleN fN), quantified)]

    -- -----------------------------------------------------------------------
    -- 33. IR tuple-with-projections axioms
    -- -----------------------------------------------------------------------
    irTupleWithProjections = map mkIRTuple multiArgFol
      where
        mkIRTuple f =
          let fN      = IR.funcName f
              irN     = irPredN fN
              dom     = domSort f
              arity   = length (IR.funcArgSorts f)
              piApps  = [app (piN fN k) [var "Z"] | k <- [1 .. arity]]
              irZ     = app irN [var "Z"]
              body    = bicond irZ (bicond (var "Z") (app (tupleN fN) piApps))
              qZ      = bounded "Z" dom body
          in FunctionFactEntry (FFCIRTupleWithProjections fN)
               [(NC.axiomTupleWithProjections irN, qZ)]

    -- -----------------------------------------------------------------------
    -- 34. IR projections-from-tuple axioms
    -- -----------------------------------------------------------------------
    irProjectionsFromTuple = map mkIRProj multiArgFol
      where
        mkIRProj f =
          let fN       = IR.funcName f
              irN      = irPredN fN
              argSorts = IR.funcArgSorts f
              varNs    = ["X" ++ show i | i <- [1 .. length argSorts]]
              tupleAp  = app (tupleN fN) (map var varNs)
              irTuple  = app irN [tupleAp]
              projEqs  = [bicond (app (piN fN k) [tupleAp]) (var xk)
                         | (k, xk) <- zip [1 ..] varNs]
              body     = bicond irTuple (foldl1 conj projEqs)
              quantified =
                foldr (\(xi, srt) acc -> bounded xi srt acc)
                      body (zip varNs argSorts)
          in FunctionFactEntry (FFCIRProjectionsFromTuple fN)
               [(NC.axiomProjectionsFromTuple irN, quantified)]

    -- -----------------------------------------------------------------------
    -- 35. IR separates axioms
    -- -----------------------------------------------------------------------
    irSeparates = map mkIRSep multiArgFol
      where
        mkIRSep f =
          let fN    = IR.funcName f
              irN   = irPredN fN
              dom   = domSort f
              irZ   = app irN [var "Z"]
              inner = impl irZ (bicond (impl (var "X") (var "Z"))
                                       (impl (var "Y") (var "Z")))
              qZ    = bounded "Z" dom inner
              sep   = bicond (bicond (var "X") (var "Y")) qZ
              qY    = bounded "Y" dom sep
              qX    = bounded "X" dom qY
          in FunctionFactEntry (FFCIRSeparates fN) [(NC.axiomSeparates irN, qX)]

    -- -----------------------------------------------------------------------
    -- 36. Extension axioms: f(xs) ↔ f(project xs into each argument sort)
    -- -----------------------------------------------------------------------
    extensions = map mkExtension userDeclFol
      where
        mkExtension f =
          let fN       = IR.funcName f
              argSorts = IR.funcArgSorts f
              varNs    = ["X" ++ show i | i <- [1 .. length argSorts]]
              mkProj xi srt = app "ProjectIntoInterval" [var xi, sMin srt, sMax srt]
              lhs      = app fN (map var varNs)
              rhs      = app fN (zipWith mkProj varNs argSorts)
              body     = bicond lhs rhs
              quantified =
                foldr IR.MUnboundedSum body varNs
          in FunctionFactEntry (FFCExtension fN) [(NC.axiomExtension fN, quantified)]

    -- -----------------------------------------------------------------------
    -- R6. Relation bounds axioms
    -- -----------------------------------------------------------------------
    relBounds = map mkRelBounds userRelations
      where
        mkRelBounds r =
          let rN    = IR.relName r
              args  = zip [1 ..] (IR.relArgSorts r)
              varNs = ["X" ++ show k | (k, _) <- args]
              dom   = IR.relDomain r
              relApp = app rN (map var varNs)
              quantify body =
                foldr (\(xi, srt) acc -> bounded xi srt acc)
                      body (zip varNs (map snd args))
          in FunctionFactEntry (FFCRelBounds rN)
               [ (NC.boundMin rN, quantify (impl relApp (sMin dom)))
               , (NC.boundMax rN, quantify (impl (sMax dom) relApp))
               ]
