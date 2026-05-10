module Eidos.Print.DebugIR
  ( dumpTheoryIR
  ) where

import           Data.List      (intercalate, sortOn)
import qualified Data.Map.Strict as Map

import           Eidos.Pipeline.FromSyntax.IR
import           Eidos.Print.Pretty   (prettyResolvedPropExpr)

-- | Produce a deterministic, human-readable dump of a theory's IR.
--
-- The dump is intentionally redundant and explicit so it is reliable for
-- debugging: every entity is listed with key links rendered by name instead
-- of via recursive 'Show' instances.
dumpTheoryIR :: Theory -> String
dumpTheoryIR = go 0
  where
    go :: Int -> Theory -> String
    go level th =
      unlines $
        [ ind level ++ "Theory " ++ renderTheoryName th
        , ind (level + 1) ++ "reflection: " ++ show (theoryReflection th)
        , ind (level + 1) ++ "uses 𝔻: " ++ show (theoryUsesDomain th)
        , ind (level + 1) ++ "uses ℙ: " ++ show (theoryUsesProp th)
        , ind (level + 1) ++ "parent: " ++ maybe "<none>" theoryFullyQualifiedName (theoryParent th)
        , ind (level + 1) ++ "closest reflection ancestor: " ++ maybe "<none>" theoryFullyQualifiedName (theoryClosestReflectionAncestor th)
        , ind (level + 1) ++ "object count: " ++ show (length (theoryObjects th))
        , ind (level + 1) ++ "name map keys: " ++ show (Map.size (theoryObjectsByName th))
        , ind (level + 1) ++ "fact count: " ++ show (length (theoryFacts th))
        , ind (level + 1) ++ "subtheory count: " ++ show (length (theorySubtheories th))
        , ind (level + 1) ++ "builtins:"
        , ind (level + 2) ++ "universe sort: " ++ sortName (theoryUniverse th)
        , ind (level + 2) ++ "domain sort: " ++ sortName (theoryDomain th)
        , ind (level + 2) ++ "prop sort: " ++ sortName (theoryProp th)
        , ind (level + 2) ++ "truth object: " ++ mereoName (theoryTruth th)
        , ind (level + 2) ++ "falsity object: " ++ mereoName (theoryFalsity th)
        , ind (level + 2) ++ "sum function: " ++ funcName (theorySum th)
        , ind (level + 2) ++ "prod function: " ++ funcName (theoryProd th)
        , ind (level + 2) ++ "diff function: " ++ funcName (theoryDiff th)
        , ind (level + 2) ++ "rev diff function: " ++ funcName (theoryRevDiff th)
        , ind (level + 2) ++ "sym diff function: " ++ funcName (theorySymDiff th)
        , ind (level + 1) ++ "objects:"
        ]
        ++ map (renderEntity (level + 2)) (sortOn entityName (theoryObjects th))
        ++ [ind (level + 1) ++ "facts:"]
        ++ zipWith (renderFact (level + 2)) [0 :: Int ..] (theoryFacts th)
        ++ [ind (level + 1) ++ "subtheories:"]
        ++ if null (theorySubtheories th)
              then [ind (level + 2) ++ "<none>"]
              else concatMap (lines . go (level + 2)) (sortOn theoryName (theorySubtheories th))

    ind :: Int -> String
    ind n = replicate (n * 2) ' '

renderTheoryName :: Theory -> String
renderTheoryName th
  | null (theoryFullyQualifiedName th) = "<root>"
  | otherwise = theoryFullyQualifiedName th

renderEntity :: Int -> Entity -> String
renderEntity level e =
  case e of
    EntitySort s ->
      ind level ++ "sort " ++ sortName s ++ summary
      where
        summary =
          " {kind=" ++ show (sortKind s) ++
          ", origin=" ++ show (sortOrigin s) ++
          ", min=" ++ mereoName (sortMin s) ++
          ", max=" ++ mereoName (sortMax s) ++
          ", components=[" ++ intercalate ", " (map sortName (sortComponentSorts s)) ++ "]" ++
          ", associated=" ++ maybe "<none>" entityName (sortAssociatedEntity s) ++
          ", reflected-from=" ++ maybe "<none>" theoryFullyQualifiedName (sortReflectedFrom s) ++
          "}"
    EntityFunction f ->
      ind level ++ "function " ++ funcName f ++ summary
      where
        summary =
          " {kind=" ++ show (funcKind f) ++
          ", origin=" ++ show (funcOrigin f) ++
          ", args=[" ++ intercalate ", " (map sortName (funcArgSorts f)) ++ "]" ++
          ", res=" ++ sortName (funcResSort f) ++
          ", res-object=" ++ mereoName (funcResObject f) ++
          ", arg-objects=[" ++ intercalate ", " (map mereoName (funcArgObjects f)) ++ "]" ++
          ", domain=" ++ maybe "<none>" sortName (funcDomain f) ++
          ", argument=" ++ maybe "<none>" mereoName (funcArgument f) ++
          ", direct-image=" ++ maybe "<none>" funcName (funcDirectImage f) ++
          ", inverse-image=" ++ maybe "<none>" funcName (funcInverseImage f) ++
          ", reflected-from=" ++ maybe "<none>" theoryFullyQualifiedName (funcReflectedFrom f) ++
          "}"
    EntityMereological m ->
      ind level ++ "mereo " ++ mereoName m ++ summary
      where
        summary =
          " {kind=" ++ show (mereoKind m) ++
          ", origin=" ++ show (mereoOrigin m) ++
          ", sort=" ++ sortName (mereoSort m) ++
          ", limit-for=" ++ maybe "<none>" sortName (mereoLimitForSort m) ++
          ", reflected-from=" ++ maybe "<none>" theoryFullyQualifiedName (mereoReflectedFrom m) ++
          "}"
    EntityRelation r ->
      ind level ++ "relation " ++ relName r ++ summary
      where
        summary =
          " {kind=" ++ show (relKind r) ++
          ", origin=" ++ show (relOrigin r) ++
          ", args=[" ++ intercalate ", " (map sortName (relArgSorts r)) ++ "]" ++
          ", domain=" ++ sortName (relDomain r) ++
          ", arg-objects=[" ++ intercalate ", " (map mereoName (relArgObjects r)) ++ "]" ++
          ", argument=" ++ mereoName (relArgument r) ++
          ", associated-set=" ++ mereoName (relAssociatedSet r) ++
          ", reflected-from=" ++ maybe "<none>" theoryFullyQualifiedName (relReflectedFrom r) ++
          "}"
    EntityTheory t ->
      ind level ++ "theory-entity " ++ renderTheoryName t
  where
    ind n = replicate (n * 2) ' '

renderFact :: Int -> Int -> Fact -> String
renderFact level i f =
  ind level ++ show i ++ ": " ++ show (factKind f) ++ " => " ++ renderFactExpr f
  where
    renderFactExpr fact = case factMereoExpr fact of
      Just me -> "[mereo] " ++ show me
      Nothing -> case factPropExpr fact of
        Just pe -> prettyResolvedPropExpr pe
        Nothing -> "<no expression>"
    ind n = replicate (n * 2) ' '
