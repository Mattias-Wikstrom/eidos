module Main where

import System.Environment (getArgs)
import System.Exit        (exitFailure)
import System.IO          (hPutStrLn, stderr)
import Text.Megaparsec    (errorBundlePretty)

import Eidos.AST       (TheoryDecl)
import Eidos.Parser     (parseString, parseFile)
import Eidos.FromSyntax (buildTheory)
import Eidos.IR

main :: IO ()
main = do
  args <- getArgs
  case args of
    -- No arguments: parse a small inline example and build the IR
    [] -> do
      putStrLn "No file given — running built-in example.\n"
      runOnString exampleSrc

    -- One argument: treat it as a .theory file path
    [path] -> do
      result <- parseFile path
      case result of
        Left err  -> die $ "Parse error in " ++ path ++ ":\n" ++ errorBundlePretty err
        Right ast -> buildAndReport path ast

    _ -> die "Usage: eidos-parser [<file.theory>]"

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

runOnString :: String -> IO ()
runOnString src =
  case parseString src of
    Left err  -> die $ "Parse error:\n" ++ errorBundlePretty err
    Right ast -> buildAndReport "<inline>" ast

buildAndReport :: String -> TheoryDecl -> IO ()
buildAndReport label ast = do
  putStrLn $ "=== Parsed: " ++ label ++ " ==="
  case buildTheory ast of
    Left err -> die $ "IR build error:\n" ++ err
    Right th -> printTheory th

-- | Pretty-print a 'Theory' to stdout.
printTheory :: Theory -> IO ()
printTheory th = do
  putStrLn $ "Theory:   " ++ showFQN th
  putStrLn $ "Sorts:    " ++ showList' (map sortName (allSorts th))
  putStrLn $ "Functions:" ++ showList' (map funcName (allFunctions th))
  putStrLn $ "Individs: " ++ showList' (map mereoName (allIndividuals th))
  putStrLn $ "Sets:     " ++ showList' (map mereoName (allSets th))
  putStrLn $ "Relations:" ++ showList' (map relName  (allRelations th))
  putStrLn $ "Facts:    " ++ show (length (userFacts th)) ++ " user fact(s)"
  putStrLn   ""
  mapM_ (printSubtheory 1) (theorySubtheories th)

printSubtheory :: Int -> Theory -> IO ()
printSubtheory depth th = do
  let indent = replicate (depth * 2) ' '
  putStrLn $ indent ++ "Subtheory: " ++ showFQN th
  putStrLn $ indent ++ "  Sorts:     " ++ showList' (map sortName (allSorts th))
  putStrLn $ indent ++ "  Functions: " ++ showList' (map funcName (allFunctions th))
  putStrLn $ indent ++ "  Facts:     " ++ show (length (userFacts th)) ++ " user fact(s)"
  mapM_ (printSubtheory (depth + 1)) (theorySubtheories th)

-- ---------------------------------------------------------------------------
-- IR accessors (filter out built-ins)
-- ---------------------------------------------------------------------------

showFQN :: Theory -> String
showFQN th = let fqn = theoryFullyQualifiedName th
             in if null fqn then "(root)" else fqn

-- | Sorts declared in the signature (excludes 𝕌, 𝔻, ℙ).
allSorts :: Theory -> [Sort]
allSorts th = [ s | EntitySort s <- theoryObjects th
              , sortOrigin s == FromSignature ]

-- | Functions declared in the signature (excludes built-in mereological ops).
allFunctions :: Theory -> [Function]
allFunctions th = [ f | EntityFunction f <- theoryObjects th
                  , funcOrigin f == FromSignature ]

allIndividuals :: Theory -> [MereologicalObject]
allIndividuals th = [ m | EntityMereological m <- theoryObjects th
                    , mereoKind m == MereologicalEntityKindIndividual
                    , mereoOrigin m == FromSignature ]

allSets :: Theory -> [MereologicalObject]
allSets th = [ m | EntityMereological m <- theoryObjects th
             , mereoKind m == MereologicalEntityKindSet
             , mereoOrigin m == FromSignature ]

allRelations :: Theory -> [Relation]
allRelations th = [ r | EntityRelation r <- theoryObjects th
                  , relOrigin r == FromSignature ]

-- | Facts that are not built-in sort-limit metafacts.
userFacts :: Theory -> [Fact]
userFacts th = filter (\f -> factKind f /= FactKindSortLimitation
                          && not (factIsInherited f)
                          && not (factIsMereologicalTranslation f))
                      (theoryFacts th)

showList' :: [String] -> String
showList' [] = " (none)"
showList' xs = " " ++ unwords (map (\x -> "[" ++ x ++ "]") xs)

die :: String -> IO ()
die msg = hPutStrLn stderr msg >> exitFailure

-- ---------------------------------------------------------------------------
-- Built-in example (a simple monoid theory with a subtheory)
-- ---------------------------------------------------------------------------

exampleSrc :: String
exampleSrc = unlines
  [ "{"
  , "  signature {"
  , "    sort D;"
  , "    n : D;"
  , "    op : D, D → D;"
  , "    MySet ⊆ D;"
  , "    r ⊆ D, D;"
  , "  },"
  , "  axioms {"
  , "    facts {"
  , "      [x : D] op(n, x) =_D x;"
  , "      [x : D] op(x, n) =_D x;"
  , "      [x : D][y : D][z : D] op(x, op(y, z)) =_D op(op(x, y), z);"
  , "    }"
  , "  },"
  , "  subtheories {"
  , "    named {"
  , "      sub: {"
  , "        signature {"
  , "          sort E;"
  , "          e : E;"
  , "        }"
  , "      }"
  , "    }"
  , "  }"
  , "}"
  ]
