-- Create a new file test/Diagnostic.hs
module Main where

import Eidos.Parser (parseString)
import Text.Megaparsec (errorBundlePretty)

main :: IO ()
main = do
  putStrLn "Testing subtheory syntax variations:\n"
  
  let tests = 
        [ ("named: Sub { signature { sort T; } }", 
           "{ subtheories { named: Sub { signature { sort T; } } } }")
        , ("named Sub { signature { sort T; } }",
           "{ subtheories { named Sub { signature { sort T; } } } }")
        , ("Sub { signature { sort T; } }",
           "{ subtheories { Sub { signature { sort T; } } } }")
        , ("[named] Sub { signature { sort T; } }",
           "{ subtheories { [named] Sub { signature { sort T; } } } }")
        , ("named: Sub [[external]]",
           "{ subtheories { named: Sub [[external]] } }")
        ]
  
  mapM_ (\(desc, input) -> do
    putStrLn $ "Testing: " ++ desc
    putStrLn $ "Input: " ++ input
    case parseString input of
      Left err -> putStrLn $ "  FAILED: " ++ errorBundlePretty err
      Right _ -> putStrLn "  SUCCESS"
    putStrLn "") tests
