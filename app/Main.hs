module Main where

import Eidos.Parser (parseString)

main :: IO ()
main = do
  let input = "{ signature { sort S; } }"
  case parseString input of
    Left err  -> putStrLn $ "Parse error: " ++ show err
    Right ast -> print ast
