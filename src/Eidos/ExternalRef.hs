-- | External reference data types - pure data only
module Eidos.ExternalRef
  ( -- * Core types
    ExternalRefError(..)
  , ExternalRefResult(..)
  , ExternalRefSource(..)
  , TheoryType(..)
    -- * File system utilities (pure)
  , generateCandidates
  , splitReference
  , splitOn
  , extractIdentifier
  , theoryTypeToExtension
  , theoryTypeToSuffix
  , allTheoryTypes
    -- * Test helpers
  , mockResolver
  ) where

import           Data.List      (intercalate, isSuffixOf)
import           System.FilePath    ((</>), joinPath)

-- | Type of theory based on file extension
data TheoryType
  = PlainTheory
  | CoherentTheory
  | EquationalTheory
  | RegularTheory
  | FOLTheory
  | SOLTheory
  deriving (Show, Eq, Enum, Bounded)

-- | Result of resolving an external reference
data ExternalRefResult = ExternalRefResult
  { extRefIdentifier :: String
  , extRefTheoryType :: TheoryType
  , extRefSource     :: ExternalRefSource
  } deriving (Show, Eq)

-- | Source information for the resolved reference
data ExternalRefSource
  = FileSystemSource FilePath
  | MemorySource String
  deriving (Show, Eq)

-- | Possible errors when resolving an external reference
data ExternalRefError
  = NoMatchingFile String
  | AmbiguousMatch String [ExternalRefResult]
  | ResolverError String
  deriving (Show, Eq)

-- | File extensions for each theory type
theoryTypeToSuffix :: TheoryType -> String
theoryTypeToSuffix PlainTheory     = ""
theoryTypeToSuffix CoherentTheory  = ".coh"
theoryTypeToSuffix EquationalTheory = ".eq"
theoryTypeToSuffix RegularTheory   = ".reg"
theoryTypeToSuffix FOLTheory       = ".fol"
theoryTypeToSuffix SOLTheory       = ".sol"

theoryTypeToExtension :: TheoryType -> String
theoryTypeToExtension tt = theoryTypeToSuffix tt ++ ".theory"

allTheoryTypes :: [TheoryType]
allTheoryTypes = [minBound .. maxBound]

-- | Split "@a.b.ext" into ["a", "b", "ext"]
splitReference :: String -> [String]
splitReference = filter (not . null) . splitOn '.'

-- | Split a string by a delimiter
splitOn :: Char -> String -> [String]
splitOn _ "" = []
splitOn c s = case break (== c) s of
                (part, []) -> [part]
                (part, _:rest) -> part : splitOn c rest

-- | Generate all candidate file paths for a reference (pure)
generateCandidates :: FilePath -> [String] -> [(TheoryType, FilePath)]
generateCandidates baseDir components =
  case components of
    [] -> []
    [single] ->
      -- Rule 1: ext.theory, ext.coh.theory, etc.
      [ (tt, baseDir </> single ++ extension)
        | tt <- allTheoryTypes
        , let extension = theoryTypeToExtension tt
      ]
    multi ->
      let (dirParts, lastPart) = splitLast multi
          dirPath = joinPath dirParts
          fullDirPath = baseDir </> dirPath
      in
        -- Rule 2: a/b/ext.theory
        [ (tt, fullDirPath </> lastPart ++ extension)
          | tt <- allTheoryTypes
          , let extension = theoryTypeToExtension tt
        ] ++
        -- Rule 3: a/b.ext.theory
        [ (tt, baseDir </> dirPath ++ "." ++ lastPart ++ extension)
          | tt <- allTheoryTypes
          , let extension = theoryTypeToExtension tt
        ] ++
        -- Rule 4: a.b.ext.theory (treat whole reference as single filename)
        [ (tt, baseDir </> intercalate "." multi ++ extension)
          | tt <- allTheoryTypes
          , let extension = theoryTypeToExtension tt
        ]

-- | Split a list into all but last element and the last element
splitLast :: [a] -> ([a], a)
splitLast [] = error "splitLast: empty list"
splitLast [x] = ([], x)
splitLast (x:xs) = let (initParts, lastElem) = splitLast xs in (x:initParts, lastElem)

-- | Extract the theory identifier from the reference
extractIdentifier :: [String] -> TheoryType -> String
extractIdentifier components theoryType =
  let baseName = case components of
                   [] -> ""
                   [single] -> single
                   multi -> last multi
      suffix = theoryTypeToSuffix theoryType
  in if null suffix
     then baseName
     else baseName ++ suffix

-- | Create a mock resolver from a list of (reference, result) pairs (for testing).
-- If a reference appears more than once, the resolver returns AmbiguousMatch.
mockResolver :: [(String, Either ExternalRefError ExternalRefResult)]
             -> Maybe String -> String -> Either ExternalRefError ExternalRefResult
mockResolver entries _baseCtx ref =
  let matches = [ r | (k, Right r) <- entries, k == ref ]
      errors  = [ e | (k, Left e)  <- entries, k == ref ]
  in case errors of
       (e:_) -> Left e
       [] -> case matches of
               []  -> Left (NoMatchingFile ref)
               [r] -> Right r
               rs  -> Left (AmbiguousMatch ref rs)