-- | BuildMonad.hs
--
-- Since Eidos theories can reference external theories, building a theory will
-- normally involve reading external files. But we want to keep things pure and
-- will therefore not use the IO monad directly. Instead, Eidos has its own 
-- 'build monad' abstraction.
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Eidos.Resolution.BuildMonad
  ( BuildM
  , BuildError
  , runBuildM
  , liftBuild
  , MonadExternalRefResolver(..)
  , ExternalRefResult(..)
  , ExternalRefSource(..)
  , ExternalRefError(..)
  , TheoryType(..)
  , PureResolver
  , FnResolver(..)
  , mkPureResolver
  , mkPureResolverWithTypes
  , emptyPureResolver
  , ioResolver
  , module Control.Monad.Except
  , module Control.Monad.Reader
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Trans (MonadTrans(..))
import qualified Data.Map as Map
import System.Directory (doesFileExist)
import System.FilePath ((</>))
import Data.Maybe (fromMaybe, catMaybes)
import Control.Monad (forM)

import Eidos.Resolution.ExternalRef

type BuildError = String

-- | Build monad parameterized by the resolver monad 'm'
newtype BuildM m a = BuildM 
  { unBuildM :: ExceptT BuildError (ReaderT (Maybe String) m) a 
  }
  deriving (Functor, Applicative, Monad, MonadError BuildError, MonadReader (Maybe String))

-- | MonadTrans instance
instance MonadTrans BuildM where
  lift = BuildM . lift . lift

-- | Helper to lift an action from the base monad into BuildM
liftBuild :: (Monad m) => m a -> BuildM m a
liftBuild = lift

-- | Run a BuildM computation
runBuildM :: MonadExternalRefResolver m => BuildM m a -> Maybe String -> m (Either BuildError a)
runBuildM (BuildM action) baseContext = 
  runReaderT (runExceptT action) baseContext

-- | Typeclass for external reference resolution
class Monad m => MonadExternalRefResolver m where
  -- | Resolve a reference to a source (may involve IO like checking file existence)
  resolveExternalRef :: Maybe String -> String -> m (Either ExternalRefError ExternalRefResult)
  
  -- | Read the content from a source (only needed for FileSystemSource)
  readExternalContent :: ExternalRefSource -> m String

-- ---------------------------------------------------------------------------
-- IO Resolver (for production)
-- ---------------------------------------------------------------------------

-- | The IO resolver implementation
ioResolver :: (FilePath -> IO Bool) -> FilePath -> Maybe String -> String -> IO (Either ExternalRefError ExternalRefResult)
ioResolver fileExists rootDir _baseContext ref = do
  let components = splitReference ref
      allCandidates = generateCandidates rootDir components
  -- mapM_ (\(tt, path) -> putStrLn $ "  " ++ show tt ++ "...: " ++ path) allCandidates
  -- Check existence for all candidates, deduplicate by path (keeping the first theory type)
  existing <- forM allCandidates $ \(tt, path) -> do
    exists <- fileExists path
    return $ if exists then Just (tt, path) else Nothing
  let valid = catMaybes existing
      -- Deduplicate by path (if same path appears multiple times, keep first)
      unique = Map.toList $ Map.fromListWith (\_old new -> new) [ (path, tt) | (tt, path) <- valid ]
  case unique of
    [] -> return $ Left $ NoMatchingFile ref
    [(path, tt)] -> return $ Right $ ExternalRefResult
                      { extRefIdentifier = ref
                      , extRefTheoryType = tt
                      , extRefSource = FileSystemSource path
                      }
    multiple -> do
      let results = map (\(path, tt) -> ExternalRefResult
                        { extRefIdentifier = ref
                        , extRefTheoryType = tt
                        , extRefSource = FileSystemSource path
                        }) multiple
      return $ Left $ AmbiguousMatch ref results

-- IO instance using actual file system
instance MonadExternalRefResolver IO where
  resolveExternalRef baseContext ref = 
    let rootDir = fromMaybe "." baseContext
    in ioResolver doesFileExist rootDir baseContext ref    
  readExternalContent (FileSystemSource path) = readFile path
  readExternalContent (MemorySource content) = return content

-- ---------------------------------------------------------------------------
-- Pure Resolver (for testing)
-- ---------------------------------------------------------------------------

-- | Pure resolver using an in-memory map
newtype PureResolver = PureResolver 
  { getPureResolver :: Map.Map String (Either ExternalRefError ExternalRefResult) }

instance MonadExternalRefResolver (Reader PureResolver) where
  resolveExternalRef _baseContext ref = do
    resolver <- ask
    return $ Map.findWithDefault (Left $ NoMatchingFile ref) ref (getPureResolver resolver)
  
  readExternalContent (MemorySource content) = return content
  readExternalContent (FileSystemSource path) = 
    error $ "Cannot read from FileSystemSource in pure resolver: " ++ path

-- | Helper to create a pure resolver from a list of (reference, content) pairs
mkPureResolver :: [(String, String)] -> PureResolver
mkPureResolver entries = PureResolver $ Map.fromList 
  [ (ref, Right $ ExternalRefResult 
        { extRefIdentifier = ref
        , extRefTheoryType = PlainTheory
        , extRefSource = MemorySource content
        })
  | (ref, content) <- entries
  ]

-- | Helper to create a pure resolver from typed entries.
mkPureResolverWithTypes :: [(String, String, TheoryType)] -> PureResolver
mkPureResolverWithTypes entries = PureResolver $ Map.fromList
  [ (ref, Right $ ExternalRefResult
        { extRefIdentifier = ref
        , extRefTheoryType = theoryType
        , extRefSource = MemorySource content
        })
  | (ref, content, theoryType) <- entries
  ]

-- | Helper to create a pure resolver that fails for all references
emptyPureResolver :: PureResolver
emptyPureResolver = PureResolver Map.empty

-- ---------------------------------------------------------------------------
-- FnResolver (for testing with arbitrary pure functions)
-- ---------------------------------------------------------------------------

-- | A resolver backed by a pure function
newtype FnResolver = FnResolver
  { getFnResolver :: Maybe String -> String -> Either ExternalRefError ExternalRefResult }

instance MonadExternalRefResolver (Reader FnResolver) where
  resolveExternalRef baseCtx ref = do
    resolver <- ask
    return $ getFnResolver resolver baseCtx ref

  readExternalContent (MemorySource content) = return content
  readExternalContent (FileSystemSource path) =
    error $ "Cannot read from FileSystemSource in FnResolver: " ++ path

