-- | External reference resolution phase (IO).
-- 
-- This module handles collecting all external subtheory references reachable
-- from a theory declaration, without constructing any IR. It uses the
-- 'BuildM' monad and 'MonadExternalRefResolver' to perform file I/O.
module Eidos.Resolution.Resolution
  ( resolveExternalRefs
  , resolveWithFn
  , ResolutionError
  , BuildError
  ) where

import           Control.Monad        (foldM)
import qualified Data.Map.Strict      as Map
import           System.FilePath      (takeDirectory)

import           Eidos.Parse.AST
import qualified Eidos.Parse.AST      as AST
import           Eidos.Resolution.BuildMonad
import           Eidos.Resolution.ExternalRef
import           Eidos.Parse.Parser   (parseString)

-- | Type alias for resolution errors (same as BuildError)
type ResolutionError = String

-- | Pure resolution using a custom resolver function (for testing).
resolveWithFn
  :: (Maybe String -> String -> Either ExternalRefError ExternalRefResult)
  -> Maybe String
  -> TheoryDecl
  -> Either BuildError (Map.Map String (TheoryBody, TheoryType))
resolveWithFn fn baseCtx td =
  runReader (runBuildM (collectRefs (AST.theoryBody td)) baseCtx) (FnResolver fn)

-- | Collect all external subtheory sources reachable from a 'TheoryDecl'
-- without constructing any IR. Returns a map from reference identifier to
-- '(TheoryBody, TheoryType)'.
resolveExternalRefs
  :: FilePath
  -> TheoryDecl
  -> IO (Either ResolutionError (Map.Map String (TheoryBody, TheoryType)))
resolveExternalRefs filePath td =
  runBuildM (collectRefs (AST.theoryBody td)) (Just (takeDirectory filePath))

-- | Collect all external references from a TheoryBody
collectRefs
  :: (MonadExternalRefResolver m)
  => TheoryBody
  -> BuildM m (Map.Map String (TheoryBody, TheoryType))
collectRefs body = foldM collectRefsSection Map.empty (sections body)

-- | Process a section for external references
collectRefsSection
  :: (MonadExternalRefResolver m)
  => Map.Map String (TheoryBody, TheoryType)
  -> Section
  -> BuildM m (Map.Map String (TheoryBody, TheoryType))
collectRefsSection acc (SectionSubtheories (SubtheoriesSection entries)) =
  foldM collectRefsEntry acc entries
collectRefsSection acc _ = return acc

-- | Process a subtheory entry for external references
collectRefsEntry
  :: (MonadExternalRefResolver m)
  => Map.Map String (TheoryBody, TheoryType)
  -> SubtheoryEntry
  -> BuildM m (Map.Map String (TheoryBody, TheoryType))
collectRefsEntry acc (SubtheoryEntryGroup (SubtheoryGroup _ items)) =
  foldM collectRefsItem acc items
collectRefsEntry acc (SubtheoryEntryItem item) =
  collectRefsItem acc item

-- | Process a subtheory item for external references
collectRefsItem
  :: (MonadExternalRefResolver m)
  => Map.Map String (TheoryBody, TheoryType)
  -> SubtheoryItem
  -> BuildM m (Map.Map String (TheoryBody, TheoryType))
collectRefsItem acc item = case itemDef item of
  SubtheoryBody b -> do
    nested <- collectRefs b
    return (Map.union acc nested)
  SubtheoryExternalRef ref -> do
    baseContext <- ask
    let refPath = case ref of { ('@':rest) -> rest; _ -> ref }
    result <- lift $ resolveExternalRef baseContext refPath
    res <- case result of
      Left err -> throwError (show err)
      Right r  -> return r
    content <- lift $ readExternalContent (extRefSource res)
    ast <- case parseString content of
      Left parseErr -> throwError $
        "Parse error in " ++ extRefIdentifier res ++ ": " ++ show parseErr
      Right a -> return a
    let body = AST.theoryBody ast
        key  = refPath
        tt   = extRefTheoryType res
    nested <- collectRefs body
    return (Map.insert key (body, tt) (Map.union acc nested))
