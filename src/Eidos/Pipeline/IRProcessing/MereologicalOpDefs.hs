-- | Per-theory definitions of the five built-in mereological operations.
--
-- Each of +, ×, −, ⇒, ∸ is defined for a theory th by relativizing the
-- corresponding raw logical connective (∧, ∨, ←, →, ↔) to the theory's
-- universe:
--
-- @
--   th.plus  (X, Y) := ProjectIntoInterval(X, 𝕌_Min, 𝕌_Max)  ∧  ProjectIntoInterval(Y, 𝕌_Min, 𝕌_Max)
--   th.times (X, Y) := ProjectIntoInterval(X, 𝕌_Min, 𝕌_Max)  ∨  ProjectIntoInterval(Y, 𝕌_Min, 𝕌_Max)
--   th.minus (X, Y) := ProjectIntoInterval(Y, 𝕌_Min, 𝕌_Max)  →  ProjectIntoInterval(X, 𝕌_Min, 𝕌_Max)
--   th.impl  (X, Y) := ProjectIntoInterval(X, 𝕌_Min, 𝕌_Max)  →  ProjectIntoInterval(Y, 𝕌_Min, 𝕌_Max)
--   th.bicond(X, Y) := ProjectIntoInterval(X, 𝕌_Min, 𝕌_Max)  ↔  ProjectIntoInterval(Y, 𝕌_Min, 𝕌_Max)
-- @
--
-- Note that the +, × and − on the right-hand side of each definition are the
-- *global*, non-relativized operators (raw ∧/∨/→ in the _Props backends), not
-- recursive calls to the relativized versions being defined.
--
-- @ProjectIntoInterval@ is a compiler-internal abbreviation defined in
-- 'IR.allAbbrevDefs'.  Its appearance in the bodies of 'MereoOpDefEntry'
-- values causes the _Props backends to include its @def@\/@Definition@ in
-- the file preamble.
module Eidos.Pipeline.IRProcessing.MereologicalOpDefs
  ( MereoOpDefEntry (..)
  , theoryMereoOpDefEntries
  ) where

import qualified Eidos.Pipeline.FromSyntax.IR as IR

-- ---------------------------------------------------------------------------
-- Entry type
-- ---------------------------------------------------------------------------

-- | A per-theory definition of one built-in mereological operation.
data MereoOpDefEntry = MereoOpDefEntry
  { modDefName :: String
    -- ^ Backend-friendly identifier: @"plus"@, @"times"@, @"minus"@,
    --   @"impl"@, or @"bicond"@.
  , modOpName  :: String
    -- ^ IR 'funcName' of the corresponding mereological op:
    --   @"+"@, @"×"@, @"-"@, @"⇒"@, or @"∸"@.
  , modParams  :: [String]
    -- ^ Parameter names used in 'modBody' (always @[\"X\", \"Y\"]@).
  , modBody    :: IR.MereoExpr
    -- ^ Body of the definition, expressed using 'IR.MAbbrevApp'
    --   @\"ProjectIntoInterval\"@ applied to each parameter and the
    --   theory's universe bounds (@'IR.MVar' \"𝕌_Min\"@, @'IR.MVar' \"𝕌_Max\"@),
    --   combined with the appropriate raw mereological constructor.
  } deriving (Show)

-- ---------------------------------------------------------------------------
-- Main entry point
-- ---------------------------------------------------------------------------

-- | Generate the five mereological-op definition entries for a theory.
--
-- The entries use the theory's actual universe bound mereoNames (𝕌_Min / 𝕌_Max
-- for the built-in universe, or the corresponding names for a sub-theory's
-- universe) so that each body refers to the correct sort limit objects.
theoryMereoOpDefEntries :: IR.Theory -> [MereoOpDefEntry]
theoryMereoOpDefEntries theory =
  let uMin = IR.MVar (IR.mereoName (IR.sortMin (IR.theoryUniverse theory)))
      uMax = IR.MVar (IR.mereoName (IR.sortMax (IR.theoryUniverse theory)))
      proj v = IR.MAbbrevApp "ProjectIntoInterval" [IR.MVar v, uMin, uMax]
  in
  [ MereoOpDefEntry
      { modDefName = "plus"
      , modOpName  = "+"
      , modParams  = ["X", "Y"]
      , modBody    = IR.MSum (proj "X") (proj "Y")
        -- (proj X) ∧ (proj Y)  in _Props backends
      }
  , MereoOpDefEntry
      { modDefName = "times"
      , modOpName  = "×"
      , modParams  = ["X", "Y"]
      , modBody    = IR.MProd (proj "X") (proj "Y")
        -- (proj X) ∨ (proj Y)
      }
  , MereoOpDefEntry
      { modDefName = "minus"
      , modOpName  = "-"
      , modParams  = ["X", "Y"]
      , modBody    = IR.MDiff (proj "X") (proj "Y")
        -- (proj Y) → (proj X)   (note: MDiff(a,b) = b → a)
      }
  , MereoOpDefEntry
      { modDefName = "impl"
      , modOpName  = "⇒"
      , modParams  = ["X", "Y"]
      , modBody    = IR.MRevDiff (proj "X") (proj "Y")
        -- (proj X) → (proj Y)
      }
  , MereoOpDefEntry
      { modDefName = "bicond"
      , modOpName  = "∸"
      , modParams  = ["X", "Y"]
      , modBody    = IR.MSymDiff (proj "X") (proj "Y")
        -- (proj X) ↔ (proj Y)
      }
  ]
