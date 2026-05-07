-- | Mid-level intermediate representation for Lean 4 export.
--
-- This module sits between 'Eidos.IR' (the theory IR) and 'LeanProps'
-- (the final Lean 4 document).  Its purpose is to give every generated
-- axiom a /semantic identity/ — what it is about and what role it plays —
-- independently of how it will ultimately be rendered or ordered.
--
-- == Design principles
--
-- * A 'Tag' names one atomic dimension of variation.  An 'AxiomSet' carries
--   a /set/ of tags so that dimensions compose freely:
--   @{TagFunction, TagProjection, TagAdjunction}@ means
--   "the adjunction axiom for a projection function of some multi-arg
--   function."
--
-- * A 'SubjectPath' locates an axiom set within the theory's entity
--   hierarchy.  Paths always start with a top-level node ('SSort',
--   'SSet', 'SFunction', or 'SGlobal') and may descend at most one level
--   into a sub-entity ('SImage', 'SProjection', 'STuple', 'SInverse',
--   'SIR', 'SArgObject', 'SResObject').
--
-- * 'AxiomSet' groups one or more 'LeanAxiom' values that express the same
--   logical thought.  Whether the group renders as one axiom or several is
--   a rendering decision, not a generation decision.
--
-- == Vocabulary notes
--
-- * We say /set/ (not subsort) for things declared with @S1 ⊆ S@.
-- * We say /connection/ (not fact) for the biconditional that links a
--   function's canonical argument/result objects to the function itself.
-- * We say /sorting/ for the bounds that record which sort an object
--   belongs to (e.g. @f_1_min@/@f_1_max@, or equivalently
--   @IsWithinBounds S_Min S_Max f_1@).
-- * We say /ordering/ for the axioms that record how sorts relate to each
--   other (e.g. @S_upper@, @S_lower@, @S_ordering@).

module Eidos.Backend.LeanProps.LeanAxiomSet
  ( -- * Tags
    Tag (..)
  , TagSet
  , tags         -- ^ smart constructor: validate and build a TagSet
    -- * Subject paths
  , SubjectNode (..)
  , SubjectPath
    -- * Axiom sets
  , AxiomSet (..)
  , axiomSet     -- ^ smart constructor
    -- * Query helpers
  , hasTag
  , hasAllTags
  , hasAnyTag
  , atPath
  , atPathPrefix
  , byTag
  , bySubject
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import Eidos.Backend.LeanProps.LeanExpr (LeanAxiom)

-- ---------------------------------------------------------------------------
-- Tags
-- ---------------------------------------------------------------------------

-- | One atomic dimension of semantic variation.
--
-- Tags are designed to be /orthogonal/: each tag names a single dimension,
-- and the full description of an axiom set is the /set/ of all applicable
-- tags.  The smart constructor 'tags' will reject combinations that violate
-- the constraint that sub-entity tags (@TagImage@, @TagProjection@, etc.)
-- must co-occur with @TagFunction@.
data Tag = TagSort
  -- -----------------------------------------------------------------------
  -- Entity-kind tags  (what kind of theory entity is involved?)
  -- -----------------------------------------------------------------------
  
    -- ^ Concerns a sort (including product-domain sorts like @f_dom@).
  | TagSet
    -- ^ Concerns a set declared with @S1 ⊆ S@.
  | TagIndividual
    -- ^ Concerns an individual declared with @i : S@.
  | TagFunction
    -- ^ Concerns a function (FOL or SOL, user-declared or generated).
    --   Always present when 'TagFOLFunction' or 'TagSOLFunction' is present,
    --   and when any of the sub-entity tags are present.
  | TagFOLFunction
    -- ^ The function originates from a user-declared FOL function
    --   (including all generated machinery: product sort, projections,
    --   tuples, image functions, IR predicate).
    --   Always co-occurs with 'TagFunction'.
  | TagSOLFunction
    -- ^ The function originates from a user-declared SOL function.
    --   Always co-occurs with 'TagFunction'.
  | TagImage
    -- ^ Concerns the direct/inverse-image sub-entity of a function.
    --   Always co-occurs with 'TagFunction'.
  | TagProjection
    -- ^ Concerns a projection function of a multi-argument function.
    --   Always co-occurs with 'TagFunction'.
  | TagTuple
    -- ^ Concerns the tuple-formation sub-entity of a multi-argument function.
    --   Always co-occurs with 'TagFunction'.
  | TagInverse
    -- ^ Concerns the (Galois) inverse of a function.
    --   Always co-occurs with 'TagFunction'.
  | TagIR
    -- ^ Concerns the invertible-rectangular predicate of a multi-arg function.
    --   Always co-occurs with 'TagFunction'.
    --   Present on /all/ IR-related axiom sets, so that filtering by 'TagIR'
    --   collects everything IR-related across all functions.  The more
    --   specific role tags ('TagIRTupleProj', 'TagIRProjFromTuple',
    --   'TagIRSeparates') narrow within that group.

  -- -----------------------------------------------------------------------
  -- Role tags  (what logical role does this axiom set play?)
  -- -----------------------------------------------------------------------

  | TagDecl
    -- ^ Declares that a name exists with a given type (no further content).
    --   E.g. @axiom f : Prop → Prop → Prop@.
  | TagConnection
    -- ^ Connects a function's canonical argument/result objects to the
    --   function itself via a biconditional.
    --   E.g. @f_fact@, @g_fact@, @f_pi_1_fact@.
  | TagAdjunction
    -- ^ States a Galois adjunction (left ⊣ right).
    --   E.g. @g_adjunction@, @f_pi_1_adjunction@, @f_image_adjunction@.
  | TagSorting
    -- ^ States that an object belongs to a particular sort.
    --   E.g. @f_1_min@/@f_1_max@ (= @IsWithinBounds S_Min S_Max f_1@).
  | TagOrdering
    -- ^ States how two sorts (or a sort and a bound) relate to each other.
    --   E.g. @S_upper@, @S_lower@, @S_ordering@, @U_to_P@.
  | TagDecomposition
    -- ^ States that a multi-arg function decomposes as dir-img ∘ tuple.
    --   E.g. @f_decomposition@.
  | TagInvDecomposition
    -- ^ States that a tuple decomposes as a meet of inverse projections.
    --   E.g. @f_tuple_inv_decomposition@.
  | TagIRTupleProj
    -- ^ States the IR characterisation via tuple+projections.
    --   E.g. @IR_f_tuple_with_projections@.
  | TagIRProjFromTuple
    -- ^ States projection recovery from IR tuples.
    --   E.g. @IR_f_projections_from_tuple@.
  | TagIRSeparates
    -- ^ States the separation axiom for IR.
    --   E.g. @IR_f_separates@.
  | TagUserFact
    -- ^ A user-written assertion or metafact from the theory source.
    --   E.g. @ax1@, @ax2@.
  | TagImplicitMerge
    -- ^ An implicit merge fact connecting entities across subtheories.
    --   Generated when an implicit subtheory's entities are merged into
    --   the parent namespace.  The Lean rendering depends on the entity
    --   type: sort bounds produce U_Min-wrapped pairs, functions produce
    --   plain equality, and propositions produce U_Min-wrapped equality.

  deriving (Eq, Ord, Show, Enum, Bounded)

-- | A set of tags describing an 'AxiomSet'.
type TagSet = Set Tag

-- | Smart constructor for 'TagSet'.
--
-- Checks that sub-entity tags (@TagImage@, @TagProjection@, @TagTuple@,
-- @TagInverse@, @TagIR@) always co-occur with @TagFunction@.
-- Raises an error on violation (programming error, not user error).
tags :: [Tag] -> TagSet
tags ts =
  let s = Set.fromList ts
      subEntityTags  = [TagImage, TagProjection, TagTuple, TagInverse, TagIR]
      originTags     = [TagFOLFunction, TagSOLFunction]
      hasSubEntity   = any (`Set.member` s) subEntityTags
      hasOriginTag   = any (`Set.member` s) originTags
      hasTagFunction = TagFunction `Set.member` s
      irRoleTags     = [TagIRTupleProj, TagIRProjFromTuple, TagIRSeparates]
      hasIRRoleTag   = any (`Set.member` s) irRoleTags
      hasTagIR       = TagIR `Set.member` s
  in if (hasSubEntity || hasOriginTag) && not hasTagFunction
       then error $ "LeanAxiomSet.tags: sub-entity or origin tag present without TagFunction: "
                 ++ show ts
     else if hasIRRoleTag && not hasTagIR
       then error $ "LeanAxiomSet.tags: IR role tag present without TagIR: "
                 ++ show ts
     else s

-- ---------------------------------------------------------------------------
-- Subject paths
-- ---------------------------------------------------------------------------

-- | One node in a subject path.
data SubjectNode
  = SGlobal
    -- ^ Not tied to any specific theory entity.
    --   Used for built-in declarations (U/P limits, propext …).
  | SSort String
    -- ^ A sort, identified by its name (e.g. @"S"@, @"T"@, @"f_dom"@).
  | SSet String
    -- ^ A set declared with @⊆@, identified by its name (e.g. @"S1"@).
  | SIndividual String
    -- ^ An individual declared with @:@, identified by name (e.g. @"i1"@).
  | SFunction String
    -- ^ A function, identified by its name (e.g. @"f"@, @"g"@, @"k"@).
    --   Always the root of a path that descends into sub-entities.
  | SImage
    -- ^ The direct/inverse-image sub-entity of the parent function.
  | SProjection Int
    -- ^ The k-th (1-based) projection of the parent function.
  | STuple
    -- ^ The tuple-formation sub-entity of the parent function.
  | SInverse
    -- ^ The Galois-inverse sub-entity of the parent function.
  | SIR
    -- ^ The invertible-rectangular predicate of the parent function.
  | SArgObject Int
    -- ^ The k-th (1-based) canonical argument object of the parent entity.
    --   E.g. @f_1@ is @SArgObject 1@ under @SFunction "f"@.
  | SResObject
    -- ^ The canonical result object of the parent entity.
    --   E.g. @f_res@ is @SResObject@ under @SFunction "f"@.
  deriving (Eq, Ord, Show)

-- | A subject path: a non-empty list of 'SubjectNode' values.
--
-- Invariants (not enforced by the type, but by 'axiomSet'):
--
-- * The first node is always 'SGlobal', 'SSort', 'SSet', 'SIndividual', or 'SFunction'.
-- * Sub-entity nodes ('SImage', 'SProjection', 'STuple', 'SInverse',
--   'SIR', 'SArgObject', 'SResObject') may only appear after 'SFunction'.
-- * Paths have depth at most 3 (root + sub-entity + object).
type SubjectPath = [SubjectNode]

-- ---------------------------------------------------------------------------
-- AxiomSet
-- ---------------------------------------------------------------------------

-- | A named, tagged, located group of one or more axioms that express a
-- single logical thought.
--
-- Use 'axiomSet' to construct values; the smart constructor validates
-- invariants.
data AxiomSet = AxiomSet
  { asPath   :: SubjectPath  -- ^ where in the theory hierarchy this lives
  , asTags   :: TagSet       -- ^ what kind of thing this is
  , asAxioms :: [LeanAxiom]  -- ^ the actual axioms (non-empty)
  } deriving (Eq, Show)

-- | Smart constructor for 'AxiomSet'.
--
-- Checks:
--
-- * @axs@ is non-empty.
-- * @path@ is non-empty.
-- * The first path node is 'SGlobal', 'SSort', 'SSet', 'SIndividual', or 'SFunction'.
-- * Sub-entity nodes only appear when the first node is 'SFunction'.
axiomSet :: SubjectPath -> TagSet -> [LeanAxiom] -> AxiomSet
axiomSet path ts axs
  | null axs  = error "LeanAxiomSet.axiomSet: empty axiom list"
  | null path = error "LeanAxiomSet.axiomSet: empty subject path"
  | otherwise =
      let root = head path
          validRoot = case root of
            SGlobal      -> True
            SSort _      -> True
            SSet _       -> True
            SIndividual _ -> True
            SFunction _  -> True
            _            -> False
          subEntityNodes = tail path
          subEntityOk = case root of
            SFunction _ -> True
            _           -> null subEntityNodes
      in if not validRoot
           then error $ "LeanAxiomSet.axiomSet: path must start with SGlobal/SSort/SSet/SIndividual/SFunction, got: " ++ show root
           else if not subEntityOk
             then error $ "LeanAxiomSet.axiomSet: sub-entity nodes only allowed under SFunction, path: " ++ show path
             else AxiomSet { asPath = path, asTags = ts, asAxioms = axs }

-- ---------------------------------------------------------------------------
-- Query helpers
-- ---------------------------------------------------------------------------

-- | Does an 'AxiomSet' have this tag?
hasTag :: Tag -> AxiomSet -> Bool
hasTag t as_ = t `Set.member` asTags as_

-- | Does an 'AxiomSet' have /all/ of these tags?
hasAllTags :: [Tag] -> AxiomSet -> Bool
hasAllTags ts as_ = all (`Set.member` asTags as_) ts

-- | Does an 'AxiomSet' have /any/ of these tags?
hasAnyTag :: [Tag] -> AxiomSet -> Bool
hasAnyTag ts as_ = any (`Set.member` asTags as_) ts

-- | Does an 'AxiomSet' have exactly this subject path?
atPath :: SubjectPath -> AxiomSet -> Bool
atPath p as_ = asPath as_ == p

-- | Does an 'AxiomSet' have a subject path that starts with this prefix?
atPathPrefix :: SubjectPath -> AxiomSet -> Bool
atPathPrefix prefix as_ = prefix `isPrefixOf` asPath as_
  where
    isPrefixOf []     _      = True
    isPrefixOf _      []     = False
    isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

-- | Filter a list of 'AxiomSet' values by tag.
byTag :: Tag -> [AxiomSet] -> [AxiomSet]
byTag t = filter (hasTag t)

-- | Filter a list of 'AxiomSet' values by exact subject path.
bySubject :: SubjectPath -> [AxiomSet] -> [AxiomSet]
bySubject p = filter (atPath p)
