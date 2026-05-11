-- | Backend-agnostic axiom set types.
--
-- This module defines the 'Tag', 'SubjectPath', 'AxiomBody', and 'AxiomSet'
-- types that represent the semantic structure of generated axioms,
-- independently of any particular backend (Lean, Coq, …).
--
-- A backend receives @['AxiomSet']@ from 'Eidos.Pipeline.IRProcessing.MkAxiomSets' and
-- interprets each 'AxiomBody' in its target language.
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
-- * 'AxiomSet' groups one or more @('String', 'AxiomBody')@ pairs that
--   express the same logical thought.  The 'String' is the axiom name;
--   'AxiomBody' is the backend-agnostic content.
module Eidos.Pipeline.IRProcessing.AxiomSet
  ( -- * Axiom body
    AxiomBody (..)
    -- * Tags
  , Tag (..)
  , TagSet
  , tags         -- ^ smart constructor: validate and build a TagSet
    -- * Subject paths
  , SubjectNode (..)
  , SubjectPath
  , prettySubjectNode  -- ^ human-readable rendering (no Unicode escaping)
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
import qualified Eidos.Pipeline.FromSyntax.IR as IR

-- ---------------------------------------------------------------------------
-- Axiom body
-- ---------------------------------------------------------------------------

-- | The backend-agnostic content of a single generated axiom.
--
-- Backends interpret each constructor as follows:
--
-- * 'ABDeclProp' — declare a nullary constant of propositional type.
--   Lean: @axiom name : Prop@.  Coq: @Axiom name : Prop.@
--
-- * 'ABDeclFunc' n — declare a function of arity @n@ (≥ 1) from @Prop@
--   to @Prop@.  Lean: @axiom name : Prop → … → Prop@.
--
-- * 'ABMereo' e — an axiom whose logical content is a mereological
--   expression.  The mapping is: @MSum@→conjunction, @MProd@→disjunction,
--   @MDiff@→reverse implication (@b → a@), @MRevDiff@→implication
--   (@a → b@), @MSymDiff@→biconditional, @MZero@→truth\/⊤.
--
-- * 'ABFuncEq' l r — assert that two function-typed entities are equal.
--   Use this (not 'ABMereo' with @MSymDiff@) when both sides are not
--   @Prop@-kinded, so that backends can emit @=@ rather than @↔@.
data AxiomBody
  = ABDeclProp
    -- ^ Declare a constant of type @Prop@.
  | ABDeclFunc Int
    -- ^ Declare a function @Prop → … → Prop@ of the given arity (≥ 1).
  | ABMereo IR.MereoExpr
    -- ^ Axiom with mereological content.
  | ABFuncEq String String
    -- ^ Assert that two named, non-@Prop@ entities are equal: @l = r@.
  deriving (Eq, Show)

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
  | TagAdjunction
    -- ^ States a Galois adjunction (left ⊣ right).
  | TagSorting
    -- ^ States that an object belongs to a particular sort.
  | TagOrdering
    -- ^ States how two sorts (or a sort and a bound) relate to each other.
  | TagDecomposition
    -- ^ States that a multi-arg function decomposes as dir-img ∘ tuple.
  | TagInvDecomposition
    -- ^ States that a tuple decomposes as a meet of inverse projections.
  | TagIRTupleProj
    -- ^ States the IR characterisation via tuple+projections.
  | TagIRProjFromTuple
    -- ^ States projection recovery from IR tuples.
  | TagIRSeparates
    -- ^ States the separation axiom for IR.
  | TagUserFact
    -- ^ A user-written assertion or metafact from the theory source.
  | TagImplicitMerge
    -- ^ An implicit merge fact connecting entities across subtheories.

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
       then error $ "Pipeline.AxiomSet.tags: sub-entity or origin tag present without TagFunction: "
                 ++ show ts
     else if hasIRRoleTag && not hasTagIR
       then error $ "Pipeline.AxiomSet.tags: IR role tag present without TagIR: "
                 ++ show ts
     else s

-- ---------------------------------------------------------------------------
-- Subject paths
-- ---------------------------------------------------------------------------

-- | One node in a subject path.
data SubjectNode
  = SGlobal
    -- ^ Not tied to any specific theory entity.
  | SSort String
    -- ^ A sort, identified by its name.
  | SSet String
    -- ^ A set declared with @⊆@, identified by its name.
  | SIndividual String
    -- ^ An individual declared with @:@, identified by name.
  | SFunction String
    -- ^ A function, identified by its name.
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
  | SResObject
    -- ^ The canonical result object of the parent entity.
  deriving (Eq, Ord, Show)

-- | A subject path: a non-empty list of 'SubjectNode' values.
--
-- Invariants (enforced by 'axiomSet'):
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
-- Each axiom is a @('String', 'AxiomBody')@ pair: the name is the
-- identifier emitted in the backend output; the body is the backend-agnostic
-- logical content.
--
-- Use 'axiomSet' to construct values; the smart constructor validates
-- invariants.
data AxiomSet = AxiomSet
  { asPath   :: SubjectPath          -- ^ where in the theory hierarchy
  , asTags   :: TagSet               -- ^ what kind of thing this is
  , asAxioms :: [(String, AxiomBody)] -- ^ (name, body) pairs (non-empty)
  } deriving (Eq, Show)

-- | Smart constructor for 'AxiomSet'.
--
-- Checks:
--
-- * @axs@ is non-empty.
-- * @path@ is non-empty.
-- * The first path node is 'SGlobal', 'SSort', 'SSet', 'SIndividual', or 'SFunction'.
-- * Sub-entity nodes only appear when the first node is 'SFunction'.
axiomSet :: SubjectPath -> TagSet -> [(String, AxiomBody)] -> AxiomSet
axiomSet path ts axs
  | null axs  = error "Pipeline.AxiomSet.axiomSet: empty axiom list"
  | null path = error "Pipeline.AxiomSet.axiomSet: empty subject path"
  | otherwise =
      let root = head path
          validRoot = case root of
            SGlobal       -> True
            SSort _       -> True
            SSet _        -> True
            SIndividual _ -> True
            SFunction _   -> True
            _             -> False
          subEntityNodes = tail path
          subEntityOk = case root of
            SFunction _ -> True
            _           -> null subEntityNodes
      in if not validRoot
           then error $ "Pipeline.AxiomSet.axiomSet: path must start with SGlobal/SSort/SSet/SIndividual/SFunction, got: " ++ show root
           else if not subEntityOk
             then error $ "Pipeline.AxiomSet.axiomSet: sub-entity nodes only allowed under SFunction, path: " ++ show path
             else AxiomSet { asPath = path, asTags = ts, asAxioms = axs }

-- ---------------------------------------------------------------------------
-- Pretty-printing helpers
-- ---------------------------------------------------------------------------

-- | Render a 'SubjectNode' as a human-readable string without escaping
-- Unicode characters (unlike the derived 'Show' instance, which would turn
-- @"𝕌"@ into @"\\120140"@).
prettySubjectNode :: SubjectNode -> String
prettySubjectNode SGlobal         = "SGlobal"
prettySubjectNode (SSort n)       = "SSort \"" ++ n ++ "\""
prettySubjectNode (SSet n)        = "SSet \"" ++ n ++ "\""
prettySubjectNode (SIndividual n) = "SIndividual \"" ++ n ++ "\""
prettySubjectNode (SFunction n)   = "SFunction \"" ++ n ++ "\""
prettySubjectNode SImage          = "SImage"
prettySubjectNode (SProjection k) = "SProjection " ++ show k
prettySubjectNode STuple          = "STuple"
prettySubjectNode SInverse        = "SInverse"
prettySubjectNode SIR             = "SIR"
prettySubjectNode (SArgObject k)  = "SArgObject " ++ show k
prettySubjectNode SResObject      = "SResObject"

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
