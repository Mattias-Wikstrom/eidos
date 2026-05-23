-- | Centralised naming conventions for compiler-generated identifiers.
--
-- Every suffix, prefix, and separator that the compiler appends or prepends
-- to user-defined names lives here.  Changing one of these values (e.g.
-- switching from @_Max@ to @_MAX@, or from @f_dom@ to @domain_of_f@) requires
-- editing only this module.
--
-- __What belongs here__: generated names that appear in the output and could
-- reasonably be changed in a future version of the language or compiler.
--
-- __What does not belong here__: names that are part of the Eidos surface
-- syntax (e.g. @#min@, @#max@, @#dom@), output-format-local conventions
-- (e.g. Lean or Coq fact indices), or names that are hardcoded in the
-- language specification and must never change (e.g. @𝕌@, @ℙ@, @𝔻@).
module Eidos.Pipeline.IRProcessing.NamingConventions
  ( -- * Sort limit names
    sortMin
  , sortMax
  , sortMinElem
  , sortMaxElem
  , sortIdentity

    -- * FOL function derived names
  , funRes
  , funArgN
  , funArg
  , funDom
  , funDirImg
  , funInvImg
  , funSet
  , funTuple
  , funPi
  , funPiInv

    -- * Axiom / fact names
  , axiomFact
  , axiomAdjunction
  , axiomImageAdjunction
  , axiomDecomposition
  , axiomInvDecomposition
  , axiomTupleWithProjections
  , axiomProjectionsFromTuple
  , axiomSeparates
  , axiomExtension

    -- * Sort ordering names
  , sortOrdering
  , sortUpper
  , sortLower
  , sortUniversalLower
  , funDomOrdering
  , funDomUpper
  , funDomLower

    -- * Sort / relation bound metafact names
    -- (relation bounds share these conventions intentionally)
  , boundSorting
  , boundMin
  , boundMax

    -- * IR predicate prefix
  , irPredicate

    -- * Implicit merge axiom name
  , mergeName

    -- * Sanitization helpers
  , sanitizeHash
  , safeMergeChar
  ) where

-- ---------------------------------------------------------------------------
-- Sort limit names
-- ---------------------------------------------------------------------------

-- | Lower limit of a sort.  Example: @"S"@ → @"S_Min"@
sortMin :: String -> String
sortMin s = s ++ "_Min"

-- | Upper limit of a sort.  Example: @"S"@ → @"S_Max"@
sortMax :: String -> String
sortMax s = s ++ "_Max"

-- | Identity relation name derived from a sort name.  Example: @"S"@ → @"S_identity"@
sortIdentity :: String -> String
sortIdentity s = s ++ "_identity"

-- | Reflected lower-limit individual of a sort.  Example: @"S"@ → @"S_min_elem"@
sortMinElem :: String -> String
sortMinElem s = s ++ "_min_elem"

-- | Reflected upper-limit individual of a sort.  Example: @"S"@ → @"S_max_elem"@
sortMaxElem :: String -> String
sortMaxElem s = s ++ "_max_elem"

-- ---------------------------------------------------------------------------
-- FOL function derived names
-- ---------------------------------------------------------------------------

-- | Result object of a function.  Example: @"f"@ → @"f_res"@
funRes :: String -> String
funRes fn = fn ++ "_res"

-- | N-th argument object of a multi-arg function (1-based).
--   Example: @"f" 2@ → @"f_2"@
funArgN :: String -> Int -> String
funArgN fn i = fn ++ "_" ++ show i

-- | Argument object of a unary function.  Example: @"f"@ → @"f_arg"@
funArg :: String -> String
funArg fn = fn ++ "_arg"

-- | Domain sort name derived from a function name.
--   Example: @"f"@ → @"f_dom"@
funDom :: String -> String
funDom fn = fn ++ "_dom"

-- | Direct-image function.  Example: @"f"@ → @"f_dir_img"@
funDirImg :: String -> String
funDirImg fn = fn ++ "_dir_img"

-- | Inverse-image function.  Example: @"f"@ → @"f_inv_img"@
funInvImg :: String -> String
funInvImg fn = fn ++ "_inv_img"

-- | Associated set of a function.  Example: @"f"@ → @"f_set"@
funSet :: String -> String
funSet fn = fn ++ "_set"

-- | Tuple (product) argument of a multi-arg function.
--   Example: @"f"@ → @"f_tuple"@
funTuple :: String -> String
funTuple fn = fn ++ "_tuple"

-- | K-th projection function.  Example: @"f" 1@ → @"f_pi_1"@
funPi :: String -> Int -> String
funPi fn k = fn ++ "_pi_" ++ show k

-- | Inverse of the k-th projection.  Example: @"f" 1@ → @"f_pi_1_inv"@
funPiInv :: String -> Int -> String
funPiInv fn k = fn ++ "_pi_" ++ show k ++ "_inv"

-- ---------------------------------------------------------------------------
-- Axiom / fact names
-- ---------------------------------------------------------------------------

-- | Connection-fact axiom.  Example: @"f"@ → @"f_fact"@
axiomFact :: String -> String
axiomFact fn = fn ++ "_fact"

-- | Adjunction axiom.  Example: @"f"@ → @"f_adjunction"@
axiomAdjunction :: String -> String
axiomAdjunction fn = fn ++ "_adjunction"

-- | Image-adjunction axiom.  Example: @"f"@ → @"f_image_adjunction"@
axiomImageAdjunction :: String -> String
axiomImageAdjunction fn = fn ++ "_image_adjunction"

-- | Decomposition axiom.  Example: @"f"@ → @"f_decomposition"@
axiomDecomposition :: String -> String
axiomDecomposition fn = fn ++ "_decomposition"

-- | Inverse-decomposition axiom.  Example: @"f"@ → @"f_inv_decomposition"@
axiomInvDecomposition :: String -> String
axiomInvDecomposition fn = fn ++ "_inv_decomposition"

-- | IR tuple-with-projections axiom.  Example: @"f"@ → @"f_tuple_with_projections"@
axiomTupleWithProjections :: String -> String
axiomTupleWithProjections fn = fn ++ "_tuple_with_projections"

-- | IR projections-from-tuple axiom.  Example: @"f"@ → @"f_projections_from_tuple"@
axiomProjectionsFromTuple :: String -> String
axiomProjectionsFromTuple fn = fn ++ "_projections_from_tuple"

-- | IR separates axiom.  Example: @"f"@ → @"f_separates"@
axiomSeparates :: String -> String
axiomSeparates fn = fn ++ "_separates"

-- | Extension axiom.  Example: @"f"@ → @"f_extension"@
axiomExtension :: String -> String
axiomExtension fn = fn ++ "_extension"

-- ---------------------------------------------------------------------------
-- Sort ordering names
-- ---------------------------------------------------------------------------

-- | Max-to-min ordering axiom for a sort.  Example: @"S"@ → @"S_ordering"@
sortOrdering :: String -> String
sortOrdering s = s ++ "_ordering"

-- | Upper-bound placement axiom for a sort.  Example: @"S"@ → @"S_upper"@
sortUpper :: String -> String
sortUpper s = s ++ "_upper"

-- | Lower-bound placement axiom for a sort.  Example: @"S"@ → @"S_lower"@
sortLower :: String -> String
sortLower s = s ++ "_lower"

-- | Auxiliary lower-bound axiom placing a sort's minimum within the universe minimum.
--   Example: @"S"@ → @"S_u_lower"@
sortUniversalLower :: String -> String
sortUniversalLower s = s ++ "_u_lower"

-- | Domain-ordering axiom for a multi-arg function.
--   Example: @"f"@ → @"f_dom_ordering"@
funDomOrdering :: String -> String
funDomOrdering fn = fn ++ "_dom_ordering"

-- | Domain-upper axiom for a multi-arg function.
--   Example: @"f"@ → @"f_dom_upper"@
funDomUpper :: String -> String
funDomUpper fn = fn ++ "_dom_upper"

-- | Domain-lower axiom for a multi-arg function.
--   Example: @"f"@ → @"f_dom_lower"@
funDomLower :: String -> String
funDomLower fn = fn ++ "_dom_lower"

-- ---------------------------------------------------------------------------
-- Sort / relation bound metafact names
-- ---------------------------------------------------------------------------
-- Relation bounds intentionally reuse the same conventions as sort bounds,
-- so renaming (e.g. "_min" → "_MIN") affects both uniformly.

-- | Collapsed sorting axiom (--sorting-axioms mode).
--   Example: @"f_res"@ → @"f_res_sorting"@
boundSorting :: String -> String
boundSorting obj = obj ++ "_sorting"

-- | Lower-bound metafact.  Example: @"f_res"@ → @"f_res_min"@
boundMin :: String -> String
boundMin obj = obj ++ "_min"

-- | Upper-bound metafact.  Example: @"f_res"@ → @"f_res_max"@
boundMax :: String -> String
boundMax obj = obj ++ "_max"

-- ---------------------------------------------------------------------------
-- IR predicate prefix
-- ---------------------------------------------------------------------------

-- | IR predicate name for a function.  Example: @"f"@ → @"IR_f"@
irPredicate :: String -> String
irPredicate fn = "IR_" ++ fn

-- ---------------------------------------------------------------------------
-- Implicit merge axiom name
-- ---------------------------------------------------------------------------

-- | Name for an implicit-merge axiom joining a fact from a subtheory.
--   @lhs@ should already be sanitized; @rhs@ is the subtheory path segment.
--   Example: @"myFact"@ @"SubTheory"@ → @"myFact_from_SubTheory"@
mergeName :: String -> String -> String
mergeName lhs rhs = lhs ++ "_from_" ++ rhs

-- ---------------------------------------------------------------------------
-- Sanitization helpers
-- ---------------------------------------------------------------------------

-- | Replace @#@ with @_@ in an IR object name, making it safe for use as
--   an identifier in output languages.
--   Example: @"f#res"@ → @"f_res"@
sanitizeHash :: String -> String
sanitizeHash = map (\c -> if c == '#' then '_' else c)

-- | Encode a single character from a user-defined name into a string that is
--   safe to embed in a generated axiom name.  Used when constructing names
--   for implicit-merge axioms.
safeMergeChar :: Char -> String
safeMergeChar c = case c of
  '+' -> "plus"; '-' -> "minus"; '×' -> "times"
  '⇒' -> "impl"; '∸' -> "sub";  '/' -> "div"
  '#' -> "_";    '.' -> "_";    _   -> [c]
