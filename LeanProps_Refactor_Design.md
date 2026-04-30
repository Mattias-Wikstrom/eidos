# LeanProps Refactor Design

## Motivation

The current `LeanProps.hs` (≈1400 lines) conflates two concerns:

1. **What** to emit — the logical content of each axiom set
2. **How** to group and render it — ordering, blank lines, future macro choices

The result is that the generation code is hard to unit-test at a meaningful
level (tests must look at raw `LeanExpr` trees), and adding new rendering
strategies (macros, grouped-by-subject output, combined axioms) requires
touching the generation code.

The refactor introduces a **mid-level IR** (`AxiomSet`) that sits between
`Eidos.IR` and `LeanDoc`.  Generation produces `AxiomSet` values; rendering
consumes them.

---

## New type: `AxiomSet`

```haskell
-- | A named, tagged group of related axioms, together with the subject they
-- pertain to.  This is the unit that tests and renderers operate on.
data AxiomSet = AxiomSet
  { asTag     :: Tag          -- ^ what kind of thing this is
  , asSubject :: Subject      -- ^ what theory entity it pertains to
  , asAxioms  :: [LeanAxiom]  -- ^ the actual axioms (1 or more)
  } deriving (Eq, Show)
```

### Tags

```haskell
data Tag
  -- Declarations
  = TagSortLimit          -- ^ U_Min / U_Max / P_Min / P_Max / S_Min / S_Max …
  | TagFunctionDecl       -- ^ axiom f : Prop → Prop → Prop
  | TagFunctionFact       -- ^ f_fact (witness biconditional)
  | TagWitnessDecl        -- ^ f_1, f_2, f_res (canonical element witnesses)
  | TagWitnessBounds      -- ^ f_1_min / f_1_max (witness bounds)
  | TagAdjunction         -- ^ g_adjunction / f_pi_1_adjunction …
  | TagImageFunction      -- ^ f_dir_img, f_inv_img declarations
  | TagImageFact          -- ^ f_dir_img_fact, f_inv_img_fact
  | TagImageAdjunction    -- ^ f_image_adjunction
  | TagProjectionDecl     -- ^ f_pi_1, f_pi_2 declarations
  | TagProjectionFact     -- ^ f_pi_1_fact (witness biconditional)
  | TagProjectionInvDecl  -- ^ f_pi_1_inv declaration
  | TagProjectionAdjunction -- ^ f_pi_1_adjunction
  | TagTupleDecl          -- ^ f_tuple declaration
  | TagTupleFact          -- ^ f_tuple_fact (witness biconditional)
  | TagTupleInvDecomp     -- ^ f_tuple_inv_decomposition
  | TagDecomposition      -- ^ f_decomposition (f = f_dir_img ∘ f_tuple)
  | TagIRDecl             -- ^ IR_f declaration
  | TagIRTupleProj        -- ^ IR_f_tuple_with_projections
  | TagIRProjFromTuple    -- ^ IR_f_projections_from_tuple
  | TagIRSeparates        -- ^ IR_f_separates
  | TagSortOrder          -- ^ S_upper / S_ordering / S_lower / S_lower_min …
  | TagSubsort            -- ^ S1_min / S1_max
  | TagUserFact           -- ^ ax1, ax2 … (user-written assertions/metafacts)
  | TagInverseDecl        -- ^ g_inv declaration
  | TagInverseFact        -- ^ g_inv_fact
  | TagProductSortLimit   -- ^ f_dom_Min / f_dom_Max
  | TagProductSortOrder   -- ^ f_dom_upper / f_dom_ordering / f_dom_lower
  deriving (Eq, Ord, Show, Enum, Bounded)
```

### Subjects

```haskell
data Subject
  = SubjectGlobal              -- ^ not tied to any single entity (e.g. U/P decls)
  | SubjectSort   String       -- ^ a sort (e.g. "S", "T")
  | SubjectSubsort String      -- ^ a subsort (e.g. "S1")
  | SubjectFunction String     -- ^ a function (e.g. "f", "g", "k")
  | SubjectProjection String Int -- ^ k-th projection of function (e.g. "f" 1)
  deriving (Eq, Ord, Show)
```

---

## New type: `BoundedForall`

The single most common pattern in the output is:

```
forall X : Prop, (IsWithinBounds lo hi X) → body
```

Rather than building `LForallKw "X" LProp (LImpl (LIsWithinBounds lo "X" hi) body)`
everywhere, introduce a smart constructor and a dedicated `LeanExpr` node:

```haskell
-- Add to LeanExpr:
| LBoundedForall String String String LeanExpr
  -- ^ LBoundedForall varName loName hiName body
  -- Renders as: forall varName : Prop, (IsWithinBounds loName hiName varName) → body
```

This makes the tree introspectable — a test can pattern-match on
`LBoundedForall` rather than peeling apart nested `LForallKw`/`LImpl`/`LIsWithinBounds`.

Smart constructor:

```haskell
boundedForall :: String -> String -> String -> LeanExpr -> LeanExpr
boundedForall var lo hi = LBoundedForall var lo hi
```

Similarly introduce:

```haskell
-- Add to LeanExpr:
| LSortBounds String String
  -- ^ LSortBounds lo hi
  -- Represents the *pair* of bounds axioms for one entity.
  -- Renders as two axioms (or one combined axiom, depending on config).
  -- lo : entity → lo_Min
  -- hi : hi_Max → entity
```

This directly addresses your `S1_min / S1_max` example — the logical
content is "S1 is bounded by S", which is one thought, currently split into
two axioms for rendering convenience.

---

## Pipeline

```
IR.Theory
    │
    ▼
[mkAxiomSets] :: IR.Theory → [AxiomSet]   -- pure, easily tested
    │
    ▼
[renderConfig] :: RenderConfig            -- controls grouping strategy
    │
    ▼
[axiomSetsToLeanDoc] :: RenderConfig → [AxiomSet] → LeanDoc
    │
    ▼
[renderLeanDoc] :: LeanDoc → String       -- unchanged
```

### `RenderConfig`

```haskell
data RenderConfig = RenderConfig
  { rcGroupBy        :: GroupBy
  , rcCombineBounds  :: Bool   -- combine _min/_max into one axiom?
  , rcBoundedForallStyle :: BFStyle  -- keyword or ∀ symbol?
  }

data GroupBy
  = GroupByOrder    -- current behaviour: fixed declaration order
  | GroupBySubject  -- all axioms for "f" together, then "g", etc.
  | GroupByTag      -- all adjunctions together, all facts together, etc.

data BFStyle
  = BFKeyword   -- forall X : Prop, (IsWithinBounds …) → …   (current)
  | BFSymbol    -- ∀ X : Prop, (IsWithinBounds …) → …
  | BFMacro     -- ∀ X ∈ [lo, hi], …                         (future)
```

---

## What this buys you

### Testing

Instead of:

```haskell
hasType doc (LImpl (LIsWithinBounds "S_Min" "X" "S_Max") (LImpl ...))
```

you can write:

```haskell
let sets = mkAxiomSets theory
adjunctions = filter ((== TagAdjunction) . asTag) sets
fAdjunctions = filter ((== SubjectFunction "f") . asSubject) adjunctions
-- then inspect fAdjunctions directly
```

Or even just count:

```haskell
length (filter ((== TagProjectionFact) . asTag) sets)
  `shouldBe` 2  -- for a binary function
```

### Future grouping

Grouping all axioms about `f` together becomes a one-liner filter on `asSubject`.
Grouping all adjunctions together is a one-liner filter on `asTag`.

### Combined bounds axioms

With `rcCombineBounds = True`, `axiomSetsToLeanDoc` can render an `AxiomSet`
with `TagSubsort` and `asAxioms = [min_ax, max_ax]` as a single combined axiom:

```lean
axiom S1_bounds : (S1 → S_Min) ∧ (S_Max → S1)
```

---

## Migration plan

The refactor can be done without breaking the existing tests or the existing
public API (`exportToLeanProps`, `theoryToLeanDoc`, `renderLeanDoc`) by:

1. Adding `AxiomSet`, `Tag`, `Subject`, `BoundedForall` as new types
2. Writing `mkAxiomSets :: IR.Theory → [AxiomSet]` (new, tested separately)
3. Writing `axiomSetsToLeanDoc :: RenderConfig → [AxiomSet] → LeanDoc`
4. Rewriting `theoryToLeanDoc` to call `mkAxiomSets` then `axiomSetsToLeanDoc`
   with a default `RenderConfig` — same output as before, all existing tests pass
5. Gradually migrating the per-section generation helpers to use `mkAxiomSets`

This means the refactor can be done incrementally, section by section, with
the test suite as a safety net at every step.

---

## What stays the same

- `LeanDoc`, `LeanDecl`, `LeanAxiom` — unchanged public types
- `renderLeanDoc` — unchanged
- `renderLeanExpr` — extended with one new constructor (`LBoundedForall`)
  but otherwise unchanged
- The public entry point `exportToLeanProps`
- All existing tests (they test `LeanDoc` content, which is still produced)