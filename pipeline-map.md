# Eidos `--lean_using_props` Pipeline Map

This document traces every entity, fact, and Lean axiom produced as a theory
passes through the two compilation stages: **FromSyntax** (IR construction)
and **MkAxiomSets / LeanProps** (Lean 4 output). Its goal is to make
redundancies and dead computations visible.

---

## Stage 1 — FromSyntax: what goes into the IR

`decorateTheoryBody` runs four passes in sequence. Below is a complete
inventory of what each pass deposits into `Theory`.

### Bootstrap: `createTheory`

Before any pass runs, every theory — including every subtheory — receives
these objects unconditionally:

| IR field / object | Name | Kind |
|---|---|---|
| `theoryUniverse` | `𝕌` | `SortKindUniverse` |
| `theoryDomain` | `𝔻` | `SortKindDomain` |
| `theoryProp` | `ℙ` | `SortKindProp` |
| `theoryTruth` | `⊤` | `MereologicalEntityKindProposition` |
| `theoryFalsity` | `⊥` | `MereologicalEntityKindProposition` |
| `theorySum` | `+` | `FunctionKindMereologicalOperation` |
| `theoryProd` | `×` | `FunctionKindMereologicalOperation` |
| `theoryDiff` | `-` | `FunctionKindMereologicalOperation` |
| `theoryRevDiff` | `⇒` | `FunctionKindMereologicalOperation` |
| `theorySymDiff` | `∸` | `FunctionKindMereologicalOperation` |
| initial fact | `⊤ = ℙ#min` | `FactKindSortLimitation` |
| initial fact | `⊥ = ℙ#max` | `FactKindSortLimitation` |

`theoryUsesDomain` and `theoryUsesProp` start `False`; they are set `True`
lazily as the signature and axiom passes encounter references to `𝔻`/`ℙ`.

### Pass 0 (pre-pass): `addSortToTh` for the three built-in sorts

Immediately after `createTheory`, `addSortToTh` is called on `𝕌`, `𝔻`, and
`ℙ`. For each sort `S` this does:

1. Adds `EntitySort S` to `theoryObjects`.
2. Adds `EntityMereological S#min` (`MereologicalEntityKindLowerLimitForSort`).
3. Adds `EntityMereological S#max` (`MereologicalEntityKindUpperLimitForSort`).
4. Emits `ℙ#max ≤ S#min` (`FactKindSortLimitation`) — *skipped for `ℙ` and `𝕌` itself*.
5. Emits `𝕌#min ≤ S#min` and `S#max ≤ 𝕌#max` (`FactKindSortLimitation`) — *skipped for `𝕌` itself*.

So the three built-in sorts produce 3 sort entities + 6 limit objects +
up to 5 ordering facts (exact count depends on which sorts trigger the guards).

### Pass 1: Subtheories

For each subtheory entry:

1. `decorateTheoryBody` is called recursively → the sub-`Theory` is fully built.
2. `addSubtheoryToTheory`: appends sub to `theorySubtheories`.
3. `propagateSubtheory`: for every `(name, [entity, ...])` in the sub's
   `theoryObjectsByName`:
   - Always: registers `sub.name → entity` in the parent's `theoryObjectsByName`
     (as the qualified name).
   - **Implicit subtheories only**: for each plain (non-`#`) name —
     - If the name is new in the parent: creates a canonical copy
       (`createCanonicalEntity`) with `origin = FromSubtheory` and registers it
       under the unqualified name; then emits `name = sub.name`
       (`FactKindImplicitMerge`).
     - If the name exists and is compatible: emits `name = sub.name`
       (`FactKindImplicitMerge`) only — no new entity.
     - If the name exists and is **incompatible**: appends to the slot; the
       slot becomes ambiguous (multi-entry list). **No** equality fact is
       emitted; name lookup will fail with "Ambiguous name".
     - Sort limits (`#min`/`#max`), `⊤`, `⊥` are **skipped** for
       unqualified registration and equality emission.
4. If implicit: propagates `theoryUsesDomain` / `theoryUsesProp` from sub to parent.
5. **Reflection subtheories**: each entity passes through `reflectEntity`
   before registration:
   - SOL functions → `FunctionKindFOLFunctionFromTheory` + `funcReflectedFrom = Just subTh`
   - Sorts → `SortKindFromReflection` + `sortReflectedFrom = Just subTh`
   - Mereological objects → `MereologicalEntityKindIndividual` + `mereoReflectedFrom = Just subTh`

### Pass 2: Signature

For each `SignatureItem`:

**`sort S`** (simple sort)

| Added to IR | Detail |
|---|---|
| `EntitySort S` | `SortKindFromSignature`, `origin = FromSignature` |
| `EntityMereological S#min` | `MereologicalEntityKindLowerLimitForSort` |
| `EntityMereological S#max` | `MereologicalEntityKindUpperLimitForSort` |
| Fact `ℙ#max ≤ S#min` | `FactKindSortLimitation` |
| Fact `𝕌#min ≤ S#min` | `FactKindSortLimitation` |
| Fact `S#max ≤ 𝕌#max` | `FactKindSortLimitation` |

`theoryUsesDomain` / `theoryUsesProp` are updated via `markTheorySortExprUsage`.

**`T subsort S`** (relational sort)

Same as simple sort, plus the relational sort has `sortRelationship = SubSort`,
`sortParent = Just S`, and two additional facts:

| Fact | Kind |
|---|---|
| `T#min = S#min` | `FactKindSortLimitation` |
| `T#max ≤ S#max` | `FactKindSortLimitation` |

For `quotient`: `S#min ≤ T#min` and `T#max = S#max`.  
For `subquotient`: `S#min ≤ T#min` and `T#max ≤ S#max`.

**`F : A → B` (SOL, uppercase)**

| Added to IR | Detail |
|---|---|
| `EntityFunction F` | `FunctionKindSOLFunctionFromTheory` |
| `MereologicalObject F#1` (one per arg) | `MereologicalEntityKindArgumentOfSOLFunction` |
| `MereologicalObject F#res` | `MereologicalEntityKindResultOfSOLFunction` |

No domain sort, no inverse, no image functions.

**`f : A → B` (FOL, lowercase)** — the biggest generator

| Added to IR | Detail |
|---|---|
| `EntityFunction f` | `FunctionKindFOLFunctionFromTheory` |
| `MereologicalObject f#1` (one per arg) | `MereologicalEntityKindArgumentOfSOLFunction` |
| `MereologicalObject f#res` | `MereologicalEntityKindResultOfSOLFunction` |
| `MereologicalObject f#arg` | `MereologicalEntityKindArgumentOfSOLFunction` — the product-sort representative |
| `EntitySort f#dom` | `SortKindProduct`, `sortComponentSorts = argSorts` |
| `EntityMereological f#dom#min` | lower limit for `f#dom` |
| `EntityMereological f#dom#max` | upper limit for `f#dom` |
| `EntityFunction f_inv` | `FunctionKindFOLFunctionFromTheory`, maps `B → A` |
| `EntitySort f_inv#dom` | `SortKindProduct`, `sortComponentSorts = [resSort]` |
| `EntityMereological f_inv#dom#min` | lower limit for `f_inv#dom` |
| `EntityMereological f_inv#dom#max` | upper limit for `f_inv#dom` |
| `EntityFunction f#dir_img` | `FunctionKindDirectImageFunction`, maps `f#dom → B` |
| `MereologicalObject f#dir_img#1` | argument object for `f#dir_img` |
| `MereologicalObject f#dir_img#res` | result object for `f#dir_img` |
| `EntityFunction f#inv_img` | `FunctionKindInverseImageFunction`, maps `B → f#dom` |
| `MereologicalObject f#inv_img#1` | argument object for `f#inv_img` |
| `MereologicalObject f#inv_img#res` | result object for `f#inv_img` |

**No facts** are emitted at signature time for functions; all function
properties become Lean axioms generated entirely in Stage 2.

Note: `f_inv` has no `funcDirectImage` or `funcInverseImage` set (both
`Nothing`) because multi-argument inverses are not automatically generated.
Only single-argument FOL functions (`folSingleArgFunctions` in `MkAxiomSets`)
participate in the FOL adjunction axioms.

**`x : S` (individual)**

| Added to IR | Detail |
|---|---|
| `EntityMereological x` | `MereologicalEntityKindIndividual` (or `MereologicalEntityKindProposition` if `S = ℙ`) |

**`X ⊆ S` (singleton set)**

| Added to IR | Detail |
|---|---|
| `EntityMereological X` | `MereologicalEntityKindSet` |

**`r ⊆ A, B` (binary+ relation)**

| Added to IR | Detail |
|---|---|
| `EntityRelation r` | |
| `Sort r#dom` | `SortKindProduct`, `sortComponentSorts = [A, B]` |
| `MereologicalObject r#arg` | `MereologicalEntityKindIndividual` |
| `MereologicalObject r#set` | `MereologicalEntityKindSet` (associated with `head argSorts`) |
| `MereologicalObject r#1`, `r#2` (one per sort) | `MereologicalEntityKindArgumentOfSOLFunction` |

### Pass 3: Axioms

For each `fact`/`assertion`/`metafact` item, one `Fact` is appended to
`theoryFacts`:

| Field | Value |
|---|---|
| `factKind` | `FactKindFact`, `FactKindAssertion`, or `FactKindMetafactsFact` |
| `factIsMereologicalTranslation` | `False` |
| `factIsInherited` | `False` (always — **see note below**) |
| `factFreeVars` | resolved free variable declarations |
| `factPropExpr` | fully resolved expression |

`markTheoryPropExprUsage` updates `theoryUsesProp` if the expression uses any
logical connective or ℙ-sorted variable.

### Pass 4: Mereological translations

For every `Fact` already in `theoryFacts` at the end of pass 3:

- **`FactKindAssertion`**: a new `Fact` is appended with
  `factIsMereologicalTranslation = True` and the expression structurally
  rewritten (→ becomes ⇒, ↔ becomes ∸, ∧ becomes +, ∨ becomes ×,
  ¬ stays as `ResolvedNegNot`, = becomes ∸, ∈/⊆/≤ become -).
- **`FactKindFact`**: a new `Fact` is appended with
  `factIsMereologicalTranslation = True` and the expression **unchanged**
  (the fact is marked as a translation but the expression is not actually
  transformed — this is a potential bug or a deliberate no-op placeholder).
- **`FactKindMetafactsFact`**, **`FactKindSortLimitation`**,
  **`FactKindImplicitMerge`**: **no translation** is emitted.

---

## Dead / always-false IR fields

| Field | Status |
|---|---|
| `factIsInherited` | **Always `False`**. The field is declared, filtered on in `MkAxiomSets`, but never set `True` anywhere in `FromSyntax`. Every filter `not (factIsInherited f)` is a vacuous no-op. |
| `SortKindFromReflection` | Set by `reflectEntity` on reflected sorts, but no code path in the compiler currently branches on it — it is a pure marker reserved for future passes. |
| `FunctionKindFOLFunctionFromReflection` | Defined in `EntityKind` but never assigned by `mkFOLFunction` or `reflectEntity` (reflected functions use `FunctionKindFOLFunctionFromTheory`). May be dead. |

---

## Stage 2 — MkAxiomSets: what Lean axioms are generated

`mkAxiomSets` reads the IR and emits 43 numbered groups of `AxiomSet` values.
The table below shows, for each group, which IR objects it reads and what
Lean axiom names it produces. Names use `f` for a function, `S` for a sort,
`X` for a mereological object, and the naming conventions from `MkAxiomSets`.

**Input lists computed once** (all are list comprehensions over `theoryObjects`
and `theoryFacts`):

| Name | What it contains |
|---|---|
| `userSorts` | `EntitySort` where `sortKind = SortKindFromSignature` |
| `solFunctions` | `EntityFunction` where `funcKind = FunctionKindSOLFunctionFromTheory` |
| `folFunctions` | `EntityFunction` where `funcKind = FunctionKindFOLFunctionFromTheory` |
| `folSingleArgFunctions` | `folFunctions` with exactly 1 arg sort, `origin = FromSignature` |
| `multiArgFolFunctions` | `folFunctions` with 2+ arg sorts, `origin = FromSignature` |
| `userDeclaredFolFunctions` | all `folFunctions` with `origin = FromSignature` |
| `functionObjects` | arg + result `MereologicalObject`s of SOL and user FOL functions |
| `individualObjects` | `EntityMereological` where `kind = Individual`, `origin = FromSignature`, name not a built-in limit |
| `mereoObjects` | `EntityMereological` where `kind = Mereological`, `origin = FromSignature`, name not a built-in limit |
| `propObjects` | `EntityMereological` where `kind = Proposition`, `origin = FromSignature`, name not `ℙ_Min/Max`, `⊤/⊥`, `ℙ#min/max` |
| `setObjects` | `EntityMereological` where `kind = Set`, `origin = FromSignature`, `mereoSort.kind = SortKindDomain` (only if `usesDomain`) |
| `userSortSets` | `EntityMereological` where `kind = Set`, `origin = FromSignature`, `mereoSort.kind = SortKindFromSignature` |
| `userFacts` | `FactKindFact`, not inherited, not mereo translation |
| `userAssertions` | `FactKindAssertion`, not inherited, not mereo translation |
| `userMetafacts` | `FactKindMetafactsFact`, not inherited, not mereo translation |
| `implicitMergeFacts` | `FactKindImplicitMerge`, not inherited, not mereo translation |

### Axiom group table

| # | Group name | Reads from IR | Lean axiom names produced |
|---|---|---|---|
| 1 | Header: built-in sort limits | `usesDomain` flag | `𝕌_Min`, `𝕌_Max`, `ℙ_Min`, `ℙ_Max`; optionally `𝔻_Min`, `𝔻_Max` — all typed `: Prop` |
| 2 | User sort limit objects | `userSorts` | `S_Min`, `S_Max` for each user sort `S` |
| 3 | Product sort limit objects | `multiArgFolFunctions` | `f_dom_Min`, `f_dom_Max` for each multi-arg FOL `f` |
| 4 | Function declarations | `solFunctions`, `userDeclaredFolFunctions` | `f : Prop → Prop → … → Prop` (one per arg, via `functionType`) |
| 5 | Image function declarations | `multiArgFolFunctions` | `f_dir_img : Prop → Prop`, `f_inv_img : Prop → Prop` |
| 6 | Projection declarations | `multiArgFolFunctions` | `f_pi_k : Prop → Prop` for each `k` |
| 7 | Inverse projection declarations | `multiArgFolFunctions` | `f_pi_k_inv : Prop → Prop` for each `k` |
| 8 | Tuple function declarations | `multiArgFolFunctions` | `f_tuple : Prop → … → Prop` |
| 9 | FOL inverse declarations | `folSingleArgFunctions` | `f_inv : Prop → Prop` |
| 10 | IR predicate declarations | `multiArgFolFunctions` | `IR_f : Prop → Prop` |
| 11 | Function arg/result object declarations | `solFunctions`, `userDeclaredFolFunctions` | `f_k`, `f_res` for each arg/result object (sanitized `#` → `_`) |
| 12 | FOL inverse arg/res declarations | `folSingleArgFunctions` | `f_inv_1`, `f_inv_res` |
| 13 | Product arg declarations + sorting | `multiArgFolFunctions` | `f_arg` declaration; `f_arg_min`, `f_arg_max` sorting axioms |
| 14 | Projection witness declarations | `multiArgFolFunctions` | `f_pi_k_1`, `f_pi_k_res` for each `k` |
| 15 | Inverse image witness declarations + sorting | `multiArgFolFunctions` | `f_inv_img_arg`, `f_inv_img_res` declarations; `…_min`/`…_max` sorting axioms |
| 16 | Mereological object declarations | `mereoObjects` | `X : Prop` for each `X` |
| 17 | Proposition declarations | `propObjects` | `P : Prop` for each `P` |
| 18 | Set declarations | `setObjects ++ userSortSets` | `X : Prop` for each set/relation object |
| 19 | Function arg/result object sorting | `functionObjects` (SOL + user FOL arg/res) | `n_min`, `n_max` sorting axioms (`ℙ_Min → (n → S_Min)` pattern) |
| 20 | FOL inverse arg/res sorting | `folSingleArgFunctions` | `f_inv_1_min/max`, `f_inv_res_min/max` |
| 21 | Projection witness sorting | `multiArgFolFunctions` | `f_pi_k_1_min/max`, `f_pi_k_res_min/max` for each `k` |
| 22 | Function connection axioms | `solFunctions`, `userDeclaredFolFunctions` | `f_fact` — bounded-∀ biconditional linking arg/res objects to function application |
| 23 | FOL inverse connection axioms | `folSingleArgFunctions` | `f_inv_fact` |
| 24 | Direct image connection axioms | `multiArgFolFunctions` | `f_dir_img_fact` |
| 25 | Inverse image connection axioms | `multiArgFolFunctions` | `f_inv_img_fact` |
| 26 | FOL adjunction axioms | `folSingleArgFunctions` | `f_adjunction` — `(Y → f(X)) ↔ (f_inv(Y) → X)` |
| 27 | Image adjunction axioms | `multiArgFolFunctions` | `f_image_adjunction` — same shape for `f_dir_img`/`f_inv_img` |
| 28 | Decomposition axioms | `multiArgFolFunctions` | `f_decomposition` — `f(X1,…) = f_dir_img(f_tuple(X1,…))` |
| 29 | Tuple connection axioms | `multiArgFolFunctions` | `f_tuple_fact` — links `f#arg` to `f_tuple` |
| 30 | Projection connection axioms | `multiArgFolFunctions` | `f_pi_k_fact` for each `k` |
| 31 | Projection adjunction axioms | `multiArgFolFunctions` | `f_pi_k_adjunction` for each `k` |
| 32 | Tuple inverse decomposition | `multiArgFolFunctions` | `f_tuple_inv_decomposition` — `f_tuple = ∩ f_pi_k_inv` |
| 33 | IR tuple-with-projections | `multiArgFolFunctions` | `IR_f_tuple_with_projections` — `IR_f(Z) ↔ Z = f_tuple(π1(Z),…)` |
| 34 | IR projections-from-tuple | `multiArgFolFunctions` | `IR_f_projections_from_tuple` — `IR_f(tuple(X1,…)) ↔ πk(tuple)=Xk` |
| 35 | IR separates | `multiArgFolFunctions` | `IR_f_separates` — `X=Y ↔ ∀Z.IR_f(Z)→((X→Z)↔(Y→Z))` |
| 35b | Individual declarations | `individualObjects` | `x : Prop` for each individual |
| 36 | Mereological object bounds | `mereoObjects` | `X_min : X → 𝕌_Min`, `X_max : 𝕌_Max → X` |
| 36a | Individual bounds | `individualObjects` | `x_min : x → S_Min`, `x_max : S_Max → x` for sort `S` |
| 37 | Proposition bounds | `propObjects` | `P_min : P → ℙ_Min`, `P_max : ℙ_Max → P` |
| 38 | 𝔻-sort set bounds | `setObjects` | `X_min : X → 𝔻_Min`, `X_max : 𝔻_Min → X` |
| 39 | User sort set bounds | `userSortSets` | `X_min : X → S_Min`, `X_max : S_Max → X` |
| 40 | Sort ordering axioms | `usesDomain`, `userSorts` | `𝕌_ordering`, `ℙ_upper/ordering/lower`, optionally `𝔻_upper/ordering/lower`, then `S_upper/ordering/lower` for each user sort (with adjusted forms for subsort/quotient/subquotient) |
| 41 | Product sort ordering | `multiArgFolFunctions` | `f_dom_upper/ordering/lower` |
| 42 | User fact axioms | `userFacts`, `userAssertions`, `userMetafacts` | `ax1`, `ax2`, … (or anonymous if only one) — each wrapped with `LFactWrapper`, `LAssertionWrapper`, or `LMetafactWrapper` |
| 43 | Implicit merge axioms | `implicitMergeFacts` | `X_from_subtheory` — `X = sub.X` (metafact-wrapped for non-functions, plain `=` for functions) |

### The three fact wrappers (rendering)

`LFactWrapper`, `LAssertionWrapper`, and `LMetafactWrapper` expand during
`renderLeanExpr` in `LeanExpr.hs`:

| Wrapper | Lean rendering |
|---|---|
| `LFactWrapper(body)` | `(ℙ_Min ∧ body) ↔ ℙ_Min` |
| `LAssertionWrapper(body)` | `(ℙ_Min ∧ (ℙ_Max ∨ body)) ↔ ℙ_Min` |
| `LMetafactWrapper(body)` | `(𝕌_Min ∧ body) ↔ 𝕌_Min` |

---

## What the IR produces that Lean never reads

| IR object / fact | Lean fate |
|---|---|
| `FactKindSortLimitation` facts | **Never emitted to Lean.** All sort ordering relationships are re-derived from scratch in groups 40–41 by reading `sortRelationship` and `sortParent` directly. |
| Mereological translation of `FactKindFact` (pass 4 clone with `factIsMereologicalTranslation = True`) | **Never emitted to Lean.** `userFacts` filters out mereo translations. The mereo translation of a `fact` is therefore computed and stored but then completely ignored. |
| `f_inv` (the `f_inv` FOL inverse function entity stored in `theoryObjects`) | Used only indirectly: `folSingleArgFunctions` picks up `f_inv` because it has `funcKind = FunctionKindFOLFunctionFromTheory` and a single arg. Wait — actually `f_inv` **is** picked up by `theoryFOLFunctions` (it matches the kind) and therefore appears in `folFunctions`. It then enters `folSingleArgFunctions` if it has exactly one arg. Its axioms (groups 9, 12, 20, 23, 26) are all generated from `folSingleArgFunctions`. So `f_inv` **is** used — but via the `folSingleArgFunctions` filter, not via `funcInverseImage`. |
| `funcInverseImage` field on the main function `f` (pointing to `f#inv_img`) | **Never read in Lean generation.** `f#inv_img` is instead found by `IR.theoryObjects`-based filtering (`FunctionKindInverseImageFunction`). The `funcInverseImage` pointer is dead in the Lean backend. |
| `funcDirectImage` field on the main function `f` (pointing to `f#dir_img`) | Same: **never read**. `dirImgName f` constructs the name from `funcName` directly; the pointer is never followed. |
| `funcArgument` field (`f#arg` mereo object) | **Read in groups 13, 24, 29** via `IR.funcArgument f`. Not dead. |
| `sortAssociatedEntity` on product sorts | **Never read** in Lean generation. Exists for potential future use. |
| `theoryUsesProp` flag | **Never read** in Lean generation. `MkAxiomSets` always emits the ℙ limit axioms (`pMinName`, `pMaxName`) regardless, because `propObjects` filtering is based on `mereoKind` and `origin`, not on this flag. The flag is only read if you want to conditionally suppress ℙ, which nothing currently does. |
| `theoryUsesDomain` flag | **Is read** — group 1 and group 40 (and `setObjects`) gate on `usesDomain`. |
| `mereoObjects` (bare `𝕌`-typed objects) | Groups 16 and 36. Used. |
| `theoryClosestReflectionAncestor` | Used in `mereologicalTranslation` (pass 4) to qualify mereological operators in reflected contexts. Not read at all in Lean generation. |
| Reflection subtheories (`theoryReflection = True`) | `theoryBlocks` skips them entirely: `| IR.theoryReflection sub = []`. Lean generation of reflected content is not yet implemented. |

---

## Potential redundancies

**Sort ordering facts computed twice.** The IR contains `FactKindSortLimitation`
facts encoding every relationship like `T#min = S#min` (from `relationalSortFacts`)
and `ℙ#max ≤ S#min` (from `relateSortToProp`). These are stored in `theoryFacts`
but are **never read by MkAxiomSets**. Instead, groups 40–41 independently
re-derive the same information by reading `sortRelationship` and `sortParent`
from the sort objects. The IR facts and the Lean axioms express the same
constraints via two completely separate computations.

**Mereological translation of `FactKindFact`.** Pass 4 of `FromSyntax` clones
every `FactKindFact` with `factIsMereologicalTranslation = True`, but leaves
the expression unchanged (unlike assertions, which get the operator-swapping
translation). These clones are then filtered out by every `userFacts`-style
comprehension in `MkAxiomSets`. They are created and immediately become
unreachable.

**`funcDirectImage` and `funcInverseImage` pointers.** `mkFOLFunction` stores
these back-pointers on the main function record, but neither is ever
dereferenced in the Lean backend. Lean generation finds `f#dir_img` and
`f#inv_img` by constructing their names from `funcName` (via `dirImgName` and
`invImgName`). The pointer fields are therefore redundant with respect to Lean
output (they may be useful to other backends or inspectors).

**`theoryUsesProp` never gates any Lean output.** The flag's purpose — to
allow conditional omission of ℙ-related declarations — is not yet acted upon.
