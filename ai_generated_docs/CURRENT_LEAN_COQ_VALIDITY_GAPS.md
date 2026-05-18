# Current Lean/Coq Output: Likely Invalid Target Code (as of 2026-05-18)

This note summarizes issues in the **current output generators** that can cause exported code to fail as valid target language code, or to be semantically malformed enough that downstream checking fails.

## Scope and limitations

- This report is based on repository inspection of exporter code and tests.
- In this environment, `cabal`, `lean`, and `coqc` are not available, so full end-to-end compilation of generated files was not possible.
- Therefore, items below are either:
  1. directly confirmed by existing regression docs/tests in this repo, or
  2. high-confidence static findings from renderer code paths.

---

## Lean output (`--lean_using_props`)

### Confirmed translation gaps that can break practical Lean validity

1. **`facts { ... }` are not exported as user axioms in the expected way.**
   This is documented as a known gap and covered by pending tests.

2. **Biconditional chains are truncated.**
   Expressions like `A ↔ B ↔ C` are not fully preserved; only part of the chain is currently translated.

3. **Relation sort qualifiers are ignored.**
   Qualified relations like `=^S` are parsed but the qualifier is not used in Lean translation.

4. **Theory-qualified evaluation drops theory path information.**
   `<<theory.path>>(...)` currently ignores the explicit theory path in translation.

5. **Generalized `Σ` / `Π` forms drop operator and binder.**
   The current exporter translates only the operand term, not the generalized operator structure.

6. **Singleton term `{t}` is flattened to `t`.**
   Singleton constructor distinctions are erased in translation.

### Why these matter for Lean validity

Even when syntax parses, these gaps can yield generated declarations that are not faithful to source structure and can fail downstream proof/use expectations. In practical Lean workflows, this often presents as target files that are unusable or rejected once referenced in expected ways.

---

## Coq output (`--coq_using_props`)

### Current status from repository evidence

- There is no Coq-specific gap-tracking document analogous to `LEAN_USING_PROPS_GAPS.md` in this repository.
- The Coq and Lean exporters share the same upstream IR preparation and many shape-level translation decisions; therefore, **the same classes of structural loss are plausible** in Coq output unless explicitly handled differently in `CoqProps`.

### High-confidence risk categories for invalid Coq output

1. **Lossy translation of source constructs** (e.g., dropped qualifiers/binders/paths) can produce Coq code that is syntactically valid but semantically wrong for expected typing/use.
2. **Name/rendering edge cases** (Unicode and encoded names) may produce identifiers that are awkward or invalid depending on Coq parser expectations and notation settings.
3. **Mismatch between exported wrappers/axioms and intended formula shape** can cause rejection when checked in realistic Coq contexts.

> Because `coqc` could not be run here, these are risk assessments from code structure rather than compiler-confirmed failures.

---

## Suggested next verification step

When toolchain is available, run a matrix check over representative theories:

- Generate Lean: `eidos-parser --lean_using_props <theory>`
- Generate Coq: `eidos-parser --coq_using_props <theory>`
- Compile generated Lean files with `lean`
- Compile generated Coq files with `coqc`

Then append a compiler-error-index section with exact failing lines and diagnostics.
