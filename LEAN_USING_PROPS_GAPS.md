# Gaps in `--lean_using_props` Translation vs Current Grammar

This note tracks parser-supported concrete syntax that is currently not translated faithfully by the `--lean_using_props` exporter (`Eidos.Export.MkAxiomSets`).

## Confirmed translation gaps

1. **User `facts { ... }` are not exported as user axioms.**
   The exporter only collects `assertions` and `metafacts` for user-authored fact export, and omits `FactKindFact` from `userFactAxiomSets`.

2. **Biconditional chains are truncated.**
   `A ↔ B ↔ C` parses, but translation keeps only the first rest (`A ↔ B`) and ignores remaining links.

3. **Relation sort qualifiers are ignored.**
   Grammar allows relation qualifiers like `=_S` / `=^S` (and parser accepts qualifiers after all relation ops), but translator does not consult qualifier info in relation-to-Lean mapping.

4. **`<<theory.path>>(...)` evaluation ignores theory path.**
   Export currently translates only the operand proposition and drops the explicit theory reference.

5. **Generalized `Σ` / `Π` drops both operator and binder.**
   Export currently translates only the operand term, ignoring whether it was sum/product and ignoring typed/bare binder.

6. **Singleton term `{t}` is flattened to `t`.**
   Parser keeps a distinct singleton base-term form, but Lean export erases that distinction.

7. **Set-membership/subset/equality semantics are flattened to implication/biconditional patterns.**
   This may be intentional in the propositional encoding, but it means syntax-level distinctions (`=`, `⊆`, `∈`, etc.) are not preserved as distinct Lean primitives.

## Parser features that are currently reflected (at least syntactically)

- Left implication (`←`) is translated (via folding into implication form).
- Disjunction/conjunction/negation/quantifiers are translated.
- Term operations (`+`, `×`, `-`, `∸`, `∪`, `∩`, `⇒`) are mapped.
- Projection-to-sort and projection-to-interval both map to `LProjectIntoInterval`.
- Call suffixes and hash attributes are translated into applications/named vars.

## Practical “what is left?” summary

If the goal is grammar-faithful export for `--lean_using_props`, the biggest remaining items are:

- add user `facts` export,
- handle full biconditional chains,
- preserve/use relation sort qualifiers,
- preserve theory-qualified evaluation,
- preserve generalized `Σ`/`Π` structure,
- preserve singleton constructor semantics.
