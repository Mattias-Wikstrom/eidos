# Eidos Pipeline Layout

This folder contains the full compiler pipeline, organized by stage:

1. `Parse/`: lexer/parser + source AST.
2. `Resolution/`: external reference resolution and build monad.
3. `FromSyntax/`: source-to-IR lowering (`FromSyntax.hs`), IR types (`IR.hs`), and `Check/`.
4. `IRProcessing/`: target-neutral IR passes and axiom set construction.
5. `Targets/`: target-specific emitters (Lean, LeanProps, CoqProps).

`InvokePipeline.hs` contains target-neutral pipeline preparation helpers used by entrypoints.
