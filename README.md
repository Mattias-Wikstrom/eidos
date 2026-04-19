# EidosLang Parser — Haskell

A Haskell port of the EidosLang parser, using
[megaparsec](https://hackage.haskell.org/package/megaparsec) for parsing.

## Structure

```
src/
  Eidos/AST.hs     — AST data types (mirrors Go struct definitions)
  Eidos/Lexer.hs   — Token/lexeme helpers (whitespace, keywords, operators)
  Eidos/Parser.hs  — Full recursive-descent parser
app/
  Main.hs          — Minimal executable entry point
test/
  Spec.hs          — hspec test suite (mirrors parser_test.go)
```

## Building

With cabal:

```bash
cabal update
cabal build
cabal test
```

With stack:

```bash
stack build
stack test
```

## Usage

```haskell
import Eidos.Parser (parseString, parseFile)

-- Parse from a String
case parseString "{ signature { sort S; } }" of
  Left err  -> putStrLn (errorBundlePretty err)
  Right ast -> print ast

-- Parse from a file
result <- parseFile "mytheory.theory"
```

## Design notes

The Haskell parser mirrors the Go participle grammar exactly:

* **Lexer.hs** — megaparsec lexeme/symbol combinators replace participle's
  `lexer.MustSimple`. Keyword word-boundary safety is achieved with
  `notFollowedBy (alphaNumChar <|> char '_')`.

* **AST.hs** — One-to-one correspondence between Go structs and Haskell data
  types. `Maybe` replaces optional fields; `[…]` replaces repeated fields.

* **Parser.hs** — Disambiguation order matches the Go grammar comments:
  - Signature items: SimpleSortDecl → RelationalSort → SetDecl →
    FunctionDecl → RelationDecl → IndividualDecl
  - BaseTerm: EvaluationInTheory → ProjectionToInterval →
    ProjectionToSort → GeneralizedSumOrProduct → Singleton →
    Paren → Atomic
  - `try` is used wherever the grammar requires backtracking, matching
    participle's `MaxLookahead` semantics.

* **Operator precedence** (lowest → highest):
  biconditional ↔ → implication → → rev-implication ← →
  disjunction ∨ → conjunction ∧ → negation ¬ →
  quantifiers ∀∃ → atomic (terms)
