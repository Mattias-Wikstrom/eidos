# Eidos Grammar (BNF-style, reflecting current parser implementation)

This document describes the **current concrete syntax** accepted by the Haskell parser in `src/Eidos/Parser.hs` and token rules in `src/Eidos/Lexer.hs`.

> Notes:
> - This is intentionally "BNF-style" rather than strict classic BNF. We use `*`, `+`, and `?` for readability.
> - Comments begin with `(* ... *)`.
> - Unicode operator/keyword tokens are written literally.
> - The parser currently allows some constructs that may later be constrained by semantic/type checking.

## 1) Lexical conventions

```bnf
<ws>              ::= (space | tab | newline | <line-comment> | <block-comment>)*
<line-comment>    ::= "//" <any-char-except-newline>*
<block-comment>   ::= "/*" ... "*/"

<ident>           ::= <ident-start> <ident-rest>*
<ident-start>     ::= "A".."Z" | "a".."z" | "_"
<ident-rest>      ::= <ident-start> | "0".."9"

<argNr>           ::= "0".."9"+

(* structural keywords are reserved and cannot be parsed as <ident> in most positions: *)
(* signature axioms assertions Assertions facts metafacts subtheories named sort *)
(* implicit reflection subquotient subsort quotient *)
```

## 2) Top-level theory

```bnf
<theory>          ::= "{" <theory-body> "}"
<theory-body>     ::= <section> ("," <section>)* [","]

<section>         ::= <signature-section>
                    | <axioms-wrapper>
                    | <subtheories-section>
                    | <axioms-section>      (* bare assertions/facts/metafacts allowed at theory level *)
```

## 3) Signature section

```bnf
<signature-section> ::= "signature" "{" <signature-item>* "}"

<signature-item>    ::= <simple-sort-decl>
                      | <relational-sort-decl>
                      | <set-or-rel-decl>
                      | <function-decl>
                      | <individual-decl>

<simple-sort-decl>     ::= "sort" <ident> ";"
<relational-sort-decl> ::= <ident> ("subquotient" | "subsort" | "quotient") <sort-expr> ";"

<function-decl>    ::= <ident> ":" <sort-expr> ("," <sort-expr>)* "→" <sort-expr> ";"
<individual-decl>  ::= <ident> ":" <sort-expr> ";"
<set-or-rel-decl>  ::= <ident> "⊆" <sort-expr> ("," <sort-expr>)* ";"
```

## 4) Sort expressions

```bnf
<sort-expr>        ::= <sort-ref>
<sort-ref>         ::= <theory-ref>* <sort-constant>
<theory-ref>       ::= <ident> "."

<sort-constant>    ::= "𝕌" | "ℙ" | "𝔻" | "Prop"
                     | "min" | "max" | "res" | "arg" | "dom"
                     | "set" | "individual" | "mereological" | "proposition"
                     | <ident>
```

## 5) Axioms/assertions/facts/metafacts

```bnf
<axioms-wrapper>   ::= "axioms" "{" <axioms-section> ("," <axioms-section>)* [","] "}"
<axioms-section>   ::= <assertions-section> | <facts-section> | <metafacts-section>

<assertions-section> ::= ("assertions" | "Assertions") "{" (<prop-expr-incl-vars> ";")* "}"
<facts-section>      ::= "facts"      "{" (<prop-expr-incl-vars> ";")* "}"
<metafacts-section>  ::= "metafacts"  "{" (<prop-expr-incl-vars> ";")* "}"

<prop-expr-incl-vars> ::= <var-decl-bracketed>* <prop-expr>
<var-decl-bracketed>  ::= "[" <var-decl> "]"
<var-decl>            ::= <ident> (":" | "⊆") <sort-expr>
```

## 6) Subtheories

```bnf
<subtheories-section> ::= "subtheories" "{" <subtheory-entry> ("," <subtheory-entry>)* [","] "}"

<subtheory-entry>     ::= <subtheory-group>
                        | <subtheory-item>   (* currently parsed then rejected unless grouped *)

<subtheory-group>     ::= <group-keyword> "{" <subtheory-item> ("," <subtheory-item>)* [","] "}"
<group-keyword>       ::= "implicit" | "named" | "reflection"

<subtheory-item>      ::= <subtheory-alias> ":" <subtheory-def>
<subtheory-alias>     ::= <ident-like-including-structural-keywords>

<subtheory-def>       ::= "{" <theory-body> "}"
                        | "@" <dotted-ident>

<dotted-ident>        ::= <ident> ("." <ident>)*
```

(* Implementation note: duplicate group keywords and duplicate aliases are rejected during parsing. *)

(* Legacy bracket qualifiers like `[implicit] name: ...` are explicitly rejected. *)

## 7) Proposition expressions (precedence and associativity)

Lowest precedence at top, highest at bottom.

```bnf
<prop-expr>        ::= <right-impl> ("↔" <right-impl>)*
                      (* left-associative *)

<right-impl>       ::= <left-impl> ["→" <right-impl>]
                      (* right-associative *)

<left-impl>        ::= <disj> ("←" <disj>)*
                      (* left-associative *)

<disj>             ::= <conj> ("∨" <conj>)*
<conj>             ::= <neg> ("∧" <neg>)*

<neg>              ::= "¬" <neg> | <quantified>

<quantified>       ::= <quantifier>* <atomic-prop>
<quantifier>       ::= "∀" <var-decl> | "∃" <var-decl>

<atomic-prop>      ::= <term-pair>
<term-pair>        ::= <term> <relation-followed-by-term>*

<relation-followed-by-term>
                   ::= <theory-ref>* <relation-op> [<optional-sort-expr>] <term>

<relation-op>      ::= "=" | "≤" | "⊆" | "∈"
<optional-sort-expr> ::= ("_" | "^") <sort-expr>
                      (* parser currently accepts this after any relation-op,
                         though it is mainly intended for equality, e.g. =_S / =^S *)
```

## 8) Terms

```bnf
<term>             ::= <factor> <operation-followed-by-factor>*
<operation-followed-by-factor>
                   ::= <theory-ref>* <term-binop> <factor>

<term-binop>       ::= "∸" | "⇒" | "∪" | "∩" | "+" | "×" | "*" | "-"

<factor>           ::= <base-term> <term-suffix>*

<base-term>        ::= <evaluation-in-theory>
                     | <projection-to-interval>
                     | <projection-to-sort>
                     | <generalized-sum-or-product>
                     | "{" <term> "}"          (* singleton-like term form *)
                     | "(" <prop-expr> ")"
                     | <constant-ref>

<evaluation-in-theory>
                   ::= "<<" <theory-name> ("." <theory-name>)* ">>" "(" <prop-expr> ")"
<theory-name>      ::= <ident>

<projection-to-sort>
                   ::= "<" <sort-expr> ">" "(" <term> ")"
<projection-to-interval>
                   ::= "<" <term> "," <term> ">" "(" <term> ")"

<generalized-sum-or-product>
                   ::= ("Σ" | "Π") (<typed-var-decl> | <ident>) "(" <term> ")"
<typed-var-decl>   ::= <ident> (":" | "⊆") <sort-expr>

<constant-ref>     ::= <theory-ref>* <const-ref-token>
<const-ref-token>  ::= "⊥" | "⊤"
                     | "min" | "max" | "res" | "arg" | "dom"
                     | "set" | "individual" | "mereological" | "proposition"
                     | <argNr>
                     | <ident>
```

## 9) Term suffixes

```bnf
<term-suffix>      ::= "." <dot-attr-keyword>
                     | <call-suffix>
                     | "#" <hash-attr-keyword>

<dot-attr-keyword> ::= "min" | "max"

<hash-attr-keyword> ::= "min" | "max" | "res" | "arg" | "dom"
                      | "set" | "individual" | "mereological" | "proposition"
                      | <argNr>

<call-suffix>      ::= "(" [<term> ("," <term>)*] ")"
```

## 10) Known parser-level constraints and likely-evolving areas

- `subtheories` currently **requires explicit names** for all items and requires items to occur inside `named { ... }`, `implicit { ... }`, or `reflection { ... }` blocks.
- Duplicate aliases and duplicate group keywords in one `subtheories` section are rejected by the parser.
- `assertions` and `Assertions` are both accepted.
- Optional sort qualifiers (`_S`, `^S`) are parsed after any relation operator, not only `=`.
- In generalized sums/products, a bare variable form and typed variable form are both accepted (`Σx(...)` and `Σx:S(...)` / `Σx⊆S(...)`).
