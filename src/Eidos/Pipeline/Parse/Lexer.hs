-- | Lexical helpers for EidosLang.
--
-- We use megaparsec's character-level combinators directly — no separate
-- lexer phase.  This module provides:
--
--   * 'sc'  — space consumer (whitespace + block/line comments)
--   * 'lexeme' / 'symbol' — wrappers that consume trailing whitespace
--   * Individual token parsers (keywords, operators, punctuation)
module Eidos.Pipeline.Parse.Lexer
  ( -- * Space consumer
    sc
  , lexeme
  , symbol
    -- * Punctuation
  , lbrace, rbrace, lparen, rparen, lbrack, rbrack
  , pipe, iotaOp
  , semi, colon, comma, dot, hash, at, underscore, caret
  , colonEquals
  , lt, gt, doubleLt, doubleGt
    -- * Operators
  , arrow, bicond, impliedBy, impliesOp
  , subset, inOp, leq
  , union, inter, orOp, andOp, notOp, forallOp, existsOp
  , plus, minus, times, dotMinus
  , generSumSym, generProdSym
  , equals
    -- * Keywords
  , kwSignature, kwAxioms, kwAssertions, kwFacts
  , kwMetafacts, kwSubtheories, kwNamed, kwSort
  , kwAbbreviations
  , kwImplicit, kwReflection
  , kwSubquotient, kwSubsort, kwQuotient
  , kwMin, kwMax, kwRes, kwArg, kwDom
  , kwSet, kwIndividual, kwMereological, kwProposition
    -- * Sort constants
  , kwProp, kwBottom, kwTop, kwUniverse, kwDomain, kwPropositions
    -- * Identifiers and numbers
  , ident, argNr
  ) where

import           Data.Void              (Void)
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

-- ---------------------------------------------------------------------------
-- Space consumer
-- ---------------------------------------------------------------------------

-- | Consumes whitespace, // line comments, and /* … */ block comments.
sc :: Parser ()
sc = L.space space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

-- ---------------------------------------------------------------------------
-- Punctuation
-- ---------------------------------------------------------------------------

lbrace, rbrace, lparen, rparen :: Parser String
lbrace  = symbol "{"
rbrace  = symbol "}"
lparen  = symbol "("
rparen  = symbol ")"

-- | '[' token.
lbrack :: Parser String
lbrack = lexeme $ try $ do
  c <- char '['
  notFollowedBy (char '[')
  return [c]

-- | ']' token.
rbrack :: Parser String
rbrack = lexeme $ try $ do
  c <- char ']'
  notFollowedBy (char ']')
  return [c]

semi, colon, comma, dot, hash, at, underscore, caret :: Parser String
semi       = symbol ";"
colon      = symbol ":"
comma      = symbol ","
dot        = symbol "."
hash       = symbol "#"
at        = symbol "@"
underscore = symbol "_"
caret      = symbol "^"

-- | ':=' assignment operator for abbreviation definitions.
colonEquals :: Parser String
colonEquals = symbol ":="

lt, gt, doubleLt, doubleGt :: Parser String
doubleLt     = symbol "<<"
doubleGt     = symbol ">>"
-- '<' / '>' must not match when '<<' / '>>' follows.
lt = lexeme $ try $ char '<' <* notFollowedBy (char '<') >>= \c -> return [c]
gt = lexeme $ try $ char '>' <* notFollowedBy (char '>') >>= \c -> return [c]

-- ---------------------------------------------------------------------------
-- Operators
-- ---------------------------------------------------------------------------

arrow, bicond, impliedBy, impliesOp :: Parser String
arrow     = symbol "→"
bicond    = symbol "↔"
impliedBy = symbol "←"
impliesOp = symbol "⇒"

subset, inOp, leq :: Parser String
subset = symbol "⊆"
inOp   = symbol "∈"
leq    = symbol "≤"

union, inter, orOp, andOp, notOp, forallOp, existsOp :: Parser String
union    = symbol "∪"
inter    = symbol "∩"
orOp     = symbol "∨"
andOp    = symbol "∧"
notOp    = symbol "¬"
forallOp = symbol "∀"
existsOp = symbol "∃"

plus, minus, dotMinus :: Parser String
plus     = symbol "+"
minus    = symbol "-"
dotMinus = symbol "∸"

-- | '×' or ASCII '*' — both are mereological product.
times :: Parser String
times = symbol "×" <|> symbol "*"

equals :: Parser String
equals = symbol "="

generSumSym, generProdSym :: Parser String
generSumSym  = symbol "Σ"
generProdSym = symbol "Π"

pipe :: Parser String
pipe = symbol "|"

iotaOp :: Parser String
iotaOp = symbol "ι"

-- ---------------------------------------------------------------------------
-- Keywords (word-boundary safe)
-- ---------------------------------------------------------------------------

-- | Parse a keyword that must not be followed by an alphanumeric char or '_'.
keyword :: String -> Parser String
keyword kw = lexeme $ try $ string kw <* notFollowedBy (alphaNumChar <|> char '_')

-- | All structural keywords that must NOT be accepted as plain identifiers.
structuralKeywords :: [String]
structuralKeywords =
  [ "signature", "axioms", "assertions", "facts"
  , "metafacts", "subtheories", "named", "sort"
  , "abbreviations"
  , "implicit", "reflection"
  , "subquotient", "subsort", "quotient"
  ]

kwSignature, kwAxioms, kwAssertions, kwFacts :: Parser String
kwSignature     = keyword "signature"
kwAxioms        = keyword "axioms"
kwAssertions    = keyword "assertions"
kwFacts         = keyword "facts"

kwMetafacts, kwSubtheories, kwNamed, kwSort :: Parser String
kwMetafacts    = keyword "metafacts"
kwSubtheories  = keyword "subtheories"
kwNamed        = keyword "named"
kwSort         = keyword "sort"

kwAbbreviations :: Parser String
kwAbbreviations = keyword "abbreviations"

kwImplicit, kwReflection :: Parser String
kwImplicit   = keyword "implicit"
kwReflection = keyword "reflection"

-- | Order: subquotient before subsort (longer match first).
kwSubquotient, kwSubsort, kwQuotient :: Parser String
kwSubquotient = keyword "subquotient"
kwSubsort     = keyword "subsort"
kwQuotient    = keyword "quotient"

kwMin, kwMax, kwRes, kwArg, kwDom :: Parser String
kwMin = keyword "min"
kwMax = keyword "max"
kwRes = keyword "res"
kwArg = keyword "arg"
kwDom = keyword "dom"

kwSet, kwIndividual, kwMereological, kwProposition :: Parser String
kwSet          = keyword "set"
kwIndividual   = keyword "individual"
kwMereological = keyword "mereological"
kwProposition  = keyword "proposition"

kwProp, kwBottom, kwTop, kwUniverse, kwDomain, kwPropositions :: Parser String
kwProp         = keyword "Prop"
kwBottom       = symbol "⊥"
kwTop          = symbol "⊤"
kwUniverse     = symbol "𝕌"
kwDomain       = symbol "𝔻"
kwPropositions = symbol "ℙ"

-- ---------------------------------------------------------------------------
-- Identifiers and numbers
-- ---------------------------------------------------------------------------

-- | Plain identifier: [a-zA-Z_][a-zA-Z0-9_]*
--   Rejects structural keywords so that e.g. "sort = x" cannot parse
--   "sort" as a term-level constant.
--   Also rejects Σ and Π, which are reserved as generalized sum/product
--   operators and must be followed by a typed binder.
ident :: Parser String
ident = lexeme $ try $ do
  notFollowedBy (char 'Σ' <|> char 'Π')
  h <- letterChar <|> char '_'
  t <- many (alphaNumChar <|> char '_')
  let w = h : t
  if w `elem` structuralKeywords
    then fail $ "keyword " ++ show w ++ " cannot be used as an identifier"
    else return w

-- | Numeric literal / argument selector: [0-9]+
argNr :: Parser String
argNr = lexeme $ some digitChar