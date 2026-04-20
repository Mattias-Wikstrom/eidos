-- | EidosLang parser implemented with megaparsec.
--
-- The grammar matches the Go participle grammar in parser.go exactly.
-- Section order and precedence levels are preserved.
--
-- Parsing entry points:
--
--   * 'parseString'  — parse from a 'String'
--   * 'parseFile'    — read a file and parse it
--   * 'theoryParser' — the raw megaparsec 'Parser TheoryDecl'
module Eidos.Parser
  ( -- * Entry points
    parseString
  , parseFile
    -- * Low-level
  , theoryParser
  , Parser
  ) where

import           Control.Monad          (void, unless)
import           Data.Void              (Void)
import           Text.Megaparsec
import           Text.Megaparsec.Char
import Data.List (sort, group, intercalate)
import Data.Maybe (mapMaybe)

import           Eidos.AST
import           Eidos.Lexer

type Parser = Parsec Void String

-- | Find duplicate elements in a list (returns each element that appears more than once)
findDuplicates :: Ord a => [a] -> [a]
findDuplicates = map head . filter (\l -> length l > 1) . group . sort

-- ---------------------------------------------------------------------------
-- Entry points
-- ---------------------------------------------------------------------------

-- | Parse EidosLang source text.
parseString :: String -> Either (ParseErrorBundle String Void) TheoryDecl
parseString = runParser (sc *> theoryParser <* eof) ""

-- | Read and parse an EidosLang theory file.
parseFile :: FilePath -> IO (Either (ParseErrorBundle String Void) TheoryDecl)
parseFile path = do
  src <- readFile path
  return $ runParser (sc *> theoryParser <* eof) path src

-- ---------------------------------------------------------------------------
-- Top-level
-- ---------------------------------------------------------------------------

-- | Parse a full theory declaration: { … }
theoryParser :: Parser TheoryDecl
theoryParser = TheoryDecl <$> between lbrace rbrace pTheoryBody

pTheoryBody :: Parser TheoryBody
pTheoryBody = TheoryBody <$> many (pSection <* optional comma)

pSection :: Parser Section
pSection =
      SectionSignature   <$> pSignatureSection
  <|> SectionAxioms      <$> pAxiomsWrapper
  <|> SectionSubtheories <$> pSubtheoriesSection
  <|> SectionBareAxioms  <$> pAxiomsSection

-- ---------------------------------------------------------------------------
-- Signature
-- ---------------------------------------------------------------------------

pSignatureSection :: Parser SignatureSection
pSignatureSection =
  SignatureSection <$> (kwSignature *> between lbrace rbrace (many pSignatureItem))

-- | Disambiguation order mirrors the Go grammar comment:
--   1. SimpleSortDecl      starts with 'sort'
--   2. RelationalSortDecl  Ident then subsort/quotient/subquotient
--   3. SetDecl             Ident then '⊆'
--   4. FunctionDecl / RelationDecl / IndividualDecl  all start 'Ident :'
--      — differentiated by presence of '→' and number of domain sorts.
pSignatureItem :: Parser SignatureItem
pSignatureItem =
      SigSimpleSort     <$> try pSimpleSortDecl
  <|> SigRelationalSort <$> try pRelationalSortDecl
  <|> SigSet            <$> try pSetDecl
  <|> SigFunction       <$> try pFunctionDecl
  <|> SigRelation       <$> try pRelationDecl
  <|> SigIndividual     <$> pIndividualDecl

pSimpleSortDecl :: Parser SimpleSortDeclaration
pSimpleSortDecl = SimpleSortDeclaration <$> (kwSort *> ident <* semi)

pRelationalSortDecl :: Parser RelationalSortDeclaration
pRelationalSortDecl = do
  n   <- ident
  rel <- try kwSubquotient <|> try kwSubsort <|> kwQuotient
  s   <- pSortExpr
  void semi
  return $ RelationalSortDeclaration n rel s

-- | f : S, T → U ;
pFunctionDecl :: Parser FunctionDeclaration
pFunctionDecl = do
  n  <- ident
  void colon
  ds <- pSortExpr `sepBy1` comma
  void arrow
  cd <- pSortExpr
  void semi
  return $ FunctionDeclaration n ds cd

-- | r : S, T ;  (≥2 sorts, no arrow)
pRelationDecl :: Parser RelationDeclaration
pRelationDecl = do
  n    <- ident
  void colon
  s1   <- pSortExpr
  void comma
  rest <- pSortExpr `sepBy1` comma
  void semi
  return $ RelationDeclaration n s1 rest

-- | x : S ;
pIndividualDecl :: Parser IndividualDeclaration
pIndividualDecl = do
  n <- ident
  void colon
  s <- pSortExpr
  void semi
  return $ IndividualDeclaration n s

-- | mySet ⊆ S ;  /  r ⊆ S, T, U ;
pSetDecl :: Parser SetDeclaration
pSetDecl = do
  n  <- ident
  void subset
  ds <- pSortExpr `sepBy1` comma
  void semi
  return $ SetDeclaration n ds

-- ---------------------------------------------------------------------------
-- Sort expressions
-- ---------------------------------------------------------------------------

pSortExpr :: Parser SortExpr
pSortExpr = SortExpr <$> pSortRef

pSortRef :: Parser SortRef
pSortRef = do
  -- Greedily collect "Ident." prefixes; stop when no dot follows.
  specs <- many (try pTheoryRef)
  c     <- pSortConstant
  return $ SortRef specs c

-- | One dot-qualified path segment: "name."
pTheoryRef :: Parser TheoryRef
pTheoryRef = TheoryRef <$> (ident <* dot)

-- | A sort constant: identifier or built-in sort symbol or attribute keyword.
pSortConstant :: Parser String
pSortConstant =
      try kwUniverse
  <|> try kwPropositions
  <|> try kwDomain
  <|> try kwProp
  <|> try kwMin
  <|> try kwMax
  <|> try kwRes
  <|> try kwArg
  <|> try kwDom
  <|> try kwSet
  <|> try kwIndividual
  <|> try kwMereological
  <|> try kwProposition
  <|> ident

-- ---------------------------------------------------------------------------
-- Axioms
-- ---------------------------------------------------------------------------

pAxiomsWrapper :: Parser AxiomsWrapper
pAxiomsWrapper =
  AxiomsWrapper <$> (kwAxioms *> between lbrace rbrace (many (pAxiomsSection <* optional comma)))

pAxiomsSection :: Parser AxiomsSection
pAxiomsSection =
      AxAssertions <$> pAssertionsSection
  <|> AxFacts      <$> pFactsSection
  <|> AxMetafacts  <$> pMetafactsSection

pAssertionsSection :: Parser AssertionsSection
pAssertionsSection =
  AssertionsSection <$>
    ((try kwAssertions <|> kwAssertionsCap) *>
      between lbrace rbrace (many (pPropExprInclVars <* semi)))

pFactsSection :: Parser FactsSection
pFactsSection =
  FactsSection <$>
    (kwFacts *> between lbrace rbrace (many (pPropExprInclVars <* semi)))

pMetafactsSection :: Parser MetafactsSection
pMetafactsSection =
  MetafactsSection <$>
    (kwMetafacts *> between lbrace rbrace (many (pPropExprInclVars <* semi)))

-- ---------------------------------------------------------------------------
-- Subtheories
-- ---------------------------------------------------------------------------

pSubtheoriesSection :: Parser SubtheoriesSection
pSubtheoriesSection = do
  void kwSubtheories
  entries <- between lbrace rbrace (many (pSubtheoryEntry <* optional comma))
  -- Check for duplicate group keywords
  let groupKws = mapMaybe getGroupKeyword entries
      dupGroups = findDuplicates groupKws
  unless (null dupGroups) $
    fail $ "Duplicate subtheory group keyword(s): " ++ intercalate ", " dupGroups
  -- Check for duplicate aliases across all entries (including inside groups)
  let aliases = collectAliases entries
      dupAliases = findDuplicates aliases
  unless (null dupAliases) $
    fail $ "Duplicate subtheory alias(es): " ++ intercalate ", " dupAliases
  return $ SubtheoriesSection entries
  where
    getGroupKeyword (SubtheoryEntryGroup (SubtheoryGroup kw _)) = Just kw
    getGroupKeyword _ = Nothing

    collectAliases :: [SubtheoryEntry] -> [String]
    collectAliases = concatMap go
      where
        go (SubtheoryEntryItem (SubtheoryItem _ (Just n) _)) = [n]
        go (SubtheoryEntryItem _) = []
        go (SubtheoryEntryGroup (SubtheoryGroup _ items)) = 
          mapMaybe (\(SubtheoryItem _ n _) -> n) items

collectAliases :: [SubtheoryEntry] -> [String]
collectAliases = concatMap go
  where
    go (SubtheoryEntryItem (SubtheoryItem _ (Just n) _)) = [n]
    go (SubtheoryEntryItem _) = []
    go (SubtheoryEntryGroup (SubtheoryGroup _ items)) = 
      mapMaybe (\(SubtheoryItem _ n _) -> n) items

pSubtheoryEntry :: Parser SubtheoryEntry
pSubtheoryEntry =
      SubtheoryEntryGroup <$> try pSubtheoryGroup
  <|> SubtheoryEntryItem  <$> pSubtheoryItem

pSubtheoryGroup :: Parser SubtheoryGroup
pSubtheoryGroup = do
  kw    <- pGroupKeyword
  items <- between lbrace rbrace (many pSubtheoryItem)
  return $ SubtheoryGroup kw items

pGroupKeyword :: Parser String
pGroupKeyword = try kwImplicit <|> try kwNamed <|> kwReflection

pSubtheoryItem :: Parser SubtheoryItem
pSubtheoryItem = do
  qual <- optional (void lbrack *> pGroupKeyword <* void rbrack)
  name <- optional (try (ident <* colon))
  def  <- pSubtheoryDef
  return $ SubtheoryItem qual name def

dottedIdent :: Parser String
dottedIdent = do
  first <- ident
  rest  <- many (try ((:) <$> char '.' <*> ident))
  return (concat (first : rest))

pSubtheoryDef :: Parser SubtheoryDef
pSubtheoryDef =
      SubtheoryBody        <$> between lbrace rbrace pTheoryBody
  <|> SubtheoryExternalRef <$> (doubleLbrack *> dottedIdent <* doubleRbrack)
  <|> SubtheoryExternalRef <$> (at *> dottedIdent)

-- ---------------------------------------------------------------------------
-- Propositions
-- ---------------------------------------------------------------------------

pPropExprInclVars :: Parser PropExprInclVars
pPropExprInclVars = do
  vars <- many (void lbrack *> pVarDecl <* void rbrack)
  expr <- pPropExpr
  return $ PropExprInclVars vars expr

pVarDecl :: Parser VarDecl
pVarDecl = do
  i  <- ident
  op <- symbol ":" <|> subset
  s  <- pSortExpr
  return $ VarDecl i op s

-- | PropExpr: biconditional ↔, left-associative (lowest precedence).
pPropExpr :: Parser PropExpr
pPropExpr = do
  l  <- pRightImpl
  rs <- many pPropExprRest
  return $ PropExpr l rs

pPropExprRest :: Parser PropExprRest
pPropExprRest = do
  op <- bicond
  r  <- pRightImpl
  return $ PropExprRest op r

-- | RightImpl: implication →, RIGHT-associative.
pRightImpl :: Parser RightImpl
pRightImpl = do
  l <- pLeftImpl
  r <- optional $ do
    op <- arrow
    ri <- pRightImpl
    return (op, ri)
  return $ RightImpl l r

-- | LeftImpl: reverse implication ←, left-associative.
pLeftImpl :: Parser LeftImpl
pLeftImpl = do
  l  <- pDisj
  rs <- many pLeftImplRest
  return $ LeftImpl l rs

pLeftImplRest :: Parser LeftImplRest
pLeftImplRest = do
  op <- impliedBy
  r  <- pDisj
  return $ LeftImplRest op r

pDisj :: Parser Disj
pDisj = do
  l  <- pConj
  rs <- many pDisjRest
  return $ Disj l rs

pDisjRest :: Parser DisjRest
pDisjRest = do
  op <- orOp
  r  <- pConj
  return $ DisjRest op r

pConj :: Parser Conj
pConj = do
  l  <- pNeg
  rs <- many pConjRest
  return $ Conj l rs

pConjRest :: Parser ConjRest
pConjRest = do
  op <- andOp
  r  <- pNeg
  return $ ConjRest op r

pNeg :: Parser Neg
pNeg =
      NegNot   <$> (notOp *> pNeg)
  <|> NegChild <$> pQuantified

pQuantified :: Parser Quantified
pQuantified = do
  qs <- many pQuantifier
  a  <- pAtomicProp
  return $ Quantified qs a

pQuantifier :: Parser Quantifier
pQuantifier =
      QForall <$> (forallOp *> pVarDecl)
  <|> QExists <$> (existsOp *> pVarDecl)

pAtomicProp :: Parser AtomicProp
pAtomicProp = AtomicProp <$> pTermPair

pTermPair :: Parser TermPair
pTermPair = do
  l  <- pTerm
  rs <- many pRelationFollowedByTerm
  return $ TermPair l rs

-- | A relational operator possibly preceded by theory-path specifiers.
--   Handles: "=", "≤", "⊆", "∈".
--   Also handles optional sort annotation "_S" or "^S" after "=".
pRelationFollowedByTerm :: Parser RelationFollowedByTerm
pRelationFollowedByTerm = do
  specs      <- many (try pTheoryRef)
  op         <- try equals <|> try leq <|> try subset <|> inOp
  mbSortQual <- optional (try pOptionalSortExpr)
  r          <- pTerm
  return $ RelationFollowedByTerm specs op mbSortQual r

pOptionalSortExpr :: Parser OptionalSortExpr
pOptionalSortExpr = do
  ind <- underscore <|> caret
  s   <- pSortExpr
  return $ OptionalSortExpr ind s

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

pTerm :: Parser Term
pTerm = do
  l  <- pFactor
  rs <- many pOperationFollowedByFactor
  return $ Term l rs

pOperationFollowedByFactor :: Parser OperationFollowedByFactor
pOperationFollowedByFactor = do
  specs <- many (try pTheoryRef)
  op    <- pTermBinOp
  r     <- pFactor
  return $ OperationFollowedByFactor specs op r

-- | Binary term operators (mereological + set).
pTermBinOp :: Parser String
pTermBinOp =
      try dotMinus
  <|> try impliesOp
  <|> try union
  <|> try inter
  <|> try plus
  <|> try times
  <|> minus

pFactor :: Parser Factor
pFactor = do
  b  <- pBaseTerm
  ss <- many pTermSuffix
  return $ Factor b ss

-- | baseTerm alternatives ordered by disambiguation (see Go grammar comments).
pBaseTerm :: Parser BaseTerm
pBaseTerm =
      BTEvaluationInTheory      <$> try pEvaluationInTheory
  <|> BTProjectionToInterval    <$> try pProjectionToInterval
  <|> BTProjectionToSort        <$> try pProjectionToSort
  <|> BTGeneralizedSumOrProduct <$> try pGeneralizedSumOrProduct
  <|> BTSingleton               <$> try (between lbrace rbrace pTerm)
  <|> BTParen                   <$> try (between lparen rparen pPropExpr)
  <|> BTAtomic                  <$> pConstantRef

-- | <<th1.th2>>(expr)
pEvaluationInTheory :: Parser EvaluationInTheory
pEvaluationInTheory = do
  void doubleLt
  n   <- pTheoryName
  ns  <- many (dot *> pTheoryName)
  void doubleGt
  op  <- between lparen rparen pPropExpr
  return $ EvaluationInTheory (n:ns) op

pTheoryName :: Parser TheoryName
pTheoryName = TheoryName <$> ident

-- | <S>(x) — sort projection.
pProjectionToSort :: Parser ProjectionToSort
pProjectionToSort = do
  void lt
  s <- pSortExpr
  void gt
  op <- between lparen rparen pTerm
  return $ ProjectionToSort s op

-- | <lo, hi>(x) — interval projection.
--   A comma after the first term distinguishes this from projectionToSort.
pProjectionToInterval :: Parser ProjectionToInterval
pProjectionToInterval = do
  void lt
  lo <- pTerm
  void comma
  hi <- pTerm
  void gt
  op <- between lparen rparen pTerm
  return $ ProjectionToInterval lo hi op

-- | Σ or Π followed by a bound variable, then a parenthesised body.
--
-- Valid forms:
--   Sy(body)       -- bare identifier (must not be immediately followed by '(')
--   Sz : D (body)  -- typed VarDecl
--
-- S(body) with no bound variable is rejected: bareId requires the next
-- char not be '(' so that S(x) fails cleanly.
pGeneralizedSumOrProduct :: Parser GeneralizedSumOrProduct
pGeneralizedSumOrProduct = do
  sym <- try generSumSym <|> generProdSym
  v   <- (Left <$> try pTypedVarDecl) <|> (Right <$> bareId)
  op  <- between lparen rparen pTerm
  return $ GeneralizedSumOrProduct sym v op
  where
    bareId = ident

-- | VarDecl without the surrounding brackets — used inside Σ/Π.
pTypedVarDecl :: Parser VarDecl
pTypedVarDecl = do
  i  <- ident
  op <- symbol ":" <|> subset
  s  <- pSortExpr
  return $ VarDecl i op s

-- | A possibly dot-qualified constant reference (ident, ⊥, ⊤, number,
--   or attribute keyword).
pConstantRef :: Parser ConstantRef
pConstantRef = do
  specs <- many (try pTheoryRef)
  ref   <- pConstRefToken
  return $ ConstantRef specs ref

-- | Tokens that can appear as a term-level constant.
--   Structural keywords (sort, implicit, …) are deliberately excluded.
pConstRefToken :: Parser String
pConstRefToken =
      try kwBottom
  <|> try kwTop
  <|> try kwMin
  <|> try kwMax
  <|> try kwRes
  <|> try kwArg
  <|> try kwDom
  <|> try kwSet
  <|> try kwIndividual
  <|> try kwMereological
  <|> try kwProposition
  <|> try argNr
  <|> ident

-- ---------------------------------------------------------------------------
-- Term suffixes
-- ---------------------------------------------------------------------------

pTermSuffix :: Parser TermSuffix
pTermSuffix =
      SuffixDotAttr   <$> try (dot *> pDotAttrKeyword)
  <|> SuffixCall      <$> try pCallSuffix
  <|> SuffixSpecialOp <$> (hash *> pHashAttrKeyword)

pDotAttrKeyword :: Parser String
pDotAttrKeyword =
      try kwMin <|> try kwMax <|> try kwRes <|> try kwArg <|> kwDom

pHashAttrKeyword :: Parser String
pHashAttrKeyword =
      try kwMin <|> try kwMax <|> try kwRes <|> try kwArg
  <|> try kwDom <|> try kwSet <|> try kwIndividual
  <|> try kwMereological <|> try kwProposition
  <|> argNr

pCallSuffix :: Parser CallSuffix
pCallSuffix =
  CallSuffix <$>
    between lparen rparen (pTerm `sepBy` comma)
