Three places:

extractEqualityEntities (TypeCheck.hs) — 8 levels deep, extraction only, returns Nothing for everything except term = term.

extractMergeAxioms (MkAxiomSets.hs) — same 8-level descent, returns [] for everything except a very specific merge fact shape.

qualifyPropExprConstants (FromSyntax.hs) — 12 levels, but it's a full traversal (every node is rebuilt), not an extraction. More justified by its nature, just verbose.

The two extraction functions (extractEqualityEntities and extractMergeAxioms) descend through exactly the same constructor chain and could in principle share a traversal combinator, but that would be a significant refactor for uncertain benefit.

------
Summary of Deep Manual AST Destructuring in Eidos Haskell Source
Based on a thorough search of the Haskell source code in /home/mattias/eidos/.claude/worktrees/friendly-blackwell-8144e0/src/, I found three major functions that perform deep manual AST destructuring with chains of local where helpers, each unwrapping one IR/AST constructor level.

1. extractEqualityEntities (TypeCheck.hs)
File: /home/mattias/eidos/.claude/worktrees/friendly-blackwell-8144e0/src/Eidos/Pipeline/FromSyntax/Check/TypeCheck.hs (lines 127–160)

Depth: 8 nested helpers
Pattern: ResolvedPropBicond → ResolvedRightImpl → ResolvedLeftImpl → ResolvedDisj → ResolvedConj → ResolvedNeg → ResolvedQuantified → ResolvedAtomicProp → ResolvedTermPair

Local helpers:

go :: ResolvedRightImpl → Maybe (Entity, Entity)
goLeft :: ResolvedLeftImpl → Maybe (Entity, Entity)
goDisj :: ResolvedDisj → Maybe (Entity, Entity)
goConj :: ResolvedConj → Maybe (Entity, Entity)
goNeg :: ResolvedNeg → Maybe (Entity, Entity)
goQuant :: ResolvedQuantified → Maybe (Entity, Entity)
goAtomic :: ResolvedAtomicProp → Maybe (Entity, Entity)
goTP :: ResolvedTermPair → Maybe (Entity, Entity)
Purpose: Extracts left and right entities from a simple equality fact (term = term). Returns Nothing for all non-equality patterns.

2. extractMergeAxioms (MkAxiomSets.hs)
File: /home/mattias/eidos/.claude/worktrees/friendly-blackwell-8144e0/src/Eidos/Pipeline/IRProcessing/MkAxiomSets.hs (lines 608–652)

Depth: 8 nested helpers
Pattern: ResolvedPropBicond → ResolvedRightImpl → ResolvedLeftImpl → ResolvedDisj → ResolvedConj → ResolvedNeg → ResolvedQuantified → ResolvedAtomicProp → ResolvedTermPair

Local helpers:

extractMergeAxioms :: IR.ResolvedPropExpr → [AxiomSet]
extractFromRightImpl :: IR.ResolvedRightImpl → [AxiomSet] (requires no rightImpl alternative)
extractFromLeftImpl :: IR.ResolvedLeftImpl → [AxiomSet] (requires empty rests)
extractFromDisj :: IR.ResolvedDisj → [AxiomSet] (requires empty rests)
extractFromConj :: IR.ResolvedConj → [AxiomSet] (requires empty rests)
extractFromNeg :: IR.ResolvedNeg → [AxiomSet] (requires NegChild, not NegNot)
extractFromQuantified :: IR.ResolvedQuantified → [AxiomSet] (requires no quantifiers)
extractFromAtomic :: IR.ResolvedAtomicProp → [AxiomSet] (requires TermPair, not Constant)
extractFromTermPair :: IR.ResolvedTermPair → [AxiomSet] (finally extracts names and emits merge axiom)
getTermName :: IR.ResolvedTerm → Maybe String (helper to extract simple constant names)
Purpose: Extracts implicit merge facts by drilling down to a specific pattern: a bicond with no rest, no right alternative, no quantifiers, no negations—only a simple term pair with "=" operator. Returns [] for everything else.

3. qualifyPropExprConstants (FromSyntax.hs)
File: /home/mattias/eidos/.claude/worktrees/friendly-blackwell-8144e0/src/Eidos/Pipeline/FromSyntax/FromSyntax.hs (lines 2664–2706)

Depth: 12 nested helpers
Pattern: ResolvedPropBicond → ResolvedRightImpl → ResolvedLeftImpl → ResolvedDisj → ResolvedConj → ResolvedNeg → ResolvedQuantified → ResolvedAtomicProp → ResolvedTermPair → ResolvedTerm → ResolvedFactor → ResolvedBaseTerm

Local helpers:

goPropRest :: ResolvedPropRest → ResolvedPropRest
goRightImpl :: ResolvedRightImpl → ResolvedRightImpl
goLeftImpl :: ResolvedLeftImpl → ResolvedLeftImpl
goDisj :: ResolvedDisj → ResolvedDisj
goConj :: ResolvedConj → ResolvedConj
goNeg :: ResolvedNeg → ResolvedNeg (handles NegNot recursively and NegChild)
goQuantified :: ResolvedQuantified → ResolvedQuantified
goAtomic :: ResolvedAtomicProp → ResolvedAtomicProp (branches on TermPair vs Constant)
goTermPair :: ResolvedTermPair → ResolvedTermPair
goRFT :: ResolvedRelationFollowedByTerm → ResolvedRelationFollowedByTerm
goTerm :: ResolvedTerm → ResolvedTerm
goOFF :: ResolvedOperationFollowedByFactor → ResolvedOperationFollowedByFactor
goFactor :: ResolvedFactor → ResolvedFactor
goBase :: ResolvedBaseTerm → ResolvedBaseTerm (handles 8 different base-term patterns)
qualifyConst :: ResolvedConstantRef → ResolvedConstantRef
Purpose: Rewrites all constant references in a resolved proposition expression to use fully-qualified entity names (for <<theory>>() constructs). Unlike the extraction functions above, this is a traversal that processes every node in the tree and rebuilds the structure.

Characteristics Summary
Function	File	Depth	Type	Success Condition
extractEqualityEntities	TypeCheck.hs	8	Extraction	Only simple equality (term = term)
extractMergeAxioms	MkAxiomSets.hs	8	Extraction	Very specific merge fact pattern
qualifyPropExprConstants	FromSyntax.hs	12	Traversal/Transformation	None (processes all patterns)
All three functions operate on the ResolvedProp AST hierarchy* and demonstrate the challenge of working with deeply-nested tagged-union types where the specific pattern of interest lies 8–12 constructor levels deep. The extraction functions are brittle (return empty/Nothing for non-matching patterns), while the transformation is robust but verbose.