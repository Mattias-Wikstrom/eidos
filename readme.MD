# EidosLang: A Language for Expressing Mathematical Theories

## What Is Eidos?
This document describes a language called *EidosLang* that can be used to express mathematical theories of all kinds. The language is best understood on its own terms but encompasses all of the following logics in very natural ways:
* Propositional logic (including quantified propositional logic),
* equational logic,
* first-order logic,
* second-order logic,
* classical logic,
* intuitionistic logic,
* many-sorted logic, and
* single-sorted logic.

One may even argue that the language is adequate as a means for expressing *any* mathematical theory in a natural manner.

Eidos is based on the discovery that Quantified Intuitionistic Propositional Logic (QIPL) has the same expressive power as first-order logic (i.e., it is Turing-complete) while at the same time being incredibly simple. One may think of Eidos as syntactic sugar on top of QIPL.

Unlike many languages for expressing mathematical theories, Eidos is not based on type theory. The idea behind the language is instead to provide ‘syntactic sugar’ on top of quantified intuitionistic propositional logic (QIPL). QIPL has been known for a long time to be Turing-complete, but it may appear very counterintuitive and hard to work with at first.

We find QIPL to be very intuitive and easy to work with once it is understood, but it does help to have some syntactic sugar on top of the core that is provided by QIPL. Hence Eidos.

### What Eidos Is *Not*
Unlike, for example, Coq or Lean, Eidos does not come with a way to express mathematical proofs and to check their correctness. The sole goal in Eidos is to be able to refer to mathematical objects of all sorts in a very simple and natural way.

We hope to be able to provide good support for exporting theories written in Eidos to Lean and Coq. The same theory will be exportable in more than one way depending on which Lean/Coq features one wishes to take advantage of. (Update: The implementation of these things is now well under way.)

Due to the richness of languages such as Coq and Lean, going in the opposite direction seems less practical.

### Where Does the Name Come from?
The Greek word εἶδος (‘form’/‘shape’/‘appearance’) comes from Plato, who used it when speaking of the abstract ‘ideas’/‘forms’ that are studied in mathematics. For example, one may study the idea/form of a circle, the idea/form of a square, the idea/form of a triangle, and so on. There is also a connotation with the philosophy of Husserl, who used the adjective ‘eidetic.’

### The Structure of This Document
This document describes the basic ideas behind Eidos before transitioning into a practical tour of the language. You may want to skip between the more theoretical parts (which help you understand what Eidos is all about) and the more practical parts (which tell you how to use Eidos).

## The Theoretical Underpinings of Eidos
The following subsections describe the theory that Eidos is based on.

This section contains advanced material and may be skipped.

### Quantified Intuitionistic Propositional Logic (QIPL)
Intuitionistic logic may be described as classical logic minus the Law of Excluded Middle (LEM). LEM tells one that only two possibilities exist for each proposition: A proposition is either true or false. Intuitionistic logic allows, instead, for a spectrum of possibilities between the inevitably true and the inevitably false.

Propositional logic is logic where the only objects one deals with are propositions. Propositions may involve the following propositional connectives:
1. Conjunction. The conjunction P ^ Q of two propositions P and Q says that P and Q both hold. P ^ Q is the weakest proposition that implies P as well as Q.
2. Disjunction.  The disjunction P v Q of two propositions P and Q says that either P or Q holds. P v Q is the strongest proposition that is implied by P as well as Q.
3. Implication. The implication P -> Q says that if P holds then so does Q. Expressed differently, P -> Q says that says that P implies Q. P -> Q is the weakest proposition R such that P ^ R implies Q.
4. Biimplication. The biimplication P <-> Q says that P holds if and only if Q holds. In Eidos this means that P and Q are one and the same proposition, and one may accordingly write P = Q instead of P <-> Q.
5. Truth. The proposition T is implied by every proposition. In other words, it is the weakest proposition.
6. Falsity. The proposition F implies every proposition. It is accordingly the strongest proposition.
7. Negation. The negation -P says that P does not hold. -P is the same thing as P -> F and is thus the weakest proposition R such that P ^ R imply Q.

Quantified propositional logic allows one to not only use the propositional connectives just listed but to also quantify over propositions:
I. Universal quantification. ∀X.P(X) says that P(X) holds for every proposition X. ∀X.P(X) is the weakest proposition that implies every proposition of the form P(X).
II. Existential quantification. ∃X.P(X) says that P(X) holds for at least one proposition X. ∃X.P(X) is the strongest proposition that is implied every proposition of the form P(X).

As a simple illustration of the things we have just listed, one can use negation, disjunction, and universal quantification to express LEM:
∀X.X v -X

Among the ingredients 1.-7. and I.-II. that we have listed above, it suffices to use 3. and I. as the basic primitives. That all of QIPL follow from these two ingredients alone may be a first indication that it is a remarkable theory with lots of power.

A second illustration comes from the fact that QIPL is Turing-complete. In spite of involving so little in its foundations, QIPL turns out to be (in a sense) maximally expressive.

### The Mereological Interpretation of QIPL
As presented above, QIPL is a language where all that one reasons about are propositions. Some alternative interpretation of QIPL is therefore necessary if one wishes to see it as an all-purpose language.

We get the interpretation we need by regarding P → Q as saying ‘P includes Q as a part’ (or ‘Q is part of P’). If P and Q are propositions and then this makes sense when propositions are thought of as pieces of information: P → Q holds just in case the information in P includes the information in Q as a part.

But P and Q can be non-propositions too, and P → Q will then be what needs to be added to P if one is to get Q. P ^ Q will be the smallest thing that includes all the parts of P as well as all the parts of Q while P v Q will be the largest thing that is included as a part in P as well as in Q.

Interpreted this way, QIPL becomes a calculus for reasoning about parts. This means that the subject is mereology, a word derived from the Greek word μέρος (‘part’).

Following notation that is widespread in mereology, we write P + Q instead of  P ^ Q and P \times Q instead of P v Q. We similarly write Q – P instead of P → Q.

The operations ‘+,’ ‘\times,’ and ‘-’ are all basic ingredients in Eidos.

P + Q,  P \times Q, and Q – P are not necessarily objects of the same kind as P and Q. Where one has two different objects P and Q, one has the object P + Q, but P + Q must not be counted as a third object, as if any two objects were magically accompanied by a third.

What are the roles of P + Q,  P \times Q, and Q – P in mathematics? If P and Q are things that may turn out to be identical (that is, P=Q is a possibility) and if it is further possible for P and/or Q to equal ‘nothing’ then P + Q = 0 says the same thing as P = 0 ^ Q = 0, where 0 stands for ‘nothing’ and is characterized by the fact that it is part of every object. In other words, treating P + Q as nothing amounts to exactly the same thing as treating both P and Q as nothing.

But when does one set an object equal to ‘nothing’ in mathematics? One way to answer is to note that partial equivalence relations are present everywhere in mathematics (whether they are mentioned explicitly or not). These are relations that are symmetric and transitive but not necessarily reflective. An object that fails to be equivalent to itself is effectively ‘nothing.’

But how do partial equivalence relations arise in mathematics? Here are some ways to answer:
1. Relations that are symmetric and transitive are more general than relations that are reflective, symmetric, and transitive. Partial equivalence relations thus include equivalence relations but are even more omnipresent.
2. Any partial function f : S → T induces a partial equivalence relation on S.
3. In a group G, the object 0 may be thought of as ‘nothing.’ A group homomorphism f : G1 → G2 can then be seen as inducing a partial equivalence relation on G1 according to which two elements a and b are equivalent if they map to the same non-zero element in G2.

It is possible to work in Eidos without knowing anything about equivalence relations or partial equivalence relations, but equivalence relations or partial equivalence relations are very much ‘built-in’ when pieces of mathematics are expressed in Eidos.

## Familiar Mathematics on Top of an Unfamiliar Framework
As the next section will demonstrate through many examples, Eidos can look very intuitive and familiar. This is, however, a bit deceptive as it misses the point behind Eidos. The following subsections illustrate how Eidos is actually unlike any other language that has been devised so far.

This section contains advanced material and may be skipped.

### Sets, Individuals, and Propositions As *Mereological Objects*
Although Eidos distinguishes between sets, individuals, and propositions, they are all interconvertible. Starting with a set/individual/proposition X, one may write X\#set to view X as a set, X\#individual to view X as an individual, and X\#proposition to view X as a proposition. A fourth optioon, finally, is to write X\#mereological to get a purely mereological view on X. One is dealing with exactly the same thing in each case, just viewed in different ways.

Writing X#mereological gives one a 'bare' mereological view on X. The mereological view on X is, however, included also when X is viewed as a set or a proposition. One can thus always use X#set or X#proposition in place of X#mereological.

Some of the syntactic differences between the different ways of viewing objects are as follows:
* Individuals are the things that can appear syntactically to the left of '∈' and sets are similarly the things that can appear to the right of '∈'. 
* Sets are the things that can appear as operands of '∪' and '∩'. The relation '⊆' is likewsie a relation between sets.
* Propositions are the things that can appear as operands of '→', '↔', '←', '∨', '∧', and '¬'.
* The operands of the relation ≤ and of the operations '+', '×', '-', '∸', and '⇒' need to be objects viewed mereologically, but this includes sets and propositions.
* For a sort S, =_S is a relation between individuals (not just individuals of sort S) while =^S is a relation between objects viewed mereologically (including sets and propositions).
* The relation = is a relation between objects viewed mereologically (including sets and propositions).
* The singleton operation '{ _ }' goes from individuals to sets. For an individual x, '{x}' has exactly the same effect as 'x#set'.

## Sets, Individuals, and Propositions Can Always Be Projected Onto *Any* Sort
If X is a set/individual/proposition/mereological object then &lt;S&gt;(X) is a set/individual/proposition/mereological object of sort S. &lt;S&gt;(X) can never be a 'typing error' but will always result in (what one can think of as) the closest approximation to X that has sort S.

Writing &lt;S&gt;(X) has the same effect as writing &lt;S#min, S#max&gt;(X) and will 'project' X onto the 'interval' delimited by S#min and S#max.

In the case where X is a mereological object, &lt;S#min, S#max&gt;(X) is the same thing as (X + S#min) × S#max and that is in turn the same thing as (X × S#max) + S#min. The only difference when X is a set, an individual, or a proposition is that &lt;S#min, S#max&gt;(X) will stay a set/individual/proposition.

### Functions and Relations Defined For Individuals Are Also Defined for Sets
A common convention in mathematics allows one to write f(S) for the set {f(x) : x ∈ S}. Eidos fully embraces this convention for functions as well as relations.

What is the difference, then, between a function/relation defined for individuals and one defined for sets? To begin with, one *cannot* use individuals as arguments for functions/relations defined for sets. For an individual x, one needs to first write {x} or x#set to view x as a set.

A more fundamental difference is that a function/relation defined for individuals is limited in what it can do when applied to sets. The function/relation will support sets as arguments, but it is constrained in what it can do when used in that way.

### 

## Some Simple Examples

[...]

## File Extensions and Sublanguages
The language uses the file ending ".theory" for all its files, but it is possible to be more specific:
* Files with the ending ".eq.theory" define  theories in *equational logic*,
* files with the ending ".reg.theory" define  theories in *regular logic*,
* files with the ending ".coh.theory" define  theories in *coherent logic*,
* files with the ending ".fol.theory" define  theories in *first-order logic*, and
* files with the ending ".sol.theory" define  theories in *second-order logic*.
* files with the ending ".prop.theory" define  theories in (unquantified) *propositional logic*.
* files with the ending ".mereo.theory" define purely mereological theories (no logic, only things such as mereological sums and mereological differences).

These are all sublanguages of the full language.

## Language Constructs

### Whitespace and Comments
Like in the C programming language, whitespace is ignored. Comments are likewise as in C:
* A multiline comment starts with "/*" and ends with "*/"
* A signline comment starts with "//"

### Theories
A theory starts with "{" and ends with "}". Every file defines a theory and must thus begin with "{" and end with "}".

The fact that a file defines a theory may also be guessed from the file ending: ".theory".

A theory may include *subtheories*, as explained below.

### Sections
A theory uses 0 or more of these sections:
* A 'signature' section,
* an 'axioms' section, and
* a 'subtheories' section.

At most one section of each kind is allowed.

A theory that includes all these sections may look as follows:
```
{
  signature {
  },
  axioms {
  },
  subtheories {
  }
}
```

As this example illustrates, sections are separated by commas.

### Signature
The signature of a theory consists of definitions of sorts, functions, relations, individuals, sets, or propositional constants.

For functions and relations, a distinction exists between those that pertain to first-order logic and those that pertain to second-order logic. The former have names that start with a lowercase letter while the latter have names that start with an uppercase letter.

#### Sorts
Sorts have names that start with uppercase letters. A typical sort declaration looks as follows:
  sort MySort;

It is possible to declare one sort to be a subsort of another sort:
  MyOtherSort subsort MySort;

It is likewise possible to declare one sort to be a quotient sort of another sort:
  MyQuotientSort quotient MySort;

As a final option, one sort can be declared to be a 'subquotient' of another sort:
  MySubQuotient subquotient MySort;

A theory that declares all these sorts while containing nothing else looks as follows:
```
{
  signature {
    sort MySort;
    MyOtherSort subsort MySort;
    MyQuotientSort quotient MySort;
    MySubQuotient subquotient MySort;
  }
}
```

#### Built-In Sorts
Three special sorts are 'built-in' and come for free in any theory:
* The sort 𝔻 functions exactly like ordinary sorts but is meant to be used as 'the domain' in single-sorted theories.
* The sort 𝕌 stands for 'the universe' and includes absolutely everything in a theory (to be exact, a set of any sort can also be viewed as a set of sort 𝕌).
* The sort ℙ is used for propositions and is special in several ways.

The idea behind the sort 𝔻 is to provide support for single-sorted theories in a natural way. It is possible to use no sorts at all except for the sort 𝔻.

At the same time, one also has the option of never using the sort 𝔻 and to always declare sorts explicitly. This allows the language to support many-sorted theories in a natural way.

Even as one uses many sorts, the sort 𝔻 can still be used for what one views as 'the main sort' -- the sort that the theory aims to describe -- with other sorts being 'auxiliary sorts' that aid in the description of the main sort.

For a sort S other than ℙ, the notation x : S signifies that x is an individual of sort S while X ⊆ S signifies that X is a set of sort S.

By contrast, X : ℙ signifies that X is a proposition. One consequence of this is that X can appear as an operand of '→', '⊆', '↔', '←', '∨', '∧', and '¬'.

Objects of sort ℙ are delimited by ℙ#min and ℙ#max. The former can also be written '⊤' and the latter can also be written '⊥'.

Under typical circumstances, an object can appear as an operand of '→', '↔', '←', '∨', '∧', and '¬' will also have sort ℙ, but it is possible to start with any object X and write X#proposition to view X as a proposition. This will make it possible to use X as an argument of '→', '↔', '←', '∨', '∧', and '¬' but will not make into an object of sort ℙ.

#### Individuals
The following declares someObject to be an individual of sort S:
  someObject : S;

Except in the case of reflection (an advanced topic), names of individuals must always start with lowercase letters.

#### Sorted Identity Relations
If S is any sort other than the special sorts 𝕌 and ℙ then:
1. =_S is the identity relation among individuals of sort S, while
2. =^S is the identity relation among sets of sort S (two sets are identical just in case they have the same elements).

For a sort with n individuals, =_S allows one to distinguish between n objects (namely the individuals just mentioned) while =^S allows one to distinguish between 2<sup>n</sup> things.

### Subsorts
If T is a subsort of S then it is possible an individual of sort S to fail to be self-identical in the sense of =_T. The following theory demonstrates this:
```
{
  signature {
    sort S;
    T subsort S;
    a : S;
	},
  axioms {
    assertions {
      ¬(a =_T a);
      a =_S a;
    }
  }
}
```

### Quotients
If T is a quotient sort of S then it is possible two different individuals of sort S to be the same individual in the sense of =_T. The following theory demonstrates this:
```
{
  signature {
    sort S;
    T quotient S;
    a : S;
    b : S;
  },
  axioms {
    assertions {
      ¬(a =_S b);
      a =_T b;
    }
  }
}
```

#### Sets
The following declares MySet to be a set of sort S:
  MySet ⊆ S;

The following illustrates how individuals and sets may be combined in a theory:
```
{
  signature {
    sort MySort;
    myIndividual : MySort;
    MySet ⊆ MySort;
  },
  axioms {
    assertions {
      myIndividual ∈ MySet;
    }
  }
}
```

#### First-Order Functions
First-order functions have names that start with lowercase letters. Here is a simple example:
  f : S, T → U

This declares f to be a 2-ary function where the first argument has sort S, where the second argument has sort T, and where the result has sort U.

Here is another example:
  inv : 𝔻 → 𝔻

This declares inv to be a 1-ary function whose argument has sort 𝔻 and whose result has sort 𝔻.

Here is an example of a theory that uses a function:
```
{
  signature {
    sort S;
    sort T;
    f: S, S → T;
  },
  axioms {
    facts {
      x : S, y : S, f(x, y) =_T f(y, x);
    }
  }
}
```

This theory specifies that f(x, y) is identical to f(y, x), where x and y have sort S.

#### First-Order Relations
First-order relations have names that start with uppercase letters and have declaratations that resemble the declarations for sets (see above):
  MyRelation ⊆ S, T, U;

This example declares MyRelation to be a 3-ary relation where the first argument has sort S, where the second argument has sort T, and where the third argument has sort U.

Here is an example of a theory that uses a relation:
```
{
  signature {
    sort S;
    R ⊆ S, S;
  },
  axioms {
    assertions {
      x : S, y : S, R(x, y) ↔ R(y, x);
    }
  }
}
```

This theory specifies that R(x, y) holds just in case R(y, x) holds, where x and y are individuals of sort S.

#### Propositional Constants
Propositional constants start with uppercase letters and have sort ℙ.

Here is an example of how a propositional constant may be declared:
  P : ℙ;

Here is an example of a theory that uses propositional logic:
```
{
  signature {
    P : ℙ;
    Q : ℙ;
    R : ℙ;
  },
  axioms {
    assertions {
      P → (Q ∧ R);
      Q → (P ∨ ¬R);
    }
  }
}
```

The first axiom says that if P holds then Q and R both hold. The second axiom says that if Q holds then either P or ¬R ('the negation of R') holds.

#### Second-Order Functions
Second-order functions have names that start with uppercase letters and are declared like first-order functions:
  F : S, T → U;

This example declares F to be a 2-ary function where the first argument is a set with sort S, where the second argument is a set with sort T, and where the result is a set with sort U.

Here is an example of a theory that uses second-order functions:
```
{
  signature {
    G : 𝔻 → 𝔻;
    H : 𝔻 → 𝔻;
    s ⊆ 𝔻
  },
  axioms {
    assertions {
      G(s) =_𝔻 H(s);
    }
  }
}
```

#### Second-Order Relations
A second-order relation is the same thing as a second-order function whose result has sort ℙ. For example, the following is a second-order relation:
  R : 𝔻, 𝔻 → ℙ

Here is an example of a theory that defines a second-order relation:
```
{
  signature {
    XOR : ℙ, ℙ → ℙ;
  },
  axioms {
    assertions {
      P : ℙ, Q : ℙ, (XOR(P, Q) ↔ ((¬P ∧ Q) ∨ (P ∧ ¬Q)));
    }
  }
}
```

### Different kinds of axioms
The following example illustrates how two things may be *made* identical:
```
{
  signature {
    a : 𝔻;
    b : 𝔻;
  },
  axioms {
    facts {
      a =_𝔻 b;
    }
  }
}
```

The following example illustrates how two things may be *asserted* to be identical:
```
{
  signature {
    a : 𝔻;
    b : 𝔻;
  },
  axioms {
    assertions {
      a =_𝔻 b;
    }
  }
}
```

So what is the difference? The axioms in the 'assertions' section is more powerful than the axioms in the 'facts' section in the sense that they can use the connective ¬ that negates formulas along with ⊥ (falsity). The 'facts' section is more powerful in the sense that what is asserted there is *enforced*.

The 'facts' section corresponds to 'positive logic' while the 'assertions' section corresponds to logic in general.

To see why it would be impossible in general to enforce what is included in the 'assertions' section, note that a theory can assert "¬(a =_𝔻 b)" in addition to "a =_𝔻 b". For this reason, the assertion "a =_𝔻 b" is understood as really meaning "either a and b are identical (as individuals of sort 𝔻) *or there is a contradiction*".

This does tell one that a and b are identical (as individuals of sort 𝔻), but only *as long as one can rule out the case of a contradiction*.

Here is an example of a theory where there is a contradiction:
```
{
  signature {
    a : 𝔻;
    b : 𝔻;
    P : ℙ
  },
  axioms {
    assertions {
      a =_𝔻 b;
      P;
      ¬P;
    }
  }
}
```

The following is a simple example of an equational theory that uses the 'facts' section:
```
{
  signature {
    n : 𝔻;
    op : 𝔻, 𝔻 → 𝔻;
  },
  axioms {
    facts {
      x : 𝔻, y : 𝔻, z : 𝔻, op(x, op(y, z)) =_𝔻 op(op(x, y), z);
      x : 𝔻, op(n, x) =_𝔻 x;
      x : 𝔻, op(x, n) =_𝔻 x;
    }
  }
}
```

A third subsection called 'metafacts' allows one to work in a 'metafacts language' as compared with what one gets with the other two sections.

### Logical Connectives
The following connectives may be used among propositions:
* ¬ (negation),
* → (implication),
* ← (reverse implication),
* ↔/= (biimplication/identity)
* ∧ (conjunction),
* ∨ (disjunction),
* ⊤ (top/truth), and
* ⊥ (bottom/falsity).

P ← Q stands for the same thing as Q → P and there is likewise no difference between P ↔ Q and P = Q.

⊤ is implied by all propositions while ⊥ implies all propositions.

All the laws of intuitionistic logic are guaranteed to hold among propositions.

### Propositional Quantification
It is possible to quantify over all propositions. For example, the following says that the Law of Excluded Middle holds:
  ∀X:ℙ (X ∨ ¬X)

For another example, the following asserts that the Weak Law of Excluded Middle holds:
  ∀X:ℙ (¬X ∨ ¬¬X)

It is likewise possible to use existential quantification among propositions:
  ∃X:ℙ ∀Y:ℙ X → Y

### Quantification over Individuals and Quantification over Sets
The following asserts that at least one object of sort S belongs to the set MySet:
```
{
  signature {
    sort S;
    MySet ⊆ S;
  },
  axioms {
    assertions {
      ∀x:S x ∈ MySet
    }
  }
}
```

The following asserts that any two sets of sort S are identical:
```
{
  signature {
    sort S;
  },
  axioms {
    assertions {
      ∀X⊆S ∀Y⊆S X =_S Y
    }
  }
}
```

### Free Variables
Eidos requires all variables to have sorts, including free variables (variables that are not bound through quantifiers).

Free variables are listed at the beginning of an expression using a bracket notation. Here are two examples:
  x : S, x ∈ MySet
  x : S, X ⊆ S, x ∈ Y

### Sets as Properties
There is no distinction between 'sets of sort S' and 'properties of sort S'. The following two lines assert exactly the same thing:
  i ∈ MySet
  MySet(i)

(For practical purposes, sets/properties may be thought of as 1-ary relations.)

### Singleton sets
For an individual x, {x} is the set whose only member is x.

This means that the following two lines assert the same thing:
  a ∈ {b}
  a = b

### Subsets
For two sets S and T, the following asserts that all the members of S and members of T:
  S ⊆ T

For an individual a and a set S, the following are thus alternative ways of asserting the same thing:
  a ∈ S
  {a} ⊆ S

### Unions and Intersections
For two set S and T, their intersections and unions can be expressed as follows:
  S ∩ T
  S ∪ T  

The following are equivalent:
  (S ∩ T)(a)
  S(a) ∧ T(a)

The following are likewise equivalent:
  (S ∪ T)(a)
  S(a) ∨ T(a)

### Empty Sets and Maximal Sets
For a sort S, and a property P of sort S, the following always hold:
  S#min ⊆ P
  P ⊆ S#max

In a sort-relative sense, S#min is the empty set while S#max is the universal set.

If S is a subsort of T then it is possible for individuals in T to fail to be elements of S#max.




### Projecting onto a Sort
For any sort S any any object x, &lt;S&gt;(x) expresses the "projection" of x onto the sort S. This can be thought of as the closest possible approximation to x among things that have sort S.

The following will always hold:
  S#min ⊆ &lt;S&gt;(x)
  &lt;S&gt;(x) ⊆ S#max
  &lt;S&gt;(&lt;S&gt;(x)) = &lt;S&gt;(x)

### Projecting onto an Interval



### The Domain of a n-ary Function/Relation for n > 1
For n > 1, an n-ary first-order function/relation may be viewed as really being a 1-ary first-order function/relation defined on an n-tuple. This perspective is directly supported by the language.

Given f : A, B → C, the meaning of f#dom is 'the sort whose individuals are all 2-tuples that f is defined for.'

Given r ⊆ A, B, C, the meaning of r#dom is 'the sort whose individuals are all 3-tuples that r is defined for.'

The following may all be referenced:
* f#dom#min,
* f#dom#max,
* r#dom#min, and
* r#dom#max.

### The Arguments of a Function




### The metafacts Section






### Subtheories
