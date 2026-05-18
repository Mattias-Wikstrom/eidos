-- Eidos compiler runtime library
-- Structures and definitions reused across all generated Lean 4 output.

-- Primitives

def IsWithinBounds (lo hi x : Prop) : Prop := (hi → x) ∧ (x → lo)

def ProjectIntoInterval (x lo hi : Prop) : Prop := (x ∧ lo) ∨ hi

def WrapFact (x y : Prop) : Prop := (x ∧ y) ↔ x

def WrapAssertion (x y z : Prop) : Prop := (x ∧ (y ∨ z)) ↔ x

def WrapMetafact (x y : Prop) : Prop := (x ∧ y) ↔ x

-- Structures

structure Sort where
  Min : Prop
  Max : Prop
  ordering : Max → Min

structure Subquotient (outer inner : Sort) where
  upper : outer.Max → inner.Max
  lower : inner.Min → outer.Min
