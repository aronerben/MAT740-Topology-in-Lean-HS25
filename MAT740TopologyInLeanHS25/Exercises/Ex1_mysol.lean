import Mathlib.Tactic

-- # Exercise 1: Logic
variable (p q r s : Prop)

/-
NOTE:
Exercise marked with
**************
are the mandatory ones mentioned on the sheet.
-/

-- tauto/aesop/simp solve most/all

-- Commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  · intro h
    exact ⟨h.right, h.left⟩
  · intro h
    exact ⟨h.right, h.left⟩
example : p ∨ q ↔ q ∨ p := by
  constructor
  · intro h
    rcases h with (a | b)
    · right
      exact a
    · left
      exact b
  · intro h
    rcases h with (a | b)
    · right
      exact a
    · left
      exact b

-- Associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  · intro h
    exact ⟨h.left.left, ⟨h.left.right, h.right⟩⟩
  · intro h
    exact ⟨⟨h.left, h.right.left⟩, h.right.right⟩
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  · intro h
    rcases h with ((a | b) | c)
    · left
      exact a
    · right
      left
      exact b
    · right
      right
      exact c
  · intro h
    rcases h with (a | b | c)
    · left
      left
      exact a
    · left
      right
      exact b
    · right
      exact c

-- Distributivity of ∧ with respect to ∨ and vice versa
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · intro h
    rcases h with ⟨a, b⟩
    rcases b with (c | d)
    · left
      exact ⟨a, c⟩
    · right
      exact ⟨a, d⟩
  · intro h
    rcases h with (⟨a, b⟩ | ⟨a, c⟩)
    · exact ⟨a, Or.inl b⟩
    · exact ⟨a, Or.inr c⟩
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  · intro h
    rcases h with (a | ⟨b, c⟩)
    · exact ⟨Or.inl a, Or.inl a⟩
    · exact ⟨Or.inr b, Or.inr c⟩
  · intro h
    rcases h with ⟨(a | b), (c | d)⟩
    · exact Or.inl a
    · exact Or.inl a
    · exact Or.inl c
    · exact Or.inr ⟨b, d⟩

-- Other properties
-- Is currying, but with Props
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  · intros h1 h2
    exact h1 h2.left h2.right
  · intros h a b
    exact h ⟨a, b⟩
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  · intro h
    constructor
    · intro a
      exact h (Or.inl a)
    · intro b
      exact h (Or.inr b)
  · intros h a
    rcases h with ⟨h1, h2⟩
    rcases a with (b | c)
    · exact h1 b
    · exact h2 c
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  · intro h
    constructor
    · intro a
      exact h (Or.inl a)
    · intro b
      exact h (Or.inr b)
  · intro h
    intro a
    rcases a with (b | c)
    · exact h.left b
    · exact h.right c
example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intros h a
  rcases h with (b | c)
  · exact b a.left
  · exact c a.right
example : ¬(p ∧ ¬p) := by
  intro h
  rcases h with ⟨a, b⟩
  contradiction
example : p ∧ ¬q → ¬(p → q) := by
  intros h a
  have b := a h.left
  have nq := h.right
  contradiction
example : ¬p → (p → q) := by
  intros h a
  exfalso
  exact h a
example : (¬p ∨ q) → (p → q) := by
  intros h a
  rcases h with (b | c)
  · exfalso
    exact b a
  · exact c
example : p ∨ false ↔ p := by
  constructor
  · intro h
    rcases h with (a | b)
    · exact a
    · contradiction
  · intro h
    exact Or.inl h
example : p ∧ false ↔ false := by
  constructor
  · intro h
    exact h.right
  · intro h
    contradiction

-- Classical reasoning required (`by_contra`, `by_cases`, `push_neg`)
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by
  intro h
  by_cases h1 : p
  · have q := h h1
    rcases q with (a | b)
    · left
      intro hp
      exact a
    · right
      intro hp
      exact b
  · left
    intro hp
    contradiction
-- 3/4 De'Morgans laws are constructive, this one isn't
-- **************
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  by_cases h1 : p
  · right
    intro h2
    have := h ⟨h1, h2⟩
    contradiction
  · left
    exact h1
example : ¬(p → q) → p ∧ ¬q := by
  intro h
  push_neg at h
  exact h
-- **************
example : (p → q) → (¬p ∨ q) := by
  intro h
  by_cases h1 : p
  · right
    exact h h1
  · left
    exact h1
example : (¬q → ¬p) → (p → q) := by
  intros h hp
  by_cases hq : q
  · exact hq
  · have hhp := h hq
    contradiction
-- LEM
example : p ∨ ¬p := by
  by_cases h : p
  · left
    exact h
  · right
    exact h
-- **************
example : (((p → q) → p) → p) := by
  intro h
  by_cases hp : p
  · exact hp
    -- Similar approach to show that LEM <=> Double Negation Elimination
  · have hhp := h (fun p => False.elim (hp p))
    exact hhp
