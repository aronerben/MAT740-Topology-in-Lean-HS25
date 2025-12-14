import Mathlib.Tactic

-- All the definitions from existing files, copied together
-- to have an overview of all definitions used in the project

universe u v

namespace TopologicalSpaces

open Set

/- A topology on a type `X` -/
class Topology (X : Type u) : Type u where
  /- A predicate witnessing that a set `s : Set X` is open. -/
  Open : Set X → Prop
  /- The universal set {x : X | True} is open. -/
  Open_univ : Open Set.univ
  /- Binary intersections of opens are open. -/
  Open_inter : ∀ s t, Open s → Open t → Open (s ∩ t)
  /- Unions of families of open sets are open. -/
  Open_sUnion : ∀ s, (∀ t ∈ s, Open t) → Open (⋃₀ s)

variable {X : Type u} {Y : Type v} [Topology X] [Topology Y] {s t : Set X}

/- Predicate on subsets of ambient topology on X. -/
def Open (s : Set X) : Prop := Topology.Open s

/- A set is closed if its complement is open. -/
@[simp]
def Closed (s : Set X) : Prop := Open sᶜ

@[simp]
theorem Open_sUnion {s : Set (Set X)} (h : ∀ t ∈ s, Open t) : Open (⋃₀ s) :=
  Topology.Open_sUnion s h

@[simp]
theorem Open_iUnion
  {I : Type*} {A : I → Set X} (h : ∀ i, Open (A i)) :
  Open (⋃ i, A i) := by
    rw [← sUnion_range]
    apply Open_sUnion
    intro U hU
    rw [mem_range] at hU
    obtain ⟨i, hi⟩ := hU
    specialize h i
    rw [hi] at h
    exact h

@[simp]
theorem Open_empty : Open (∅ : Set X) := by
  have w : ∀ t ∈ (∅ : Set (Set X)), Open t := by
    intro t ht
    contradiction
  apply Open_sUnion at w
  rw [sUnion_empty] at w
  exact w

@[simp]
def Nbhd (N : Set X) (x : X) := ∃ V, Open V ∧ x ∈ V ∧ V ⊆ N

end TopologicalSpaces

namespace Filters
open TopologicalSpaces

variable {X : Type*} {F G : Filter X}

-- Modified to match the book
structure Filter (X : Type*) where
  Sets : Set (Set X)
  nonempty_Sets : Sets ≠ ∅
  upward_Sets {A B} : A ∈ Sets → A ⊆ B → B ∈ Sets
  inter_Sets {A B} : A ∈ Sets → B ∈ Sets → ∃ C ∈ Sets, C ⊆ A ∩ B

instance instMembership : Membership (Set X) (Filter X) where
  mem := fun F U ↦ U ∈ F.Sets

def ProperFilter
  {X : Type*}
  (F : Filter X)
  : Prop :=
  ∅ ∉ F

theorem filter_eq : ∀ {F G : Filter X}, F.Sets = G.Sets → F = G := by
  intro F G h
  cases F
  cases G
  simp only [Filter.mk.injEq]
  exact h

@[ext]
theorem ext (h : ∀ A, A ∈ F ↔ A ∈ G) : F = G := by
  apply filter_eq
  ext A
  apply h

def neighborhoods [Topology X] (x : X) : Set (Set X) := {U | Nbhd U x}

def filter_convergence [Topology X] (F : Filter X) (x : X) : Prop :=
  neighborhoods x ⊆ F.Sets

notation:50 F:50 " lim " x:50 => filter_convergence F x
end Filters
