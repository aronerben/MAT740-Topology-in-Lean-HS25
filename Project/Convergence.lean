import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Existing

open TopologicalSpaces
open Filters

namespace Convergence
abbrev Filter := Filters.Filter

def closure
  {X : Type*} [Topology X]
  (A : Set X)
  : Set X :=
  ⋂₀ {B : Set X | A ⊆ B ∧ Closed B}

lemma infinite_intersect_closed
  {X : Type*} [Topology X]
  (S : Set (Set X))
  (h : ∀ B ∈ S, Closed B)
  : Closed (⋂₀ S)
:= by
  rw [Closed, Set.compl_sInter]
  apply Open_sUnion
  intro A hmem
  rw [Set.mem_image] at hmem
  rcases hmem with ⟨B, hBmem, hB⟩
  rw [←hB, ←Closed]
  exact h B hBmem

theorem closed_iff_closure_self_eq
  {X : Type*} [Topology X]
  (A : Set X)
  : Closed A ↔ closure A = A
:= by
  constructor
  · intro hcl
    ext x
    constructor
    · intro hel
      simp_rw [closure,
          Set.mem_sInter,
          Set.mem_setOf_eq] at hel
      exact hel A ⟨by trivial, hcl⟩
    · intro hel
      rw [closure]
      simp_rw [Set.mem_sInter,
          Set.mem_setOf_eq]
      rintro B ⟨hsub, _⟩
      exact hsub hel
  · intro heq
    rw [closure] at heq
    rw [←heq]
    apply infinite_intersect_closed
    intro B hBmem
    rw [Set.mem_setOf] at hBmem
    exact hBmem.2

lemma nbhd_mem_self
  {X : Type*} [Topology X]
  (x : X)
  : ∀ U ∈ neighborhoods x, x ∈ U
:= by
  intro U hU
  simp_rw [neighborhoods, Nbhd, Set.mem_setOf_eq] at hU
  exact hU.2

theorem closed_iff_compl_nhds
  {X : Type*} [Topology X]
  (A : Set X)
  : Closed A ↔ ∀ x ∈ Aᶜ, ∃ U ∈ neighborhoods x, U ⊆ Aᶜ
:= by
  constructor
  · intro hcl x hx
    simp_rw [neighborhoods, Nbhd, Set.mem_setOf_eq]
    use Aᶜ
    constructor
    · rw [Closed] at hcl
      exact ⟨hcl, hx⟩
    · trivial
  · intro hnbhd
    choose U hUmem hUsub using hnbhd
    -- Pick out opens
    let V := fun x => U x
    have hV : ∀ x (hx : x ∈ Aᶜ), Nbhd (V x hx) x := by
      intro x hx
      exact hUmem x hx
    have compl_eq
      -- Double union
      : Aᶜ = (⋃ (x : X) (hx : x ∈ Aᶜ), V x hx)
    := by
      ext x
      constructor
      · intro hmem
        specialize hV x hmem
        rw [Nbhd] at hV
        simp_rw [Set.mem_compl_iff, Set.mem_iUnion]
        use x, hmem
        exact hV.2
      · intro h
        simp_rw [Set.mem_iUnion] at h
        rcases h with ⟨z, hz, memUz⟩
        apply hUsub z hz
        exact memUz
    rw [Closed, compl_eq]
    apply Open_iUnion
    intro x
    apply Open_sUnion
    intro W hmemrange
    simp only [Set.mem_range, Set.mem_compl_iff] at hmemrange
    rcases hmemrange with ⟨hnmem, heq⟩
    rw [←heq]
    exact (hV x hnmem).1

theorem in_closure_iff_filter_conv
  {X : Type*} [Topology X]
  (A : Set X)
  (x : X)
  : x ∈ closure A ↔ ∃ G : Filter X, G lim x ∧ A ∈ G ∧ ∅ ∉ G
:= by
  constructor
  · intro hcl

  · intro hex
end Convergence
