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
    have compl_eq
      -- Double union
      : Aᶜ = (⋃ (x : X) (hx : x ∈ Aᶜ), U x hx)
    := by
      ext x
      constructor
      · intro hmem
        specialize hUmem x hmem
        simp_rw [neighborhoods, Nbhd, Set.mem_setOf_eq] at hUmem
        simp_rw [Set.mem_compl_iff, Set.mem_iUnion]
        use x, hmem
        exact hUmem.2
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
    exact (hUmem x hnmem).1

structure FilterBase (X : Type*) where
  Sets : Set (Set X)
  univ_Sets : Set.univ ∈ Sets
  inter_Sets {A B} : A ∈ Sets → B ∈ Sets → A ∩ B ∈ Sets

def upwardClosure
  {X : Type*}
  (B : Set (Set X))
  : Set (Set X) :=
  {C | ∃ A ∈ B, A ⊆ C}

def generateFilter
  {X : Type*}
  (B : FilterBase X)
  : Filter X :=
  {
    Sets := upwardClosure B.Sets
    univ_Sets := by
      use Set.univ
      exact ⟨B.univ_Sets, by trivial⟩
    inter_Sets := by
      rintro C D ⟨A, hAmem, hAsubC⟩ ⟨A', hA'mem, hA'subD⟩
      rw [upwardClosure]
      simp only [Set.mem_setOf_eq, Set.subset_inter_iff]
      use A ∩ A'
      constructor
      · exact B.inter_Sets hAmem hA'mem
      · constructor
        · intro x hx
          exact hAsubC hx.1
        · intro x hx
          exact hA'subD hx.2
    upward_Sets := by
      rintro C D ⟨A, hAmem, hAsubC⟩ A_sub_B
      rw [upwardClosure]
      use A
      exact ⟨hAmem, by exact Set.Subset.trans hAsubC A_sub_B⟩
  }

-- x in closure if

-- x ∈ Abar if and only if every neighborhood of x nontrivially intersects A
lemma in_closure_iff_nbhd_inter
  {X : Type*} [Topology X]
  (A : Set X)
  (x : X)
  : x ∈ closure A ↔ ∀ U ∈ neighborhoods x, (A ∩ U) ≠ ∅
:= by
  by_cases hxmemA : x ∈ A
  · constructor
    · intro hcl U hU heq
      have hxmemU := nbhd_mem_self x U hU
      rw [Set.eq_empty_iff_forall_notMem] at heq
      specialize heq x
      simp only [Set.mem_inter_iff, not_and] at heq
      exact heq hxmemA hxmemU
    · intro hnbhd U hUmem
      rw [Set.mem_setOf_eq] at hUmem
      exact hUmem.1 hxmemA
  · constructor
    · intro hcl U hU heq

    · intro hnbhd U hUmem


    --
  --   simp_rw [neighborhoods, Nbhd, Set.mem_setOf_eq] at hU
  --   have hnsub : ¬A ⊆ Uᶜ := by
  --     intro hsub
  --     rw [closure] at hcl
  --     simp at hcl
  --     specialize hcl Uᶜ hsub (by simp_all only [compl_compl])
  --     have hU := hU.2
  --     contradiction
  --   rw [Set.not_subset] at hnsub
  --   rcases hnsub with ⟨a, haA, hnmem⟩
  --   rw [Set.mem_compl_iff, not_not] at hnmem
  --   rw [Set.eq_empty_iff_forall_notMem] at heq
  --   specialize heq a
  --   simp only [Set.mem_inter_iff, not_and] at heq
  --   exact heq haA hnmem
  -- · intro hnbhd U hUmem
  --   rw [Set.mem_setOf_eq] at hUmem
  --   have hsub : A ∩ Uᶜ = ∅ := by
  --     aesop
  --   have : x ∉ Uᶜ := by
  --     simp_rw [Set.mem_compl_iff, not_not]










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

-- TODO use different nbhd definition, note it
