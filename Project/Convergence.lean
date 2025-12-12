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

lemma inter_nonempty_iff_el
  {X : Type*}
  (A B : Set X)
  (x : X)
  (hA : x ∈ A)
  (hB : x ∈ B)
  : (A ∩ B) ≠ ∅
:= by
  intro heq
  rw [Set.eq_empty_iff_forall_notMem] at heq
  specialize heq x
  simp only [Set.mem_inter_iff, not_and] at heq
  exact heq hA hB

lemma inter_empty_iff_subset_compl
  {X : Type*}
  (A B : Set X)
  : A ∩ B = ∅ ↔ A ⊆ Bᶜ
:= by
  constructor
  · intro heq x hxA
    rw [Set.mem_compl_iff]
    intro hxB
    exact inter_nonempty_iff_el A B x hxA hxB heq
  · intro hsub
    ext x
    constructor
    · intro hmem
      simp only [Set.mem_empty_iff_false]
      rw [Set.mem_inter_iff] at hmem
      specialize hsub hmem.1
      have : x ∈ B := hmem.2
      contradiction
    · intro hmem
      contradiction

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
      exact inter_nonempty_iff_el A U x hxmemA hxmemU heq
    · intro hnbhd U hUmem
      rw [Set.mem_setOf_eq] at hUmem
      exact hUmem.1 hxmemA
  · constructor
    · intro hcl U hU heq
      rw [closure] at hcl
      simp only [Set.mem_sInter, Set.mem_setOf_eq, and_imp] at hcl
      simp_rw [neighborhoods, Nbhd, Set.mem_setOf_eq] at hU
      have hsub := (inter_empty_iff_subset_compl A U).mp heq
      specialize hcl Uᶜ hsub (by simp_all only [Closed, compl_compl])
      have hU := hU.2
      contradiction
    · intro hnbhd U hUmem
      rw [Set.mem_setOf_eq] at hUmem
      simp_rw [neighborhoods, Nbhd, Set.mem_setOf_eq] at hnbhd
      rcases hUmem with ⟨hAsub, hcl⟩
      by_contra hxU
      rw [Closed] at hcl
      specialize hnbhd Uᶜ ⟨hcl, Set.mem_compl hxU⟩
      rw [←Set.nonempty_iff_ne_empty, Set.nonempty_def] at hnbhd
      rcases hnbhd with ⟨y, hymemA, _⟩
      specialize hAsub hymemA
      contradiction

theorem in_closure_iff_filter_conv
  {X : Type*} [Topology X]
  (A : Set X)
  (x : X)
  : x ∈ closure A ↔ ∃ G : Filter X, G lim x ∧ A ∈ G ∧ ∅ ∉ G
:= by
  constructor
  · intro hcl
    have foo := (in_closure_iff_nbhd_inter A x).mp hcl
    choose U hUmem using foo


  · intro hex
end Convergence

-- TODO use different nbhd definition, note it
