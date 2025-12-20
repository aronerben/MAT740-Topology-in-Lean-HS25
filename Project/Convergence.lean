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
  rcases hU with ⟨_, _, hmem, hsub⟩
  exact hsub hmem

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
      use Aᶜ
    · trivial
  · intro hnbhd
    choose U hU using hnbhd
    -- Pick out opens
    choose V hV using fun x hx => (hU x hx).1
    have compl_eq
      -- Double union
      : Aᶜ = (⋃ (x : X) (hx : x ∈ Aᶜ), V x hx)
    := by
      ext x
      constructor
      · intro hmem
        specialize hV x hmem
        simp_rw [Set.mem_compl_iff, Set.mem_iUnion]
        use x, hmem
        exact hV.2.1
      · intro h
        simp_rw [Set.mem_iUnion] at h
        rcases h with ⟨z, hz, hzmem⟩
        specialize hV z hz
        specialize hU z hz
        exact hU.2 (hV.2.2 hzmem)
    rw [Closed, compl_eq]
    apply Open_iUnion
    intro x
    apply Open_sUnion
    intro W hmemrange
    simp only [Set.mem_range, Set.mem_compl_iff] at hmemrange
    rcases hmemrange with ⟨hnmem, heq⟩
    rw [←heq]
    exact (hV x hnmem).1

structure FilterBase (X : Type*) where
  Sets : Set (Set X)
  nonempty_Sets : Sets ≠ ∅
  inter_Sets {A B} : A ∈ Sets → B ∈ Sets → ∃ C ∈ Sets, C ⊆ A ∩ B

-- Can this just be derived via Filter instance using some coercion?
instance instMembership
  {X : Type*}
  : Membership (Set X) (FilterBase X) where
  mem := fun F U ↦ U ∈ F.Sets

def upwardClosure
  {X : Type*}
  (B : Set (Set X))
  : Set (Set X) :=
  {C | ∃ A ∈ B, A ⊆ C}

def generateFilterFromFilterBase
  {X : Type*}
  (B : FilterBase X)
  : Filter X :=
  {
    Sets := upwardClosure B.Sets
    nonempty_Sets := by
      intro heq
      rw [upwardClosure] at heq
      have hmem := B.nonempty_Sets
      rw [←Set.nonempty_iff_ne_empty, Set.nonempty_def] at hmem
      rcases hmem with ⟨A, hAmem⟩
      rw [Set.eq_empty_iff_forall_notMem] at heq
      specialize heq A
      simp only [Set.mem_setOf_eq, not_exists, not_and] at heq
      specialize heq A hAmem (by exact subset_refl A)
      exact heq
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

lemma closure_closed
  {X : Type*} [Topology X]
  (A : Set X)
  : Closed (closure A)
:= by
  rw [closure, Closed, Set.compl_sInter]
  apply Open_sUnion
  intro B hmem
  simp only [Closed, Set.mem_image, Set.mem_setOf_eq] at hmem
  rcases hmem with ⟨C, ⟨_, hopen⟩, heq⟩
  rw [←heq]
  exact hopen

lemma subset_self_closure
  {X : Type*} [Topology X]
  (A : Set X)
  : A ⊆ closure A
:= by
  intro x hx
  rw [closure]
  simp_rw [Set.mem_sInter, Set.mem_setOf_eq]
  intro B hBmem
  rcases hBmem with ⟨hsub, _⟩
  exact hsub hx

-- x ∈ Abar if and only if every neighborhood of x nontrivially intersects A
lemma in_closure_iff_nbhd_inter
  {X : Type*} [Topology X]
  (A : Set X)
  (x : X)
  : x ∈ closure A ↔ ∀ U ∈ neighborhoods x, (A ∩ U) ≠ ∅
:= by
  constructor
  · contrapose
    intro hnnbhd hcl
    -- TODO THIS IS THE PROBLEM
    push_neg at hnnbhd
    rcases hnnbhd with ⟨U, hUmem, heq⟩
    rcases hUmem with ⟨V, hVopen, hVmem, hVsub⟩
    rw [inter_empty_iff_subset_compl] at heq
    simp only [closure, Set.mem_sInter, Set.mem_setOf_eq, and_imp] at hcl
    rw [←Set.compl_subset_compl] at hVsub
    specialize hcl Vᶜ (Set.Subset.trans heq hVsub)
      (by simp only [Closed, compl_compl, hVopen])
    exact hcl hVmem
  · contrapose
    intro hncl
    -- TODO THIS IS THE PROBLEM
    push_neg
    use (closure A)ᶜ
    constructor
    · use (closure A)ᶜ
      constructor
      · exact closure_closed A
      · trivial
    · have := Set.disjoint_compl_right_iff_subset.mpr (subset_self_closure A)
      exact Disjoint.inter_eq this

def nbhd_inter_filterbase
  {X : Type*} [Topology X]
  (A : Set X)
  (x : X)
  : FilterBase X
:= {
    Sets := {U ∩ A | U ∈ neighborhoods x}
    nonempty_Sets := by
      intro heq
      rw [Set.eq_empty_iff_forall_notMem] at heq
      simp_rw [Set.mem_setOf_eq, not_exists, not_and, forall_apply_eq_imp_iff₂,
        imp_false] at heq
      specialize heq Set.univ
      rw [neighborhoods] at heq
      simp only [Nbhd, Set.mem_setOf_eq, Set.subset_univ, and_true, not_exists, not_and] at heq
      exact heq Set.univ (Topology.Open_univ) (Set.mem_univ x)
    inter_Sets := by
      rintro C D ⟨U, hUnhbd, heqC⟩ ⟨V, hVnhbd, heqD⟩
      simp only [Set.mem_setOf_eq, Set.subset_inter_iff, exists_exists_and_eq_and]
      use U ∩ V
      constructor
      · simp_rw [neighborhoods, Nbhd, Set.mem_setOf_eq] at *
        rcases hUnhbd with ⟨U', hU'open, hU'mem, hU'sub⟩
        rcases hVnhbd with ⟨V', hV'open, hV'mem, hV'sub⟩
        use U' ∩ V'
        constructor
        · exact Topology.Open_inter U' V' hU'open hV'open
        · constructor
          · rw [Set.mem_inter_iff]
            exact ⟨hU'mem, hV'mem⟩
          · intro y hy
            rw [Set.mem_inter_iff] at hy
            exact ⟨hU'sub hy.1, hV'sub hy.2⟩
      · constructor
        · intro y hy
          simp only [Set.mem_inter_iff] at hy
          rw [←heqC]
          exact Set.mem_inter hy.1.1 hy.2
        · intro y hy
          simp only [Set.mem_inter_iff] at hy
          rw [←heqD]
          exact Set.mem_inter hy.1.2 hy.2
  }

def nbhd_inter_filter
  {X : Type*} [Topology X]
  (A : Set X)
  (x : X)
  : Filter X :=
  generateFilterFromFilterBase (nbhd_inter_filterbase A x)

-- G does not contain empty set
lemma nbhd_inter_filter_proper
  {X : Type*} [Topology X]
  (A : Set X)
  (x : X)
  (hcl : x ∈ closure A)
  : ProperFilter (nbhd_inter_filter A x)
:= by
  intro hemptymem
  rcases hemptymem with ⟨U, hUmem, hUsub⟩
  simp only [Set.subset_empty_iff] at hUsub
  rcases hUmem with ⟨V, hVmem, heq⟩
  rw [hUsub] at heq
  have hinter := (in_closure_iff_nbhd_inter A x).mp hcl
  specialize hinter V hVmem
  rw [Set.inter_comm] at hinter
  contradiction

-- thm 3.9 bradley
theorem in_closure_iff_filter_conv
  {X : Type*} [Topology X]
  (A : Set X)
  (x : X)
  : x ∈ closure A ↔ ∃ G : Filter X, G lim x ∧ A ∈ G ∧ ProperFilter G
:= by
  let B : FilterBase X := nbhd_inter_filterbase A x
  constructor
  · intro hcl
    let G := generateFilterFromFilterBase B
    use G
    constructor
    · intro N hN
      use N ∩ A
      constructor
      · use N
      · exact Set.inter_subset_left
    · constructor
      · use A
        constructor
        · use Set.univ
          constructor
          · simp_rw [neighborhoods, Nbhd, Set.mem_setOf_eq]
            use Set.univ
            exact ⟨Topology.Open_univ, by trivial⟩
          · exact Set.univ_inter A
        · trivial
      · exact nbhd_inter_filter_proper A x hcl
  · intro hex
    rcases hex with ⟨G, hGlimx, ⟨hAmem, hproper⟩⟩
    rw [filter_convergence] at hGlimx
    have hsub : B.Sets ⊆ G.Sets := by
      intro U hUmem
      rcases hUmem with ⟨V, hVnbhd, heq⟩
      specialize hGlimx hVnbhd
      rw [←heq]
      have := G.inter_Sets (hGlimx) (hAmem)
      rcases this with ⟨W, hWmem, hWsub⟩
      exact G.upward_Sets hWmem hWsub
    rw [in_closure_iff_nbhd_inter]
    intro U hUmem heq
    specialize hsub (by use U)
    rw [ProperFilter] at hproper
    rw [Set.inter_comm] at heq
    rw [←heq] at hproper
    contradiction
end Convergence
