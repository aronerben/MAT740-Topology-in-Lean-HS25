import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.Filters

open MyFilter

variable {X Y : Type*} {A B : Set X}

section Ex1

lemma max_tail' {s : ℕ → X} {nA nB : ℕ}
(hn : tail s nA ⊆ A) (hm : tail s nB ⊆ B)
: tail s (max nA nB) ⊆ A ∩ B := by
  rw [Set.subset_inter_iff]
  constructor
  · intro x ⟨m, hmge, hms⟩
    have hmgeq : m ≥ nA := by
      have hnAleq : nA ≤ max nA nB := by
        apply Nat.le_max_left
      rw [@ge_iff_le]
      rw [@ge_iff_le] at hmge
      apply Nat.le_trans hnAleq hmge
    exact hn ⟨m, hmgeq, hms⟩
  · intro x ⟨m, hmge, hms⟩
    have hmgeq : m ≥ nB := by
      have hnBleq : nB ≤ max nA nB := by
        apply Nat.le_max_right
      rw [@ge_iff_le]
      rw [@ge_iff_le] at hmge
      apply Nat.le_trans hnBleq hmge
    exact hm ⟨m, hmgeq, hms⟩

def eventuality' (s : ℕ → X) : MyFilter.Filter X where
  Sets := {A | ∃ n, tail s n ⊆ A}
  /- exercise -/
  univ_Sets := by
    use 0
    intros x hx
    exact Set.mem_univ x
  upward_Sets := by
    rintro A B ⟨n, hn⟩ hAB
    use n
    intro x hx
    apply hAB
    exact hn hx
  inter_Sets := by
    rintro A B ⟨nA, hnA⟩ ⟨nB, hnB⟩
    use max nA nB
    intro x hx
    apply max_tail'
    · exact hnA
    · exact hnB
    · exact hx

end Ex1

section Ex2

theorem Cont_convergence' [Topology X] [Topology X] (f : X → Y)
  : Cont f ↔ ∀ (G : MyFilter.Filter X) (x : X), G lim x → (mapFilter f G) lim (f x) := by
    constructor
    case mp => sorry -- no need to fill this in
    case mpr =>
      intro h U open_U
      have g : ∀ x ∈ f ⁻¹' U, ∃ V, Nbhd V x ∧ V ⊆ f ⁻¹' U := by
        intro x hx
        let F := NbhdFilter x
        have hF : F lim x := by
          intro V hV
          simp only [Set.mem_preimage, mem_sets] at *
          rw [neighborhoods] at hV
          exact ⟨V, ⟨hV, by trivial⟩⟩
        have ⟨V, hV⟩ : f ⁻¹' U ∈ F := by
          have maplim := h F x hF
          have hnbd : U ∈ neighborhoods (f x) := by
            constructor
            · exact open_U
            · trivial
          exact maplim hnbd
        use V
      choose V g using g
      have union_fU : f ⁻¹' U = ⋃₀ {B | ∃ (x : X) (w : x ∈ f ⁻¹' U), B = V x w} := by
        ext x
        constructor
        · intro hx
          use V x hx
          constructor
          · use x
            use hx
          · exact (g x hx).1.2
        · intro hx
          simp only [Set.mem_preimage, Set.mem_sUnion, Set.mem_setOf_eq] at hx
          rcases hx with ⟨W, ⟨y, wy, hW_eq⟩, hxmem⟩
          rw [hW_eq] at hxmem
          exact (g y wy).2 hxmem
      rw [union_fU]
      apply Open_sUnion
      intro W hW
      obtain ⟨x,wx,hx⟩ := hW
      specialize g x wx
      rw [hx]
      exact g.1.1

end Ex2
