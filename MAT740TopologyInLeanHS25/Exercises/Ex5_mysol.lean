import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.Bases

universe u v
variable {X : Type u} {Y : Type v}

/- # Problem 1 (4 points) -/
section Problem1
variable [Topology X] [BY : Basis Y]

theorem Cont_Basics' (f : X → Y) : Cont f ↔ ∀ b ∈ BY.Basics, Open (f ⁻¹' b) := by
  /-
    (=>) use `Open_Basics`
    (<=) use `IsBasis_basisTopology` to decompose open U into union of basis element.
    Then use properties of preimages `Set.preimage_sUnion` and `Set.sUnion_image`.
  -/
  constructor
  · intro hcont U hUmem
    have hUopen := Open_Basics U hUmem
    exact hcont U hUopen
  · intro h U hUopen
    obtain ⟨hbopen, hUcover⟩ : IsBasis := @IsBasis_basisTopology Y BY
    specialize hUcover U hUopen
    rcases hUcover with ⟨C, hCsub, hUsUnion⟩
    rw [hUsUnion, Set.preimage_sUnion]
    apply Open_sUnion
    intro b hbmem
    rw [Set.mem_range] at hbmem
    rcases hbmem with ⟨bx, heq⟩
    rw [←heq]
    apply Open_sUnion
    intro a hmema
    -- Ugly repetition of the above...
    -- Can probably be golfed quite a bit
    rw [Set.mem_range] at hmema
    rcases hmema with ⟨hbxmem, heq⟩
    rw [←heq]
    have hbxmem : bx ∈ BY.Basics := by
      apply hCsub
      exact hbxmem
    specialize h bx hbxmem
    exact h


end Problem1

/- # Problem 2 (6 points) -/
section Problem2
open Metric
variable [MetricSpace X]


/- (a) (3 points) -/
theorem ball_in_ball' {x : X} {ε : ℝ} : ∀ y ∈ ball x ε, ∃ δ, (0 < δ ∧ ball y δ ⊆ ball x ε) := by
  intro y hy
  use ε - dist x y
  constructor
  · rw [mem_ball] at hy
    rw [sub_pos, dist_comm]
    exact hy
  · intro z hz
    rw [mem_ball] at *
    rw [dist_comm] at *
    have triineq := dist_triangle x y z
    linarith
  /-
  use `linarith` and `dist_triangle`
  -/

/- (b) (3 points) -/
instance metricBasis' : Basis X where
  Basics := {B | ∃ x ε, B = ball x ε}
  Basis_cover := by
    rw [Set.sUnion_eq_univ_iff]
    intro x
    use ball x 1
    constructor
    · use x, 1
    · rw [mem_ball]
      rw [dist_self]
      linarith
    /-
    Prove this!
    use `simp?` here to get a short proof
    -/
  Basis_inter := by
    /- No need to prove this! -/
    sorry

end Problem2
