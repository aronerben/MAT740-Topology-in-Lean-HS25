import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.ContinuousFunctions

universe u v
variable {X : Type u} {Y : Type v} [Topology X] [Topology Y]

/-
NOTE:
Exercise marked with
**************
are the mandatory ones mentioned on the sheet.
-/

-- **************
theorem Cont_preimage_Closed_iff (f : X → Y) : Cont f ↔ (∀ s, Closed s → Closed (f ⁻¹' s)) := by
  constructor
  · intro h_cont s h_closed
    exact h_cont (sᶜ) h_closed
  · intro h_preimage s h_open
    rw [←compl_compl s] at h_open
    specialize h_preimage (sᶜ) h_open
    simp only [Set.preimage_compl] at h_preimage
    rw [Closed, compl_compl] at h_preimage
    exact h_preimage
