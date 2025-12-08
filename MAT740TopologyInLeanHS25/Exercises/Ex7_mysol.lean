import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.NewSpaces

section Ex1
variable (I : Type) (J : I → Type) (P : (i : I) → J i → Prop)

theorem dist_quant : (∀ i, ∃ j : J i, P i j) ↔ (∃ c : (i : I) → J i, ∀ i, P i (c i)) := by
  constructor
  · intro h
    choose f hf using h
    use f
  · rintro ⟨a, b⟩ i
    use a i
    exact b i

end Ex1

section Ex2
universe u
open Constructions
instance Coproduct_coproductTopology (X : Type u) [TX : Topology X] (Y : Type u) [TY : Topology Y]
  : CoproductSpace X Y where
  TC := coproductTopology X Y
  char_Coproduct := by
    intro T TT f
    constructor
    case mp =>
      intros h
      let TC := coproductTopology X Y
      constructor
      · intro U hU
        simp only [Cont] at *
        rw [Set.preimage_comp]
        have hinlCont : Cont (@Sum.inl X Y) := by
          intros S hS
          rcases hS with ⟨l, r⟩
          exact l
        apply hinlCont
        exact h U hU
      · intro V hV
        simp only [Cont] at *
        rw [Set.preimage_comp]
        have hinrCont : Cont (@Sum.inr X Y) := by
          intros S hS
          rcases hS with ⟨l, r⟩
          exact r
        apply hinrCont
        exact h V hV
    case mpr =>
      rintro ⟨hl, hr⟩ U hU
      exact ⟨hl U hU, hr U hU⟩


end Ex2

section Bonus
variable (I : Type*) (J : I → Type*) (X : (i : I) → J i → Type*)

instance dist_type : (Π i, Σ j : J i, X i j) ≃ (Σ c : (i : I) → J i, Π i, X i (c i)) where
  toFun := fun f => ⟨fun i => (f i).1, fun i => (f i).2⟩
  invFun := fun g => fun i => ⟨g.1 i, g.2 i⟩
  left_inv := by
    intro f
    rfl
  right_inv := by
    intro g
    rfl

end Bonus
