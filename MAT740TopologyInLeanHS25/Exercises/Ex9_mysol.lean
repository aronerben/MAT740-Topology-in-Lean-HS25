import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.Connectedness

open MyConnected

variable {X Y : Type*} [Topology X] [Topology Y]

theorem Disconnected_Prop : ¬(Connected Prop) := by
  rw [Connected]
  push_neg
  have cont_id : Cont (id : Prop → Prop) := Cont_id
  have non_const : ∀ b : Prop, ¬(Constant id b) := by
    intros p hconst
    -- If id were constant on Prop, we could have two
    -- contradictory statements assigned to it, here we use True and False
    have hnp := hconst False
    have hp := hconst True
    rw [id] at hnp hp
    rw [←hnp] at hp
    contradiction
  use id

theorem Connected_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f)
  : Connected X → Connected Y := by
    -- We follow Theorem 2.1 in the Bradley book
    intros hconn g hcontg
    contrapose hconn
    push_neg at hconn
    have hfnnotconst : ∀ b : Prop, ¬(Constant (g ∘ f) b)  := by
      intros b hconst
      have hnconstg := hconn b
      rw [Constant] at hconst hnconstg
      push_neg at hnconstg
      obtain ⟨y, hneqg⟩ := hnconstg
      rw [Function.Surjective] at surj_f
      have ⟨x, heqf⟩ := surj_f y
      specialize hconst x
      rw [←heqf] at hneqg
      contradiction
    have hcontfn : Cont (g ∘ f) := by
      apply Cont_comp f g cont_f hcontg
    intro hconnX
    rw [Connected] at hconnX
    have ⟨b, hconst⟩ := hconnX (g ∘ f) hcontfn
    exact hfnnotconst b hconst


theorem PathConnected_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f)
  : PathConnected X → PathConnected Y := by
    -- We follow Theorem 2.1 in the Bradley book
    intros hpathconn y1 y2
    rw [PathConnected] at hpathconn
    obtain ⟨x1, heqf1⟩ := surj_f y1
    obtain ⟨x2, heqf2⟩ := surj_f y2
    have hpathx := Classical.choice (hpathconn x1 x2)
    have hcontcomp : Cont (f ∘ hpathx.p) := by
      apply Cont_comp hpathx.p f hpathx.Cont_p cont_f
    have hpathy : MyConnected.Path y1 y2 := by
      constructor
      · exact hcontcomp
      · rw [Function.comp_apply, hpathx.source]
        exact heqf1
      · rw [Function.comp_apply, hpathx.target]
        exact heqf2
    constructor
    · exact hpathy
