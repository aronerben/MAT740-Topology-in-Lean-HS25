import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.NewSpaces

universe u
variable {X : Type u} [TX : Topology X]

open Constructions

instance Subspace_pullbackTopology' {S : Type u} (incl : S → X) (inj : Function.Injective incl)
  : Subspace X where
    S := S
    TS := pullbackTopology X TX S incl
    incl := incl
    Injective_incl := inj
    char_Subspace := by
      let TS := pullbackTopology X TX S incl
      intros T TT m
      constructor
      -- Couldn't get it to work with Cont_comp, though it would've been nicer
      · intros hcontm U hopenU
        have hopenS : TS.Open (incl ⁻¹' U) := ⟨U, hopenU, rfl⟩
        exact hcontm (incl ⁻¹' U) hopenS
      · rintro hcont U ⟨V, hopenV, heqV⟩
        rw [heqV]
        exact hcont V hopenV

theorem Cont_qmap' [quot : Quotient X] : @Cont X quot.Q TX quot.TQ quot.qmap := by
  intros U hopenU
  have hquot := quot.char_Quotient quot.TQ id
  have hcont : @Cont quot.Q quot.Q quot.TQ quot.TQ id := by
    intros _ hopenV
    exact hopenV
  exact hquot.mp hcont U hopenU

/- The quotient topology is the largest (finest) topology on Q that makes `qmap` continuous. -/
theorem final_Quotient' [quot : Quotient X] [TQ' : Topology quot.Q] :
  @Cont X quot.Q TX TQ' quot.qmap → TQ' ≤ quot.TQ := by
  intro h
  rw [Coarser, quot.char_Quotient, Function.id_comp]
  exact h

instance pushforwardTopology'
  (X : Type u) (TX : Topology X) (Q : Type u) (qmap : X → Q)
  : Topology Q where
    Open := fun (U : Set Q) ↦ Open (qmap ⁻¹' U)
    Open_univ := by
      rw [Set.preimage_univ]
      exact TX.Open_univ
    Open_inter := by
      intros U V hpreopenU hpreopenV
      exact TX.Open_inter (qmap ⁻¹' U) (qmap ⁻¹' V) hpreopenU hpreopenV
    Open_sUnion := by
      intros PS hopen
      rw [Set.preimage_sUnion]
      exact Open_preimageUnion hopen

instance Quotient_pushforwardTopology'
  {Q : Type u} (qmap : X → Q) (surj : Function.Surjective qmap)
  : Quotient X where
    Q := Q
    TQ := pushforwardTopology X TX Q qmap
    qmap := qmap
    Surjective_qmap := surj
    char_Quotient := by
      let TQ := pushforwardTopology X TX Q qmap
      intros T TT m
      constructor
      · intros hcontm U hopenU
        simp at hcontm
        have hqmapcont : Cont qmap := by
          intros V hopenV
          have _ : TQ.Open V := by
            exact hopenV
          assumption
        exact hqmapcont (m ⁻¹' U) (hcontm U hopenU)
      · rintro hcont U hopenU
        exact hcont U hopenU
