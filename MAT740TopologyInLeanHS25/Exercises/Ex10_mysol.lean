import Mathlib.Tactic

import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.ContinuousFunctions

universe u

structure openCover (I : Type u) (X : Type u) [Topology X] where
  Cover : I → Set X
  Open_cover : ∀ i, Open (Cover i)
  Is_cover : (⋃ i, Cover i) = Set.univ

def subCover {I J : Type u} {X : Type u} [Topology X] (s : I → J) (C : openCover J X) : Prop :=
  Function.Injective s ∧
  (⋃ i : I, C.Cover (s i)) = Set.univ

def Compact (X : Type u) [Topology X] : Prop
  := ∀ (I : Type u) (C : openCover I X), ∃ (N : Type u) (s : N → I), Finite N ∧ subCover s C

variable {X Y : Type u} [Topology X] [Topology Y]

def pullbackCover {I : Type u} (f : X → Y) (cont_f : Cont f) (C : openCover I Y)
  : openCover I X where
  Cover := fun i ↦ f ⁻¹' (C.Cover i)
  Open_cover := by
    intro i
    exact cont_f (C.Cover i) (C.Open_cover i)
  Is_cover := by
    rw [←Set.preimage_iUnion]
    rw [C.Is_cover]
    exact Set.preimage_univ

theorem Compact_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f) :
  Compact X → Compact Y := by
  intro hcomp I cover
  let hpullback := pullbackCover f cont_f cover
  obtain ⟨N, s, hfin, hsubcov⟩ := hcomp I hpullback
  use N, s
  constructor
  · exact hfin
  · constructor
    · exact hsubcov.1
    · have hsub := hsubcov.2
      rw [subCover] at hsubcov
      apply_fun (fun S ↦ f '' S) at hsub
      rw [Set.image_iUnion,
          Set.image_univ_of_surjective surj_f] at hsub
      -- Lean seems to struggle to see this equality when rewriting
      have heq : ⋃ i, f '' (f ⁻¹' cover.Cover (s i)) = ⋃ i, f '' hpullback.Cover (s i) := by
        rfl
      simp_rw [Set.image_preimage_eq _ surj_f] at heq
      rw [heq]
      exact hsub
