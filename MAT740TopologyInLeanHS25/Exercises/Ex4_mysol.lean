import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.ContinuousFunctions

universe u v
variable {X : Type u} {Y : Type v} (f : X → Y) (g : Y → X)

lemma l1 (inv_fg : InverseFun f g) (x : X) : g (f x) = x := by
  have hcomp := inv_fg.2
  apply_fun (fun h => h x) at hcomp
  rw [Function.comp_apply, id_eq] at hcomp
  exact hcomp

lemma l2 (inv_fg : InverseFun f g) (y : Y) : f (g y) = y := by
  have hcomp := inv_fg.1
  apply_fun (fun h => h y) at hcomp
  rw [Function.comp_apply, id_eq] at hcomp
  exact hcomp

lemma image_eq_preimage_InverseFun (inv_fg : InverseFun f g) (U : Set X) : f '' U = g ⁻¹' U := by
  ext y
  constructor
  · rintro ⟨x, hxU, hy⟩
    rw [Set.mem_preimage, ←hy]
    rw [l1 f g inv_fg x]
    exact hxU
  · intro hy
    rw [Set.mem_preimage] at hy
    rw [InverseFun] at inv_fg
    rw [Set.mem_image]
    use g y
    constructor
    · exact hy
    · exact l2 f g inv_fg y

variable [Topology X] [Topology Y]

example : HomeoMap f → OpenMap f := by
  rintro ⟨_, g, ⟨hcontg, inv_fg⟩⟩ U hoU
  rw [image_eq_preimage_InverseFun f g inv_fg U]
  exact hcontg U hoU

example (inv_fg : InverseFun f g) (cont_f : Cont f) : OpenMap f → HomeoMap f := by
  intro hmo
  constructor
  · intro U hoU
    exact cont_f U hoU
  · use g
    constructor
    · intro U hoU
      rw [←image_eq_preimage_InverseFun f g inv_fg U]
      exact hmo U hoU
    · exact inv_fg

example (bij_f : Function.Bijective f) : OpenMap f ↔ ClosedMap f := by
  constructor
  · intro hU U hclU
    have hocl := hU (Uᶜ) hclU
    rw [Set.image_compl_eq bij_f] at hocl
    exact hocl
  · intro hmc U hoU
    rw [←compl_compl U] at hoU
    have hocl := hmc Uᶜ hoU
    rw [Closed, Set.image_compl_eq bij_f, compl_compl] at hocl
    exact hocl
