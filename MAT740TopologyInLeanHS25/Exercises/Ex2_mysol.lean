import Mathlib.Tactic

variable {α : Type} (A B C : Set α)

/-
NOTE:
Exercise marked with
**************
are the mandatory ones mentioned on the sheet.
-/


-- # Set identities

-- ## Boolean algebra
-- Idempotence
example : A ∪ A = A := by
  ext x
  constructor
  · intro h
    rcases h with (h | h)
    · exact h
    · exact h
  · intro h
    left
    exact h

example : A ∩ A = A := by
  ext x
  constructor
  · intro h
    exact h.left
  · intro h
    exact ⟨h, h⟩

-- Identity
example : A ∩ ∅ = ∅ := by
  ext x
  constructor
  · intro h
    exact h.right
  · intro h
    contradiction

example : A ∪ Set.univ = Set.univ := by
  ext x
  constructor
  · intro h
    trivial
  · intro h
    right
    trivial

-- Commutativity
example : A ∩ B = B ∩ A := by
  ext x
  constructor
  · intro h
    exact ⟨h.right, h.left⟩
  · intro h
    exact ⟨h.right, h.left⟩

example : A ∪ B = B ∪ A := by
  ext x
  constructor
  · intro h
    rcases h with (a | b)
    · right
      exact a
    · left
      exact b
  · intro h
    rcases h with (a | b)
    · right
      exact a
    · left
      exact b

-- Associativity
example : A ∩ (B ∩ C) = (A ∩ B) ∩ C := by
  ext x
  constructor
  · intro h
    exact ⟨⟨h.left, h.right.left⟩, h.right.right⟩
  · intro h
    exact ⟨h.left.left, ⟨h.left.right, h.right⟩⟩
example : A ∪ (B ∪ C) = (A ∪ B) ∪ C := by
  ext x
  constructor
  · intro h
    rcases h with (a | (b | c))
    · left
      left
      exact a
    · left
      right
      exact b
    · right
      exact c
  · intro h
    rcases h with ((a | b) | c)
    · left
      exact a
    · right
      left
      exact b
    · right
      right
      exact c

-- Distributivity
example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · intro h
    rcases h with (a | ⟨b, c⟩)
    · exact ⟨Or.inl a, Or.inl a⟩
    · exact ⟨Or.inr b, Or.inr c⟩
  · intro h
    rcases h with ⟨(a | b), (a' | c)⟩
    · left
      exact a
    · left
      exact a
    · left
      exact a'
    · right
      exact ⟨b, c⟩
example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · intro h
    rcases h with ⟨a, (b | c)⟩
    · left
      exact ⟨a, b⟩
    · right
      exact ⟨a, c⟩
  · intro h
    rcases h with (⟨a, b⟩ | ⟨a, c⟩)
    · exact ⟨a, Or.inl b⟩
    · exact ⟨a, Or.inr c⟩

-- DeMorgan
example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  constructor
  · intro h
    constructor
    · intro a
      exact h (Or.inl a)
    · intro b
      exact h (Or.inr b)
  · intro h
    rcases h with ⟨hA, hB⟩
    intro c
    rcases c with (a | b)
    · exact hA a
    · exact hB b
example : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  constructor
  · intro h
    -- Same treatment as non-constructive De'Morgan in prop. logic
    by_cases hA : x ∈ A
    · right
      intro hB
      exact h ⟨hA, hB⟩
    · left
      exact hA
  · intro h
    rcases h with (hA | hB)
    · intro h'
      exact hA h'.left
    · intro h'
      exact hB h'.right

-- ## Empty set
example : A = ∅ ↔ ∀ x : α, ¬(x ∈ A) := by
  constructor
  · intros h x hx
    rw [h] at hx
    contradiction
  · intro h
    ext x
    constructor
    · intro ha
      exact h x ha
    · intro ha
      contradiction
example : A ≠ ∅ ↔ ∃ x, x ∈ A := by
  constructor
  -- This direction needs AoC
  · intro h
    rw [←Set.nonempty_iff_ne_empty] at h
    have _ := Set.Nonempty.some_mem h
    use h.some
  · intro h1 h2
    rw [h2] at h1
    rcases h1 with ⟨x, hx⟩
    contradiction
example : A ∩ B = ∅ ↔ A ⊆ Bᶜ := by
  constructor
  · intros h x hxA hxB
    have h' := h
    rw [Set.eq_empty_iff_forall_notMem] at h'
    exact h' x ⟨hxA, hxB⟩
  · intro h
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxA, hxB⟩
      have _ := h hxA
      contradiction
    · intro hx
      contradiction

-- ## Containment properties
example : A ⊆ B → B ⊆ A → A = B := by
  intros h1 h2
  ext x
  constructor
  · intro ha
    exact h1 ha
  · intro hb
    exact h2 hb
example : A ⊆ B ↔ A ∪ B = B := by
  constructor
  · intro h
    ext x
    constructor
    · intro ha
      rcases ha with (ha | hb)
      · exact h ha
      · exact hb
    · intro hb
      right
      exact hb
  · intros h ha hma
    have hma' : ha ∈ A ∪ B := by
      left
      exact hma
    rw [h] at hma'
    exact hma'
example : A ⊆ B ↔ A ∩ B = A := by
  constructor
  · intro h
    ext x
    constructor
    · intro ha
      exact ha.left
    · intro ha
      have h' := h ha
      exact ⟨ha, h'⟩
  · intros h ha hb
    rw [←h] at hb
    exact hb.right
example : A ⊆ B → B ⊆ C → A ⊆ C := by
  intros h1 h2 a ha
  exact h2 (h1 ha)
example : A ⊆ B ∧ A ⊆ C → A ⊆ B ∩ C := by
  intro h a ha
  rcases h with ⟨h1, h2⟩
  exact ⟨h1 ha, h2 ha⟩
example : A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C := by
  intros h x hx
  rcases hx with (ha | hb)
  · exact h.left ha
  · exact h.right hb
example {F G : Set (Set α)} (h : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x hx
  rcases hx with ⟨U, hU, hxU⟩
  use U
  constructor
  · exact h hU
  · exact hxU
example {F G : Set (Set α)} (h : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x hx
  intro U hU
  have hU' : U ∈ G := by
    exact h hU
  exact hx U hU'

-- # Functions

variable {β : Type} (U V : Set β) (f : α → β)

-- ## Images
-- **************
example (hab : A ⊆ B) : f '' A ⊆ f '' B := by
  intro y hy
  rcases hy with ⟨x, hxA, hy⟩
  use x
  constructor
  · exact hab hxA
  · exact hy
example : f '' (A ∪ B) = (f '' A) ∪ (f '' B) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, hy⟩
    rcases hx with (ha | hb)
    · left
      use x
    · right
      use x
  · intro hy
    rcases hy with (⟨x, ha, hy⟩ | ⟨x, hb, hy⟩)
    · use x
      constructor
      · left
        exact ha
      · exact hy
    · use x
      constructor
      · right
        exact hb
      · exact hy
example : f '' (A  ∩ B) ⊆  (f '' A) ∩  (f '' B) := by
  intro y hy
  rcases hy with ⟨x, hx, hy⟩
  rcases hx with ⟨ha, hb⟩
  constructor
  · use x
  · use x
example {F : Set (Set α)} : f '' ⋃₀ F = ⋃₀ {V : Set β | ∃ U ∈ F, V = f '' U} := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, ⟨U, hU, hxU⟩, hy⟩
    use f '' U
    constructor
    · use U
    · use x
  · intro hy
    rcases hy with ⟨V, ⟨U, hU, rfl⟩, ⟨x, hxU, hy⟩⟩
    use x
    constructor
    · use U
    · exact hy
example {F : Set (Set α)} : f '' ⋂₀ F ⊆ ⋂₀ {V : Set β | ∃ U ∈ F, V = f '' U} := by
  rintro y ⟨x, hxF, hy⟩ V ⟨U, hU, rfl⟩
  use x
  constructor
  · exact hxF U hU
  · exact hy

-- ## Preimages
-- **************
example (huv : U ⊆ V) : f ⁻¹' U ⊆ f ⁻¹' V := by
  intro x hx
  exact huv hx
-- **************
example : f ⁻¹' (U  ∩ V ) = (f ⁻¹' U) ∩ (f ⁻¹' V )  := by
  ext x
  constructor
  · intro h
    exact ⟨h.left, h.right⟩
  · intro h
    exact ⟨h.left, h.right⟩
example :  f ⁻¹' (U  ∪ V ) = (f ⁻¹' U) ∪ (f ⁻¹' V ) := by
  ext x
  constructor
  · intro h
    rcases h with (a | b)
    · left
      exact a
    · right
      exact b
  · intro h
    rcases h with (a | b)
    · left
      exact a
    · right
      exact b
example {F : Set (Set β)} : f ⁻¹' (⋂₀ F ) = ⋂ (V : Set β) (hV: V ∈  F), f ⁻¹' V := by
  ext x
  constructor
  · rintro h V ⟨hV, hxV⟩
    rw [←hxV]
    simp only [Set.mem_iInter, Set.mem_preimage]
    intro hx
    exact h hV hx
  · intros h V hV
    simp only [Set.mem_iInter, Set.mem_preimage] at h
    specialize h V hV
    exact h
example {F : Set (Set β)} : f ⁻¹' (⋂₀ F ) = ⋂₀ { (f ⁻¹' V) | V ∈ F} := by
  ext x
  constructor
  · intros h V hV
    simp only [Set.mem_setOf_eq] at hV
    rcases hV with ⟨hV, ⟨hxV, hP⟩⟩
    rw [←hP]
    simp only [Set.preimage_sInter, Set.mem_iInter, Set.mem_preimage] at h
    simp only [Set.mem_preimage]
    specialize h hV hxV
    exact h
  · intro h
    simp only [Set.mem_sInter, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Set.mem_preimage] at h
    simp only [Set.preimage_sInter, Set.mem_iInter, Set.mem_preimage]
    exact h
example {F : Set (Set β)} : f ⁻¹' (⋃₀ F ) = ⋃ (V : Set β) (hV: V ∈  F), f ⁻¹' V := by
  ext x
  constructor
  · rintro ⟨y, hyF, _⟩
    simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
    use y
  · rintro ⟨U, hU, hx⟩
    simp only [Set.preimage_sUnion, Set.mem_iUnion, Set.mem_preimage, exists_prop]
    simp only [Set.mem_range] at hU
    rcases hU with ⟨y, hyF, _⟩
    simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop] at hx
    use y
example {F : Set (Set β)} : f ⁻¹' (⋃₀ F ) = ⋃₀ {(f ⁻¹' V) | V ∈  F} := by
  ext x
  constructor
  · rintro ⟨y, hyF, hfx⟩
    simp only [Set.mem_sUnion, Set.mem_setOf_eq, exists_exists_and_eq_and, Set.mem_preimage]
    use y
  · rintro ⟨U, hU, hx⟩
    simp only [Set.preimage_sUnion, Set.mem_iUnion, Set.mem_preimage, exists_prop]
    simp only [Set.mem_setOf_eq] at hU
    rcases hU with ⟨y, hyF, hpf⟩
    use y
    constructor
    · exact hyF
    · rw [←hpf] at hx
      exact hx

-- ## Interaction
-- Loop
-- **************
example : f '' (f ⁻¹' V ) ⊆ V := by
  intros y hy
  rcases hy with ⟨x, hx, hy⟩
  rw [←hy]
  exact hx
-- **************
example : A ⊆ f ⁻¹' (f '' A) := by
  intros x hx
  use x

-- Galois connection
-- **************
example : f '' A ⊆ U ↔ A ⊆ f ⁻¹' U := by
  constructor
  · intro h a ha
    apply h
    use a
  · intro h y hy
    rcases hy with ⟨x, hxA, hy⟩
    rw [←hy]
    exact h hxA
