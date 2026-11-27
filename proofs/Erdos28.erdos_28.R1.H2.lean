import OMAReductions.R_Erdos28_erdos_28_R1

/-!
An ordered pair summing to n uses the new element in the first coordinate, the
second coordinate, or both. Those are at most two pairs on the antidiagonal.
-/

open AdditiveCombinatorics Finset

theorem OMA.solution : OMA.R_Erdos28_erdos_28_R1.H2 := by
  intro A a n
  classical
  rw [sumRep_def, sumRep_def]
  let old := (antidiagonal n).filter fun p => p.1 ∈ A ∧ p.2 ∈ A
  let extra := (antidiagonal n).filter fun p => p.1 = a ∨ p.2 = a
  let new := (antidiagonal n).filter fun p => p.1 ∈ insert a A ∧ p.2 ∈ insert a A
  have hsub : new ⊆ old ∪ extra := by
    intro p hp
    obtain ⟨hmem, hp1, hp2⟩ := mem_filter.mp hp
    by_cases hboth : p.1 ∈ A ∧ p.2 ∈ A
    · exact mem_union_left _ (mem_filter.mpr ⟨hmem, hboth⟩)
    · refine mem_union_right _ (mem_filter.mpr ⟨hmem, ?_⟩)
      rcases Set.mem_insert_iff.mp hp1 with h1 | h1A
      · exact Or.inl h1
      rcases Set.mem_insert_iff.mp hp2 with h2 | h2A
      · exact Or.inr h2
      · exact (hboth ⟨h1A, h2A⟩).elim
  have hextra : extra.card ≤ 2 := by
    by_cases han : a ≤ n
    · have hfew : extra ⊆ ({(a, n - a), (n - a, a)} : Finset (ℕ × ℕ)) := by
        intro p hp
        obtain ⟨hmem, hor⟩ := mem_filter.mp hp
        have hsum : p.1 + p.2 = n := mem_antidiagonal.mp hmem
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases hor with h1 | h2
        · have h2' : p.2 = n - a := by omega
          left
          obtain ⟨x, y⟩ := p
          dsimp at h1 h2'
          subst h1
          subst h2'
          rfl
        · have h1' : p.1 = n - a := by omega
          right
          obtain ⟨x, y⟩ := p
          dsimp at h1' h2
          subst h1'
          subst h2
          rfl
      have htwo : ({(a, n - a), (n - a, a)} : Finset (ℕ × ℕ)).card ≤ 2 := by
        simpa using (card_insert_le (a, n - a) ({(n - a, a)} : Finset (ℕ × ℕ))).trans
          (by simp)
      exact (card_le_card hfew).trans htwo
    · have hempty : extra = ∅ := by
        ext p
        constructor
        · intro hp
          obtain ⟨hmem, hor⟩ := mem_filter.mp hp
          have hsum : p.1 + p.2 = n := mem_antidiagonal.mp hmem
          rcases hor with h1 | h2
          · omega
          · omega
        · simp
      simp [hempty]
  have hcard : new.card ≤ old.card + extra.card :=
    (card_le_card hsub).trans (card_union_le _ _)
  have : new.card ≤ old.card + 2 := by omega
  simpa [new, old] using this
