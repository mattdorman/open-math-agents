import OMAReductions.R_Green37_green_37_lower_bound_R1

/-!
A longer arithmetic progression contains its initial segment, so a cover by
progressions of length k2 is a cover by progressions of length k1. The minimum
cardinality therefore grows with the length.
-/

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N k1 k2 hk
  have hsub :
      {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k2} ⊆
      {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k1} := by
    rintro m ⟨A, hcard, hcov⟩
    refine ⟨A, hcard, ?_⟩
    intro d hd
    obtain ⟨a, s, hsA, hs⟩ := hcov d hd
    refine ⟨a, ((Finset.range k1).image fun i ↦ a + i * d : Set ℕ), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hi' : i < k2 := Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) hk
      have hx_s : a + i * d ∈ s := by
        rw [hs.2]
        simp only [Set.mem_setOf_eq, nsmul_eq_mul]
        exact ⟨i, by simpa [Nat.cast_lt] using hi', rfl⟩
      exact hsA hx_s
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_image_of_injective _
          (fun x y hxy ↦ by
            have : x * d = y * d := Nat.add_left_cancel hxy
            exact Nat.eq_of_mul_eq_mul_right hd.1 this),
        Finset.card_range]
    · ext x
      simp [Finset.mem_coe, Finset.mem_image, Finset.mem_range, Nat.cast_lt]
  have hne :
      {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k2}.Nonempty := by
    refine ⟨k2 * N + 1, Finset.range (k2 * N + 1), Finset.card_range _, ?_⟩
    intro d hd
    refine ⟨0, ((Finset.range k2).image (fun i ↦ i * d) : Set ℕ), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
      exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_image_of_injective _
          (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd.1 h),
        Finset.card_range]
    · ext x
      simp
  simpa [Green37.m] using csInf_le_csInf' hne hsub
