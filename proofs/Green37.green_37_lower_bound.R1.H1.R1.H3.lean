import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1
import Mathlib.NumberTheory.Bertrand

-- Green 37, reduction step H3: the AP-cover minimum is monotone in the largest
-- difference, and every N ≥ 2 has a prime in the upper half of {1, …, N}.

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1_H1_R1.H3 := by
  constructor
  · intro N₁ N₂ k hN
    have hsub :
        {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N₂ k} ⊆
        {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N₁ k} := by
      rintro m ⟨A, hcard, hcov⟩
      refine ⟨A, hcard, ?_⟩
      intro d hd
      exact hcov d ⟨hd.1, hd.2.trans hN⟩
    have hne :
        {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N₂ k}.Nonempty := by
      refine ⟨k * N₂ + 1, Finset.range (k * N₂ + 1), Finset.card_range _, ?_⟩
      intro d hd
      refine ⟨0, ((Finset.range k).image (fun i ↦ i * d) : Set ℕ), ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
        exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
      · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
          Finset.card_image_of_injective _
            (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd.1 h), Finset.card_range]
      · ext x; simp
    simpa [Green37.m] using csInf_le_csInf' hne hsub
  · intro N hN
    have hn : (N + 1) / 2 ≠ 0 := by omega
    obtain ⟨p, hp, hlt, hle⟩ :=
      Nat.exists_prime_lt_and_le_two_mul ((N + 1) / 2) hn
    refine ⟨p, hp, ?_, ?_⟩
    · have hlt' : (N + 1) / 2 + 1 ≤ p := Nat.succ_le_of_lt hlt
      have hNle : N ≤ 2 * ((N + 1) / 2) + 1 := by omega
      have h2p : 2 * ((N + 1) / 2) + 2 ≤ 2 * p := by
        have : 2 * (((N + 1) / 2) + 1) ≤ 2 * p := Nat.mul_le_mul_left 2 hlt'
        simpa [Nat.mul_add, Nat.mul_one] using this
      omega
    · by_cases hEven : Even N
      · obtain ⟨t, ht⟩ := hEven
        have : 2 * ((N + 1) / 2) = N := by omega
        omega
      · have hodd : Odd N := Nat.not_even_iff_odd.mp hEven
        obtain ⟨t, rfl⟩ := hodd
        have hup : 2 * ((2 * t + 1 + 1) / 2) = 2 * t + 2 := by omega
        have hp1 : p ≤ 2 * t + 2 := by simpa [hup] using hle
        have hne : p ≠ 2 * t + 2 := by
          intro heq
          have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left (by
            intro hp2
            have : 2 * t + 2 = 2 := heq.symm.trans hp2
            omega)
          rw [heq] at hpodd
          obtain ⟨s, hs⟩ := hpodd
          omega
        omega
