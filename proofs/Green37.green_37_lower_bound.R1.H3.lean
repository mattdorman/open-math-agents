import OMAReductions.R_Green37_green_37_lower_bound_R1
import Mathlib.Order.Lattice.Nat

/-!
Length one forces a nonempty cover. Length two realizes each difference from 1
to N by a strictly ordered pair, and a set of size m has m(m - 1)/2 such pairs.
-/

open Finset

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H3 := by
  constructor
  · intro N hN
    have hone :
        {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N 1}.Nonempty := by
      refine ⟨1, {0}, by simp, ?_⟩
      intro d hd
      refine ⟨0, ({0} : Set ℕ), by simp, ?_⟩
      simp [Set.IsAPOfLengthWith.one]
    have hpos : ∀ m ∈ {m | ∃ A : Finset ℕ, A.card = m ∧
        Green37.IsAPCover (A : Set ℕ) N 1}, 1 ≤ m := by
      rintro m ⟨A, rfl, hcov⟩
      obtain ⟨a, s, hsA, hs⟩ := hcov 1 ⟨by omega, hN⟩
      have ha : a ∈ s := by
        rw [hs.2]
        refine ⟨0, by simp, ?_⟩
        simp [zero_nsmul]
      have hmem : a ∈ A := by simpa using hsA ha
      exact Finset.card_pos.mpr ⟨a, hmem⟩
    have hmem := Nat.sInf_mem hone
    have hle : 1 ≤ sInf {m | ∃ A : Finset ℕ, A.card = m ∧
        Green37.IsAPCover (A : Set ℕ) N 1} := hpos _ hmem
    simpa [Green37.m] using hle
  · intro N
    let S := {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N 2}
    have hne : S.Nonempty := by
      refine ⟨2 * N + 1, range (2 * N + 1), card_range _, ?_⟩
      intro d hd
      refine ⟨0, ((range 2).image (fun i ↦ i * d) : Set ℕ), ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
        simp only [mem_coe, mem_range] at hi ⊢
        exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
      · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
          card_image_of_injective _
            (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd.1 h),
          card_range]
      · ext x
        simp [Finset.mem_coe, Finset.mem_image, Finset.mem_range, nsmul_eq_mul]
    obtain ⟨A, hcard, hcov⟩ := Nat.sInf_mem hne
    have hA : A.card = Green37.m N 2 := by
      simpa [Green37.m, S] using hcard
    classical
    have hw (d : ℕ) (hd : d ∈ Icc 1 N) : ∃ a ∈ A, a + d ∈ A := by
      obtain ⟨a, s, hsA, hs⟩ := hcov d (mem_Icc.mp hd)
      have ha : a ∈ s := by
        rw [hs.2]
        refine ⟨0, by simp, ?_⟩
        simp [zero_nsmul]
      have had : a + d ∈ s := by
        rw [hs.2]
        refine ⟨1, by simp, ?_⟩
        simp [one_nsmul]
      exact ⟨a, by simpa using hsA ha, by simpa using hsA had⟩
    let aOf (d : ℕ) (hd : d ∈ Icc 1 N) : ℕ := Classical.choose (hw d hd)
    have haOf (d : ℕ) (hd : d ∈ Icc 1 N) : aOf d hd ∈ A ∧ aOf d hd + d ∈ A :=
      Classical.choose_spec (hw d hd)
    let lo := {p ∈ A.product A | p.1 < p.2}
    have hlo : lo.card = A.card.choose 2 := Finset.card_product_filter_lt
    let f (d : ℕ) : ℕ × ℕ :=
      if hd : d ∈ Icc 1 N then (aOf d hd, aOf d hd + d) else (0, 0)
    have hf : ∀ d ∈ Icc 1 N, f d ∈ lo := by
      intro d hd
      have hlt : aOf d hd < aOf d hd + d := by
        have : 1 ≤ d := (mem_Icc.mp hd).1
        omega
      have hdI : 1 ≤ d ∧ d ≤ N := mem_Icc.mp hd
      have : f d = (aOf d hd, aOf d hd + d) := by simp [f, dif_pos hdI]
      rw [this]
      exact mem_filter.mpr ⟨mem_product.mpr ⟨(haOf d hd).1, (haOf d hd).2⟩, hlt⟩
    have hinj : Set.InjOn f (Icc 1 N : Set ℕ) := by
      intro d hd e he hfe
      have hd' : d ∈ Icc 1 N := by simpa using hd
      have he' : e ∈ Icc 1 N := by simpa using he
      have hdI : 1 ≤ d ∧ d ≤ N := mem_Icc.mp hd'
      have heI : 1 ≤ e ∧ e ≤ N := mem_Icc.mp he'
      have hfe' : (aOf d hd', aOf d hd' + d) = (aOf e he', aOf e he' + e) := by
        rw [show f d = (aOf d hd', aOf d hd' + d) by simp [f, dif_pos hdI],
          show f e = (aOf e he', aOf e he' + e) by simp [f, dif_pos heI]] at hfe
        exact hfe
      obtain ⟨h1, h2⟩ := Prod.mk.inj hfe'
      omega
    have hN : N ≤ lo.card := by
      have hcardI : (Icc 1 N).card = N := by simp
      rw [← hcardI]
      exact card_le_card_of_injOn f hf hinj
    have htwo : 2 * A.card.choose 2 = A.card * (A.card - 1) := by
      rw [Nat.choose_two_right]
      exact Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_pred_self A.card))
    have hmul : 2 * N ≤ 2 * lo.card := Nat.mul_le_mul_left 2 hN
    rw [hlo, htwo, hA] at hmul
    exact hmul
