import OMAReductions.R_OeisA5258_conjecture_R1
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
When p = n + 1 is prime, the coefficient of x^k in the Apéry polynomial has
p-adic valuation 1 for every 1 ≤ k ≤ n, and the constant term is 1. The
reversed polynomial is therefore Eisenstein at p, and reversal preserves
irreducibility over the rationals.
-/

open Finset Nat Polynomial

namespace AperyPrime

lemma log_lt_two {p k : ℕ} (hp : p.Prime) (hk : k ≤ p - 1) : log p (p - 1 + k) < 2 := by
  have hp2 : 2 ≤ p := hp.two_le
  apply log_lt_of_lt_pow (by omega : p - 1 + k ≠ 0)
  rw [pow_two]
  have hle : p - 1 + k ≤ 2 * p - 2 := by omega
  have hmul : 2 * p ≤ p * p := by
    simpa [Nat.mul_comm p 2] using Nat.mul_le_mul_left p hp2
  have hsub : 2 * p - 2 < 2 * p := Nat.sub_lt (by omega : 0 < 2 * p) (by decide)
  omega

lemma val_low {p k : ℕ} (hp : p.Prime) (hk : k ≤ p - 1) :
    padicValNat p ((p - 1).choose k) = 0 := by
  have hp2 : 2 ≤ p := hp.two_le
  haveI : Fact p.Prime := ⟨hp⟩
  have hlog : log p (p - 1) < 2 := by
    apply log_lt_of_lt_pow (by omega : p - 1 ≠ 0)
    rw [pow_two]
    have hmul : 2 * p ≤ p * p := by
      simpa [Nat.mul_comm p 2] using Nat.mul_le_mul_left p hp2
    omega
  rw [padicValNat_choose (k := k) (n := p - 1) (b := 2) hk hlog]
  have hfilter :
      (Finset.Ico 1 2).filter (fun i => p ^ i ≤ k % p ^ i + (p - 1 - k) % p ^ i) = ∅ := by
    ext i
    simp only [mem_filter, mem_Ico, notMem_empty, iff_false, not_and]
    intro ⟨hi1, hi2⟩
    have hi : i = 1 := by omega
    subst hi
    simp only [pow_one]
    have hklt : k < p := by omega
    have hrest : p - 1 - k < p := by omega
    rw [Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hrest]
    omega
  rw [hfilter]
  simp

lemma val_high {p k : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k) (hk : k ≤ p - 1) :
    padicValNat p ((p - 1 + k).choose k) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlog : log p ((p - 1) + k) < 2 := log_lt_two hp hk
  rw [padicValNat_choose' (n := p - 1) (k := k) (b := 2) hlog]
  have hfilter :
      (Finset.Ico 1 2).filter (fun i => p ^ i ≤ k % p ^ i + (p - 1) % p ^ i) = {1} := by
    ext i
    simp only [mem_filter, mem_Ico, mem_singleton]
    constructor
    · rintro ⟨⟨hi1, hi2⟩, _⟩
      omega
    · rintro rfl
      refine ⟨⟨by decide, by decide⟩, ?_⟩
      simp only [pow_one]
      have hklt : k < p := by omega
      rw [Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt (by omega : p - 1 < p)]
      omega
  rw [hfilter]
  simp

noncomputable def polyZ (n : ℕ) : ℤ[X] :=
  ∑ k ∈ range (n + 1), C (((n.choose k ^ 2 * (n + k).choose k : ℕ) : ℤ)) * X ^ k

lemma coeff_polyZ (n j : ℕ) :
    (polyZ n).coeff j =
      if j ≤ n then (((n.choose j ^ 2 * (n + j).choose j : ℕ) : ℤ)) else 0 := by
  unfold polyZ
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hj : j ≤ n
  · simp only [hj, ite_true]
    rw [Finset.sum_eq_single j]
    · simp [mem_range, hj]
    · intro k hk hkj
      rw [if_neg hkj.symm]
    · intro hjn
      exact absurd (mem_range.mpr (by omega)) hjn
  · simp only [hj, ite_false]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : j ≠ k := by
      intro h
      subst h
      exact hj (by
        have := mem_range.mp hk
        omega)
    rw [if_neg hne]

lemma natDegree_polyZ {n : ℕ} (hn : 1 ≤ n) : (polyZ n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [coeff_polyZ]
    simp [not_le.mpr hj]
  · rw [coeff_polyZ]
    simp
    exact (Nat.choose_pos (show n ≤ n + n by omega)).ne'

lemma map_polyZ (n : ℕ) :
    (polyZ n).map (Int.castRingHom ℚ) = OeisA5258.aperyPoly n := by
  ext j
  rw [coeff_map, coeff_polyZ]
  simp only [OeisA5258.aperyPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one,
    mul_zero]
  by_cases hj : j ≤ n
  · simp only [hj, ite_true, Int.cast_natCast]
    rw [Finset.sum_eq_single j]
    · simp [mem_range, hj, Int.cast_natCast]
    · intro k hk hkj
      rw [if_neg hkj.symm]
    · intro hjn
      exact absurd (mem_range.mpr (by omega)) hjn
  · rw [if_neg hj]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hne : j ≠ k := by
      intro h
      subst h
      exact hj (by
        have := mem_range.mp hk
        omega)
    rw [if_neg hne]

end AperyPrime

open AperyPrime

theorem OMA.solution : OMA.R_OeisA5258_conjecture_R1.H1 := by
  intro n hn hp
  set p := n + 1 with hpdef
  have hp2 : 2 ≤ p := hp.two_le
  let f := polyZ n
  have hdeg : f.natDegree = n := natDegree_polyZ hn
  have hcoeff0 : f.coeff 0 = 1 := by
    rw [coeff_polyZ]
    simp [hn]
  haveI : Fact p.Prime := ⟨hp⟩
  have htr : f.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (by
      rw [constantCoeff_apply, hcoeff0]
      decide)
  let g := f.reverse
  have hdegG : g.natDegree = n := by
    rw [show g = f.reverse from rfl, reverse_natDegree, hdeg, htr, Nat.sub_zero]
  have hlead : g.leadingCoeff = 1 := by
    rw [leadingCoeff, hdegG, show g = f.reverse from rfl, coeff_reverse, hdeg, revAt_le (le_refl n),
      Nat.sub_self, hcoeff0]
  have hconst : g.coeff 0 = ((n.choose n ^ 2 * (n + n).choose n : ℕ) : ℤ) := by
    rw [show g = f.reverse from rfl, coeff_zero_reverse, leadingCoeff, hdeg, coeff_polyZ]
    simp
  have hval (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ n) :
      padicValNat p (n.choose j ^ 2 * (n + j).choose j) = 1 := by
    have hj' : j ≤ p - 1 := by omega
    have hv1 := val_low hp hj'
    have hv2 := val_high hp hj1 hj'
    have h1 : n.choose j ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have h2 : (n + j).choose j ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hsq : n.choose j ^ 2 ≠ 0 := pow_ne_zero 2 h1
    have hpow := padicValNat.pow (p := p) (n.choose j) 2
    have hmul := padicValNat.mul (p := p) hsq h2
    have hn : n = p - 1 := by omega
    rw [hmul, hpow, hn, hv1, hv2]
  have hmem (j : ℕ) (hj : j < n) : (p : ℤ) ∣ g.coeff j := by
    have hrev : g.coeff j = f.coeff (n - j) := by
      rw [show g = f.reverse from rfl, coeff_reverse, hdeg, revAt_le (by omega)]
    rw [hrev, coeff_polyZ]
    have hj' : n - j ≤ n := by omega
    simp only [hj', ite_true]
    have hpos : 1 ≤ n - j := by omega
    have hv := hval (n - j) hpos (by omega)
    have hne : n.choose (n - j) ^ 2 * (n + (n - j)).choose (n - j) ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero _ (Nat.choose_pos (by omega)).ne') (Nat.choose_pos (by omega)).ne'
    have hdvd : p ∣ n.choose (n - j) ^ 2 * (n + (n - j)).choose (n - j) := by
      rw [← pow_one p, padicValNat_dvd_iff_le hne]
      omega
    exact_mod_cast hdvd
  have hnotsq : ¬ (p : ℤ) ^ 2 ∣ g.coeff 0 := by
    rw [hconst]
    intro h
    have hv := hval n (by omega) (le_refl n)
    have hne : n.choose n ^ 2 * (n + n).choose n ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero _ (Nat.choose_pos (le_refl n)).ne')
        (Nat.choose_pos (by omega)).ne'
    have : 2 ≤ padicValNat p (n.choose n ^ 2 * (n + n).choose n) := by
      rw [← padicValNat_dvd_iff_le hne]
      exact_mod_cast h
    omega
  have hP : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime := by
    rw [Ideal.span_singleton_prime (by omega : (p : ℤ) ≠ 0)]
    exact Nat.prime_iff_prime_int.mp hp
  have hprim : g.IsPrimitive := by
    rw [isPrimitive_iff_isUnit_of_C_dvd]
    intro c hc
    have hdc : c ∣ g.coeff n := ((C_dvd_iff_dvd_coeff c g).mp hc) n
    have hgn : g.coeff n = 1 := by
      rw [show g = f.reverse from rfl, coeff_reverse, hdeg, revAt_le (le_refl n), Nat.sub_self,
        hcoeff0]
    rw [hgn] at hdc
    exact isUnit_of_dvd_one hdc
  have hirrZ : Irreducible g := by
    refine irreducible_of_eisenstein_criterion hP ?_ ?_ ?_ ?_ hprim
    · rw [hlead]
      intro h
      have : (p : ℤ) ∣ 1 := by simpa [Ideal.mem_span_singleton] using h
      have hp1 : p ∣ 1 := by exact_mod_cast this
      have : p ≤ 1 := Nat.le_of_dvd (by decide) hp1
      omega
    · intro j hj
      have hgne : g ≠ 0 := by
        intro h
        have : g.natDegree = 0 := natDegree_eq_zero.mpr ⟨0, by simp [h]⟩
        omega
      rw [degree_eq_natDegree hgne, hdegG] at hj
      exact Ideal.mem_span_singleton.mpr (hmem j (by exact_mod_cast hj))
    · have hgne : g ≠ 0 := by
        intro h
        have : g.natDegree = 0 := natDegree_eq_zero.mpr ⟨0, by simp [h]⟩
        omega
      rw [degree_eq_natDegree hgne, hdegG]
      exact_mod_cast (show 0 < n by omega)
    · intro h
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
      exact hnotsq h
  have hmapirr : Irreducible (g.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hirrZ
  have hrev : (OeisA5258.aperyPoly n).reverse = g.map (Int.castRingHom ℚ) := by
    have hf : (OeisA5258.aperyPoly n) = f.map (Int.castRingHom ℚ) := (map_polyZ n).symm
    rw [hf]
    ext j
    rw [coeff_reverse, coeff_map, coeff_map, coeff_reverse]
    have hdegm : (f.map (Int.castRingHom ℚ)).natDegree = f.natDegree := by
      rw [natDegree_map_eq_iff]
      left
      rw [leadingCoeff, hdeg, coeff_polyZ]
      simp
      exact (Nat.choose_pos (show n ≤ n + n by omega)).ne'
    rw [hdegm]
  have htrQ : (OeisA5258.aperyPoly n).natTrailingDegree = 0 := by
    apply natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
    rw [constantCoeff_apply, ← map_polyZ, coeff_map, hcoeff0]
    simp
  have hdegQ : (OeisA5258.aperyPoly n).natDegree = n := by
    rw [← map_polyZ]
    have hmap : ((polyZ n).map (Int.castRingHom ℚ)).natDegree = (polyZ n).natDegree := by
      rw [natDegree_map_eq_iff]
      left
      rw [leadingCoeff, hdeg, coeff_polyZ]
      simp
      exact (Nat.choose_pos (show n ≤ n + n by omega)).ne'
    rw [hmap, hdeg]
  rw [← hrev] at hmapirr
  refine ⟨?_, ?_⟩
  · intro hunit
    have hdeg0 : (OeisA5258.aperyPoly n).degree = 0 := (isUnit_iff_degree_eq_zero).mp hunit
    rw [degree_eq_natDegree, hdegQ] at hdeg0
    · exact absurd (Nat.cast_eq_zero.mp hdeg0) (by omega)
    · intro h
      have : (OeisA5258.aperyPoly n).natDegree = 0 := natDegree_eq_zero.mpr ⟨0, by simp [h]⟩
      omega
  · intro a b hab
    have hrevEq : (a * b).reverse = a.reverse * b.reverse := reverse_mul_of_domain a b
    rw [← hab] at hrevEq
    have hunitR := hmapirr.isUnit_or_isUnit hrevEq
    have ha0 : a ≠ 0 := by
      intro h
      have : (OeisA5258.aperyPoly n).natDegree = 0 := natDegree_eq_zero.mpr ⟨0, by simp [h, hab]⟩
      omega
    have hb0 : b ≠ 0 := by
      intro h
      have : (OeisA5258.aperyPoly n).natDegree = 0 := natDegree_eq_zero.mpr ⟨0, by simp [h, hab]⟩
      omega
    have hsplit : a.natTrailingDegree = 0 ∧ b.natTrailingDegree = 0 := by
      have hsum : a.natTrailingDegree + b.natTrailingDegree = 0 := by
        rw [← natTrailingDegree_mul ha0 hb0, ← hab, htrQ]
      omega
    rcases hunitR with ha | hb
    · left
      have hrevDeg : a.reverse.natDegree = 0 := by
        have hd : a.reverse.degree = 0 := (isUnit_iff_degree_eq_zero).mp ha
        rw [degree_eq_natDegree ha.ne_zero] at hd
        exact Nat.cast_eq_zero.mp hd
      have hnat : a.natDegree = 0 := by
        have hsub := reverse_natDegree a
        rw [hrevDeg, hsplit.1, Nat.sub_zero] at hsub
        exact hsub.symm
      rw [isUnit_iff_degree_eq_zero, degree_eq_natDegree ha0, hnat]
      rfl
    · right
      have hrevDeg : b.reverse.natDegree = 0 := by
        have hd : b.reverse.degree = 0 := (isUnit_iff_degree_eq_zero).mp hb
        rw [degree_eq_natDegree hb.ne_zero] at hd
        exact Nat.cast_eq_zero.mp hd
      have hnat : b.natDegree = 0 := by
        have hsub := reverse_natDegree b
        rw [hrevDeg, hsplit.2, Nat.sub_zero] at hsub
        exact hsub.symm
      rw [isUnit_iff_degree_eq_zero, degree_eq_natDegree hb0, hnat]
      rfl
