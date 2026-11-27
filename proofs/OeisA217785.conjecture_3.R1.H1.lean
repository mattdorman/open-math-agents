import OMAReductions.R_OeisA217785_conjecture_3_R1
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
When `n + 2` is prime, `s_n(X + 1)` is Eisenstein at that prime. The shift has
degree one, so `s_n` is irreducible over the integers and therefore over the rationals.
-/

open Polynomial Nat Finset

lemma sum_choose_shift (n j : ℕ) (hj : j ≤ n) :
    ∑ k ∈ range (n + 1), (k + 1) * k.choose j = (j + 1) * (n + 2).choose (j + 2) := by
  have hzero : ∀ k ∈ range (n + 1), k ∉ Icc j n → (k + 1) * k.choose j = 0 := by
    intro k hk hnot
    have hklt : k < j := by
      simp only [mem_range] at hk
      simp only [mem_Icc, not_and, not_le] at hnot
      omega
    simp [choose_eq_zero_of_lt hklt]
  have hsubset : Icc j n ⊆ range (n + 1) := by
    intro k hk
    simp only [mem_Icc] at hk
    simp [mem_range]
    omega
  rw [← sum_subset hsubset hzero]
  have hterm : ∀ k ∈ Icc j n, (k + 1) * k.choose j = (j + 1) * (k + 1).choose (j + 1) := by
    intro k hk
    rw [add_one_mul_choose_eq, Nat.mul_comm]
  rw [sum_congr rfl hterm, ← mul_sum]
  have hre : ∑ k ∈ Icc j n, (k + 1).choose (j + 1) =
      ∑ m ∈ Icc (j + 1) (n + 1), m.choose (j + 1) := by
    refine sum_nbij' (fun k => k + 1) (fun m => m - 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_Icc] at hk ⊢
      omega
    · intro m hm
      simp only [mem_Icc] at hm ⊢
      omega
    · intro k hk
      simp only [mem_Icc] at hk
      omega
    · intro m hm
      simp only [mem_Icc] at hm
      omega
    · intro k hk
      rfl
  rw [hre, sum_Icc_choose]

lemma coeff_shifted (n j : ℕ) :
    ((OeisA217785.polyS n).comp (X + 1)).coeff j =
      if j ≤ n then ((j + 1) * (n + 2).choose (j + 2) : ℤ) else 0 := by
  classical
  rw [OeisA217785.polyS, Polynomial.sum_comp]
  have hterm : ∀ k ∈ range (n + 1),
      (C ((k : ℤ) + 1) * X ^ k).comp (X + 1) = C ((k : ℤ) + 1) * (X + 1) ^ k := by
    intro k hk
    rw [mul_comp, C_comp, pow_comp, X_comp]
  rw [sum_congr rfl hterm, finsetSum_coeff]
  by_cases hj : j ≤ n
  · have hnat := sum_choose_shift n j hj
    simp only [coeff_C_mul, coeff_X_add_one_pow, if_pos hj]
    exact_mod_cast hnat
  · simp only [hj, if_false, coeff_C_mul, coeff_X_add_one_pow]
    apply sum_eq_zero
    intro k hk
    have hklt : k < j := by
      simp only [mem_range] at hk
      omega
    simp [choose_eq_zero_of_lt hklt]

theorem OMA.solution : OMA.R_OeisA217785_conjecture_3_R1.H1 := by
  intro n hn hp
  set p := n + 2
  have hp2 : 2 ≤ p := by omega
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  set f := OeisA217785.polyS n
  set g := f.comp (X + 1)
  have hcoeff : ∀ j, g.coeff j =
      if j ≤ n then ((j + 1) * p.choose (j + 2) : ℤ) else 0 := by
    intro j
    simpa [g, f, p] using coeff_shifted n j
  have hdeg : g.natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      rw [hcoeff, if_neg (not_le.mpr hj)]
    · rw [hcoeff, if_pos (le_refl n)]
      have : (n + 2).choose (n + 2) = 1 := choose_self _
      rw [this]
      norm_cast
  have hlead : g.leadingCoeff = (n + 1 : ℤ) := by
    rw [leadingCoeff, hdeg, hcoeff, if_pos (le_refl n), choose_self]
    norm_cast
    omega
  have hconst : g.coeff 0 = (p.choose 2 : ℤ) := by
    rw [hcoeff, if_pos (by omega : 0 ≤ n)]
    simp
  have hprev : g.coeff (n - 1) = (n * p : ℤ) := by
    have hle : n - 1 ≤ n := by omega
    rw [hcoeff, if_pos hle]
    have hch : p.choose (n - 1 + 2) = p := by
      have : n - 1 + 2 = p - 1 := by omega
      rw [this, Nat.choose_symm (by omega : 1 ≤ p), choose_one_right]
    have hmul : (n - 1 + 1) * p.choose (n - 1 + 2) = n * p := by
      have : n - 1 + 1 = n := by omega
      rw [this, hch]
    exact_mod_cast hmul
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hP : P.IsPrime := (Ideal.span_singleton_prime (by simp)).mpr (Nat.prime_iff_prime_int.mp hp)
  have hfl : g.leadingCoeff ∉ P := by
    intro hmem
    rw [Ideal.mem_span_singleton, hlead] at hmem
    have : p ∣ n + 1 := by exact_mod_cast hmem
    have : p ≤ n + 1 := le_of_dvd (by omega) this
    omega
  have hg0 : g ≠ 0 := by
    intro hzero
    have : g.coeff n = 0 := by simp [hzero]
    rw [hcoeff, if_pos (le_refl n), choose_self] at this
    norm_cast at this
  have hdegN : g.degree = n := by
    rw [degree_eq_natDegree hg0, hdeg]
  have hfP : ∀ j : ℕ, ↑j < g.degree → g.coeff j ∈ P := by
    intro j hj
    have hjn : j < n := by
      rw [hdegN] at hj
      exact_mod_cast hj
    rw [Ideal.mem_span_singleton, hcoeff, if_pos (le_of_lt hjn)]
    have hdvd : p ∣ (j + 1) * p.choose (j + 2) := by
      refine dvd_mul_of_dvd_right (hp.dvd_choose_self ?_ ?_) _
      · omega
      · omega
    exact_mod_cast hdvd
  have h0 : g.coeff 0 ∉ P ^ 2 := by
    intro hmem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hconst] at hmem
    have hsq : (p : ℤ) ^ 2 ∣ (p.choose 2 : ℤ) := hmem
    have hnat : p ^ 2 ∣ p.choose 2 := by exact_mod_cast hsq
    have hform : p.choose 2 = p * ((p - 1) / 2) := by
      have heven : Even (p - 1) := by
        rw [Nat.even_sub (by omega : 1 ≤ p)]
        simp [(not_even_iff_odd).mpr hpodd, show ¬ Even (1 : ℕ) by decide]
      have htwo : 2 ∣ p - 1 := even_iff_two_dvd.mp heven
      rw [choose_two_right, Nat.mul_div_assoc _ htwo]
    have : p ∣ (p - 1) / 2 := by
      rw [hform] at hnat
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos (by simpa [pow_two, Nat.mul_assoc] using hnat)
    have : p ∣ p - 1 := by
      have htwo : 2 * ((p - 1) / 2) = p - 1 := by
        have : 2 ∣ p - 1 := by
          have : Even (p - 1) := by
            rw [Nat.even_sub (by omega : 1 ≤ p)]
            simp [(not_even_iff_odd).mpr hpodd, show ¬ Even (1 : ℕ) by decide]
          exact even_iff_two_dvd.mp this
        exact Nat.mul_div_cancel' this
      rw [← htwo]
      exact dvd_mul_of_dvd_right this 2
    have hpone : p ∣ 1 := by
      have hpdvd : p ∣ p - (p - 1) := Nat.dvd_sub (dvd_refl p) this
      have : p - (p - 1) = 1 := by omega
      rwa [this] at hpdvd
    have : p ≤ 1 := Nat.le_of_dvd (by decide) hpone
    omega
  have hprim : g.IsPrimitive := by
    rw [isPrimitive_iff_isUnit_of_C_dvd]
    intro r hr
    have hdvd : ∀ i, r ∣ g.coeff i := (C_dvd_iff_dvd_coeff r g).1 hr
    have hr1 : r ∣ (n + 1 : ℤ) := by
      rw [← hlead, leadingCoeff, hdeg]
      exact hdvd n
    have hr2 : r ∣ (n * p : ℤ) := by
      rw [← hprev]
      exact hdvd (n - 1)
    have hcopN : Nat.Coprime (n + 1) (n * p) := by
      rw [Nat.coprime_mul_iff_right]
      constructor
      · simpa [Nat.add_comm] using
          ((Nat.coprime_add_self_left).mpr (Nat.coprime_one_left n) : (1 + n).Coprime n)
      · have : p = (n + 1) + 1 := by omega
        rw [this]
        exact (Nat.coprime_self_add_right).mpr (Nat.coprime_one_right (n + 1))
    obtain ⟨a, b, hab⟩ := hcopN.isCoprime
    have hsum : r ∣ a * ((n + 1 : ℕ) : ℤ) + b * ((n * p : ℕ) : ℤ) := by
      have hcast1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by norm_cast
      have hcast2 : ((n * p : ℕ) : ℤ) = (n : ℤ) * (p : ℤ) := by norm_cast
      rw [hcast1, hcast2]
      exact dvd_add (dvd_mul_of_dvd_right hr1 a) (dvd_mul_of_dvd_right hr2 b)
    rw [hab] at hsum
    exact isUnit_of_dvd_one hsum
  have hfd0 : 0 < g.degree := by
    rw [degree_eq_natDegree hg0, hdeg]
    exact_mod_cast hn
  have hirr : Irreducible g :=
    irreducible_of_eisenstein_criterion hP hfl hfP hfd0 h0 hprim
  have hmapg : Irreducible (g.map (algebraMap ℤ ℚ)) :=
    (IsPrimitive.irreducible_iff_irreducible_map_fraction_map (K := ℚ) hprim).mp hirr
  have hcomp : g.map (algebraMap ℤ ℚ) = (f.map (algebraMap ℤ ℚ)).comp (X + 1) := by
    simp [g, map_comp]
  have htop : f.coeff n = (n + 1 : ℤ) := by
    classical
    simp only [f]
    unfold OeisA217785.polyS
    rw [finsetSum_coeff]
    have hone : (C ((n : ℤ) + 1) * X ^ n).coeff n = (n + 1 : ℤ) := by
      rw [coeff_C_mul, coeff_X_pow]
      simp
    have hrest : ∑ k ∈ range n, (C ((k : ℤ) + 1) * X ^ k).coeff n = 0 := by
      apply sum_eq_zero
      intro k hk
      simp only [mem_range] at hk
      rw [coeff_C_mul, coeff_X_pow]
      simp [show n ≠ k by omega]
    have hsplit : range (n + 1) = insert n (range n) := by
      ext k
      simp only [mem_range, mem_insert]
      omega
    rw [hsplit, sum_insert (by simp [mem_range]), hone, hrest, add_zero]
  have hdegf : f.natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      classical
      simp only [f]
      unfold OeisA217785.polyS
      rw [finsetSum_coeff]
      apply sum_eq_zero
      intro k hk
      simp only [mem_range] at hk
      rw [coeff_C_mul, coeff_X_pow]
      simp [show j ≠ k by omega]
    · rw [htop]
      norm_cast
  let qf := f.map (algebraMap ℤ ℚ)
  have hfac : Irreducible qf := by
    refine ⟨?_, ?_⟩
    · intro hu
      have hzero : qf.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
      have hdegq : qf.natDegree = n := by
        have heq : qf.natDegree = f.natDegree := by
          rw [show qf = f.map (algebraMap ℤ ℚ) from rfl, natDegree_map_eq_iff]
          refine Or.inl ?_
          rw [leadingCoeff, hdegf, htop]
          intro h
          have : (n + 1 : ℤ) = 0 := Int.cast_injective h
          omega
        rw [heq, hdegf]
      exact absurd (hdegq.symm.trans hzero) (by omega)
    · intro a b hab
      have hmul : g.map (algebraMap ℤ ℚ) = a.comp (X + 1) * b.comp (X + 1) := by
        rw [hcomp]
        simp only [qf] at hab
        rw [hab, mul_comp]
      rcases hmapg.isUnit_or_isUnit hmul with h | h
      · left
        have hdeg0 : (a.comp (X + 1)).natDegree = 0 := natDegree_eq_zero_of_isUnit h
        have hdega : (a.comp (X + 1)).natDegree = a.natDegree := by
          rw [natDegree_comp, show (X + 1 : ℚ[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one]
        have ha0 : a.natDegree = 0 := by rw [← hdega]; exact hdeg0
        have hcompA : a.comp (X + 1) = a := by
          rw [eq_C_of_natDegree_eq_zero ha0, C_comp]
        rwa [hcompA] at h
      · right
        have hdeg0 : (b.comp (X + 1)).natDegree = 0 := natDegree_eq_zero_of_isUnit h
        have hdegb : (b.comp (X + 1)).natDegree = b.natDegree := by
          rw [natDegree_comp, show (X + 1 : ℚ[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one]
        have hb0 : b.natDegree = 0 := by rw [← hdegb]; exact hdeg0
        have hcompB : b.comp (X + 1) = b := by
          rw [eq_C_of_natDegree_eq_zero hb0, C_comp]
        rwa [hcompB] at h
  have halg : algebraMap ℤ ℚ = Int.castRingHom ℚ := rfl
  simpa [qf, halg] using hfac
