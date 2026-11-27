import OMAReductions.R_Erdos420_erdos_420_parts_i_R1
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

-- Step Erdos420.erdos_420.parts.i.R1.H2
-- Credit: @mattdorman
-- If (a, b] contains s*p with p prime and s < p, the p-adic valuation of a!
-- is at most s-1, while b! gains at least one more factor p. That multiplies
-- the divisor count by at least (s+1)/s.

open scoped ArithmeticFunction.sigma

theorem OMA.solution : OMA.R_Erdos420_erdos_420_parts_i_R1.H2 := by
  intro a b p s hp hs hsp ha hb
  let d := a.factorial
  let e := d.factorization p
  let v := ordCompl[p] d
  have hd : d ≠ 0 := Nat.factorial_ne_zero _
  have hdet : p ^ e * v = d := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : p.Coprime v := Nat.coprime_ordCompl hp hd
  have hpmul : p * d ∣ (s * p).factorial := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, s * p = m + 1 := ⟨s * p - 1, by omega⟩
    rw [hm, Nat.factorial_succ]
    apply Nat.mul_dvd_mul
    · rw [← hm]
      exact dvd_mul_left p s
    · exact Nat.factorial_dvd_factorial (by omega)
  have hfactor :=
    (Nat.factorization_le_iff_dvd (Nat.mul_ne_zero hp.ne_zero hd) (Nat.factorial_ne_zero _)).2
      hpmul p
  have hbefore : (s * p).factorial.factorization p = s := by
    rw [Nat.mul_comm s p, Nat.factorization_factorial_mul hp,
      Nat.factorization_factorial_eq_zero_of_lt hsp, Nat.zero_add]
  rw [Nat.factorization_mul hp.ne_zero hd, Finsupp.add_apply, hp.factorization_self, hbefore]
    at hfactor
  have he : e + 1 ≤ s := by simpa [e, Nat.add_comm] using hfactor
  have hdiv := hpmul.trans (Nat.factorial_dvd_factorial hb)
  have hcount : σ 0 (p * d) ≤ σ 0 b.factorial := by
    simp only [ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _) hdiv)
  have count_for (j : ℕ) : σ 0 (p ^ j * v) = (j + 1) * σ 0 v := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_left j),
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  have hdcount : σ 0 d = (e + 1) * σ 0 v := hdet ▸ count_for e
  have hpd : p ^ (e + 1) * v = p * d := by
    rw [pow_succ, ← hdet]
    ac_rfl
  have hpdcount : σ 0 (p * d) = (e + 1 + 1) * σ 0 v := hpd ▸ count_for (e + 1)
  change (s + 1) * σ 0 d ≤ _
  calc
    (s + 1) * σ 0 d = ((s + 1) * (e + 1)) * σ 0 v := by rw [hdcount, Nat.mul_assoc]
    _ ≤ (s * (e + 1 + 1)) * σ 0 v := by
      apply Nat.mul_le_mul_right
      rw [Nat.add_one_mul, Nat.mul_add_one s (e + 1)]
      omega
    _ = s * σ 0 (p * d) := by rw [hpdcount, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left s hcount
