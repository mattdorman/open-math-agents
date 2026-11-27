import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic

/-!
If q ≡ 1 mod p, the repunit N = (q^p - 1)/(q - 1) is 0 mod p, while
M = (p^q - 1)/(p - 1) is 1 mod p. A prime divisor of N therefore misses M.
-/

open Finset Nat

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H1 := by
  intro p q hp hq hpq hmod
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := by omega
  have hN : (q ^ p - 1) / (q - 1) = ∑ i ∈ range p, q ^ i := (Nat.geomSum_eq hq2 p).symm
  have hM : (p ^ q - 1) / (p - 1) = ∑ i ∈ range q, p ^ i := (Nat.geomSum_eq hp2 q).symm
  have hNmod : p ∣ ∑ i ∈ range p, q ^ i := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    simp_rw [Nat.cast_pow]
    have hq1 : (q : ZMod p) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff, Nat.ModEq, hmod]
      exact (Nat.mod_eq_of_lt (by omega : 1 < p)).symm
    simp [hq1, Finset.sum_const, Finset.card_range]
  have hMmod : ¬ p ∣ ∑ i ∈ range q, p ^ i := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    simp_rw [Nat.cast_pow]
    have hq1 : q = (q - 1) + 1 := by omega
    rw [hq1, sum_range_succ']
    simp [pow_succ]
    intro h
    have hp1 : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h)
    have : p ≤ 1 := Nat.le_of_dvd (by decide) hp1
    omega
  intro hdiv
  rw [hN, hM] at hdiv
  exact hMmod (hNmod.trans hdiv)
