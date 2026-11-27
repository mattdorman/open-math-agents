import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
If N has a prime factor r whose residue degree avoids q, then N does not divide M.
The order of p modulo r is 1 or q. Order 1 forces r = q, but N is 1 mod q.
Order q forces q to divide r - 1.
-/

open Finset Nat

theorem OMA.solution :
    OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1.H1 := by
  intro p q hp hq _hpq _hmod _h4 ⟨r, hr, hrN, hqr⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := by omega
  set N := (q ^ p - 1) / (q - 1)
  set M := (p ^ q - 1) / (p - 1)
  have hMsum : M = ∑ i ∈ range q, p ^ i := (Nat.geomSum_eq hp2 q).symm
  have hNsum : N = ∑ i ∈ range p, q ^ i := (Nat.geomSum_eq hq2 p).symm
  have hmul : M * (p - 1) = p ^ q - 1 := by
    have h := geom_sum_mul_add (p - 1) q
    have hp1 : (p - 1) + 1 = p := by omega
    rw [hp1, ← hMsum] at h
    have hle : 1 ≤ p ^ q := one_le_pow _ _ (by omega)
    omega
  intro hdiv
  have hrM : r ∣ M := hrN.trans hdiv
  have hrpow : r ∣ p ^ q - 1 := by
    rw [← hmul]
    exact dvd_mul_of_dvd_left hrM (p - 1)
  haveI : Fact r.Prime := ⟨hr⟩
  have hpow : (p : ZMod r) ^ q = 1 := by
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff, Nat.ModEq]
    have hle : 1 ≤ p ^ q := one_le_pow _ _ (by omega)
    have hmod0 : (p ^ q - 1) % r = 0 := Nat.mod_eq_zero_of_dvd hrpow
    have hsplit : p ^ q = (p ^ q - 1) + 1 := by omega
    rw [hsplit, Nat.add_mod, hmod0, Nat.zero_add, Nat.mod_mod]
  have hr2 : 2 ≤ r := hr.two_le
  have hpne : (p : ZMod r) ≠ 0 := by
    intro h0
    have hzero : (p : ZMod r) ^ q = 0 := by
      rw [h0]
      exact zero_pow hq.ne_zero
    have : (0 : ZMod r) = 1 := hzero.symm.trans hpow
    rw [← Nat.cast_zero, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff, Nat.ModEq,
      Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < r)] at this
    omega
  have hdivord : orderOf (p : ZMod r) ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hpow
  rcases (dvd_prime hq).mp hdivord with hord | hord
  · have hp1 : (p : ZMod r) = 1 := (orderOf_eq_one_iff).mp hord
    have hMmod : M ≡ q [MOD r] := by
      rw [hMsum, ← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
      simp_rw [Nat.cast_pow]
      simp [hp1, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    have hrq : r ∣ q := by
      have hM0 : M ≡ 0 [MOD r] := by
        rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd hrM, Nat.zero_mod]
      have : q ≡ 0 [MOD r] := hMmod.symm.trans hM0
      rw [Nat.ModEq, Nat.zero_mod] at this
      exact dvd_of_mod_eq_zero this
    have hrqeq : r = q := (prime_dvd_prime_iff_eq hr hq).mp hrq
    have hN1 : N % q = 1 := by
      rw [hNsum]
      have hsum : ∑ i ∈ range p, (q : ZMod q) ^ i = 1 := by
        rw [show p = (p - 1) + 1 by omega, sum_range_succ']
        simp [pow_succ, mul_zero, sum_const_zero]
      have hmod' : (∑ i ∈ range p, q ^ i) ≡ 1 [MOD q] := by
        rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one, Nat.cast_sum]
        simp_rw [Nat.cast_pow]
        exact hsum
      rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < q)] at hmod'
      exact hmod'
    have hqN : q ∣ N := hrqeq ▸ hrN
    have : N % q = 0 := Nat.mod_eq_zero_of_dvd hqN
    omega
  · have hfermat : (p : ZMod r) ^ (r - 1) = 1 := ZMod.pow_card_sub_one_eq_one hpne
    have hdivr : orderOf (p : ZMod r) ∣ r - 1 := orderOf_dvd_iff_pow_eq_one.mpr hfermat
    rw [hord] at hdivr
    exact hqr hdivr
