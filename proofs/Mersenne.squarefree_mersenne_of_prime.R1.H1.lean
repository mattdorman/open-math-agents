import OMAReductions.R_Mersenne_squarefree_mersenne_of_prime_R1
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
A squared prime factor of a prime-exponent Mersenne number is a Wieferich prime.
The order of 2 modulo p is q, so q divides p - 1, and 2 ^ q ≡ 1 mod p ^ 2 lifts to
the Fermat quotient.
-/

open Nat

theorem OMA.solution : OMA.R_Mersenne_squarefree_mersenne_of_prime_R1.H1 := by
  intro q p hq hp hsq
  have hbase : 2 ^ q ≡ 1 [MOD p ^ 2] :=
    ((modEq_iff_dvd' (one_le_pow q 2 (by decide))).2 (by simpa [mersenne] using hsq)).symm
  have hdvd : p ∣ mersenne q := by
    have : p * p ∣ mersenne q := by simpa [pow_two] using hsq
    exact (dvd_mul_left p p).trans this
  have hpne : p ≠ 2 := by
    intro hp2
    subst hp2
    have htwo : 2 ∣ 2 ^ q - 1 := (dvd_mul_left 2 2).trans (by simpa [mersenne] using hsq)
    have hpow : 2 ∣ 2 ^ q := dvd_pow_self 2 hq.ne_zero
    have hle : 1 ≤ 2 ^ q := one_le_pow q 2 (by decide)
    have hsub : 2 ∣ 2 ^ q - (2 ^ q - 1) := dvd_sub hpow htwo
    have : 2 ^ q - (2 ^ q - 1) = 1 := by omega
    rw [this] at hsub
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hord := OMA.R_Mersenne_squarefree_mersenne_of_prime_R1.orderOf_two_eq hq hp hdvd
  have hunit : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have : p = 2 := by
      have hp2 : 2 ≤ p := hp.two_le
      have : p ≤ 2 := le_of_dvd (by decide) hdv
      omega
    exact hpne this
  have hdiv : q ∣ p - 1 := by
    have hfermat : orderOf (2 : ZMod p) ∣ p - 1 :=
      orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one hunit)
    rwa [hord] at hfermat
  obtain ⟨t, ht⟩ := hdiv
  have hpow : 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
    rw [ht, pow_mul]
    simpa [one_pow] using hbase.pow t
  exact IsWieferichPrimeBase.of_pow_modEq hp hpow
