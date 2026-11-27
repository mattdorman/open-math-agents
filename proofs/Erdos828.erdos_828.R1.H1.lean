import OMAReductions.R_Erdos828_erdos_828_R1
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Totient
import Mathlib.Order.Interval.Finset.Basic

/-!
Known cases of Erdős 828. Powers of two are divisible by their totient, and if
φ(m) divides m then m times a large prime is divisible by its totient after
subtracting m.
-/

open Nat

lemma infinite_zero :
    {n : ℕ | ((n.totient : ℕ) : ℤ) ∣ (n : ℤ)}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  refine ⟨2 ^ (N + 1), ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq]
    have hk : 0 < N + 1 := by omega
    have hφ : (2 ^ (N + 1)).totient = 2 ^ N := by
      rw [totient_prime_pow (by decide : (2 : ℕ).Prime) hk]
      simp
    rw [hφ]
    exact Int.natCast_dvd_natCast.mpr (pow_dvd_pow 2 (Nat.le_succ N))
  · have : N + 1 < 2 ^ (N + 1) := Nat.lt_pow_self (by decide : 1 < 2)
    omega

lemma infinite_neg (m : ℕ) (hm : 0 < m) (hdiv : m.totient ∣ m) :
    {n : ℕ | ((n.totient : ℕ) : ℤ) ∣ (n : ℤ) + (-(m : ℤ))}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨p, hpge, hpp⟩ := exists_infinite_primes (max (N + 1) (m + 1))
  have hpN : N < p := by
    have : N + 1 ≤ p := (le_max_left _ _).trans hpge
    omega
  have hpm : m < p := by
    have : m + 1 ≤ p := (le_max_right _ _).trans hpge
    omega
  have hnd : ¬ p ∣ m := by
    intro h
    exact absurd (le_of_dvd hm h) (not_le_of_gt hpm)
  refine ⟨m * p, ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq]
    have hφ : (m * p).totient = m.totient * (p - 1) := by
      rw [mul_comm, totient_mul_of_prime_of_not_dvd hpp hnd, mul_comm]
    have hsub : m * p - m = m * (p - 1) := by
      calc
        m * p - m = m * p - m * 1 := by rw [Nat.mul_one]
        _ = m * (p - 1) := (Nat.mul_sub m p 1).symm
    have hnat : (m * p).totient ∣ m * p - m := by
      rw [hφ, hsub]
      exact mul_dvd_mul_right hdiv (p - 1)
    have hcast : ((m * p : ℕ) : ℤ) + (-(m : ℤ)) = ((m * p - m : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.le_mul_of_pos_right m hpp.pos)]
      ring
    rw [hcast]
    exact Int.natCast_dvd_natCast.mpr hnat
  · have : p ≤ m * p := Nat.le_mul_of_pos_left p hm
    omega

theorem OMA.solution : OMA.R_Erdos828_erdos_828_R1.H1 := by
  intro a ha
  rcases ha with rfl | ⟨m, hm, hdiv, rfl⟩
  · simpa using infinite_zero
  · simpa using infinite_neg m hm hdiv
