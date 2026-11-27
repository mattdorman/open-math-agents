import OMAReductions.R_Erdos366_erdos_366_variants_weaker_R2

-- A positive cube times a fourth power times a fifth power is 3-full:
-- every prime factor meets exponent at least 3.

theorem OMA.solution : OMA.R_Erdos366_erdos_366_variants_weaker_R2.H2 := by
  intro a b c ha hb hc p hp
  have hpr := (Nat.mem_primeFactors.mp hp).1
  have hn := Nat.dvd_of_mem_primeFactors hp
  have hmul : p ∣ a ^ 3 * (b ^ 4 * c ^ 5) := by simpa [Nat.mul_assoc] using hn
  rcases hpr.dvd_mul.mp hmul with ha3 | hrest
  · have hpow : p ^ 3 ∣ a ^ 3 := pow_dvd_pow_of_dvd (hpr.dvd_of_dvd_pow ha3) 3
    have htail : a ^ 3 ∣ a ^ 3 * (b ^ 4 * c ^ 5) := dvd_mul_right _ _
    simpa [Nat.mul_assoc] using dvd_trans hpow htail
  · rcases hpr.dvd_mul.mp hrest with hb4 | hc5
    · have hpow : p ^ 3 ∣ b ^ 4 :=
        dvd_trans (pow_dvd_pow p (by decide : 3 ≤ 4))
          (pow_dvd_pow_of_dvd (hpr.dvd_of_dvd_pow hb4) 4)
      have htail : b ^ 4 ∣ b ^ 4 * (a ^ 3 * c ^ 5) := dvd_mul_right _ _
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using dvd_trans hpow htail
    · have hpow : p ^ 3 ∣ c ^ 5 :=
        dvd_trans (pow_dvd_pow p (by decide : 3 ≤ 5))
          (pow_dvd_pow_of_dvd (hpr.dvd_of_dvd_pow hc5) 5)
      have htail : c ^ 5 ∣ c ^ 5 * (a ^ 3 * b ^ 4) := dvd_mul_right _ _
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using dvd_trans hpow htail
