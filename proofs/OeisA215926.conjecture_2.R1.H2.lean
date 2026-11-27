import OMAReductions.R_OeisA215926_conjecture_2_R1

-- An odd prime q < 2^{j+1} makes 2^j * q perfect or abundant:
-- σ(2^j * q) - 2^{j+1} * q = 2^{j+1} - 1 - q ≥ 0.

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  intro j q hq hq2 hqlt
  have hpos : 0 < 2 ^ j * q := Nat.mul_pos (pow_pos (by decide) _) hq.pos
  have hodd : Odd q := hq.odd_of_ne_two (by omega)
  have hcop : Nat.Coprime (2 ^ j) q := (Nat.coprime_two_left.mpr hodd).pow_left j
  have hsum : ∑ d ∈ (2 ^ j * q).divisors, d = (2 ^ (j + 1) - 1) * (q + 1) := by
    rw [hcop.sum_divisors_mul, Nat.sum_divisors_prime_pow Nat.prime_two]
    have hgeom : ∑ i ∈ Finset.range (j + 1), 2 ^ i = 2 ^ (j + 1) - 1 := by
      have h := Nat.geomSum_eq (by decide : 2 ≤ 2) (j + 1)
      simpa [Nat.div_one] using h
    have hqsum : ∑ d ∈ q.divisors, d = q + 1 := by
      rw [← pow_one q, Nat.sum_divisors_prime_pow hq]
      simp [Finset.sum_range_succ, Finset.range_one, pow_zero, pow_one, add_comm]
    simp [hgeom, hqsum]
  have hge : 2 * (2 ^ j * q) ≤ ∑ d ∈ (2 ^ j * q).divisors, d := by
    rw [hsum]
    have htwo : 2 * (2 ^ j * q) = 2 ^ (j + 1) * q := by
      rw [pow_succ]
      ac_rfl
    rw [htwo]
    have hone : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow _ _ (by decide)
    have hrest : q ≤ 2 ^ (j + 1) - 1 := by
      have hlt : q < 2 ^ (j + 1) := by simpa [pow_succ, Nat.mul_comm] using hqlt
      omega
    have hsplit : (2 ^ (j + 1) - 1) * (q + 1) =
        2 ^ (j + 1) * q + (2 ^ (j + 1) - 1 - q) := by
      zify [hone, hrest]
      ring
    omega
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, Nat.abundant_iff_sum_divisors]
  omega
