import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
If p ≡ 3 mod 4 and q ≡ 1 mod 4, with q not congruent to 1 mod p, quadratic
reciprocity makes J(p | N) equal to -1. Divisibility N | M would force it to be 1.
-/

open Finset Nat NumberTheorySymbols

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H2 := by
  intro p q hp hq hpq hmod hp4 hq4
  have hp2 : 2 ≤ p := by omega
  have hq2 : 2 ≤ q := by omega
  set N := (q ^ p - 1) / (q - 1)
  set M := (p ^ q - 1) / (p - 1)
  have hNsum : N = ∑ i ∈ range p, q ^ i := (Nat.geomSum_eq hq2 p).symm
  have hMsum : M = ∑ i ∈ range q, p ^ i := (Nat.geomSum_eq hp2 q).symm
  have hNmod : N % p = 1 := by
    haveI : Fact p.Prime := ⟨hp⟩
    rw [hNsum]
    have hq1 : (q : ZMod p) ≠ 1 := by
      intro h
      have : q ≡ 1 [MOD p] := by
        rwa [← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h
      rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < p)] at this
      exact hmod this
    have hcard : (q : ZMod p) ^ p = q := by
      simpa using ZMod.pow_card (q : ZMod p)
    have hsum : ∑ i ∈ range p, (q : ZMod p) ^ i = 1 := by
      rw [geom_sum_eq hq1, hcard]
      exact div_self (sub_ne_zero.mpr hq1)
    have hsumMod : (∑ i ∈ range p, q ^ i) ≡ 1 [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one, Nat.cast_sum]
      simp_rw [Nat.cast_pow]
      exact hsum
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < p)] at hsumMod
    exact hsumMod
  have hN4 : N % 4 = 3 := by
    have hpow : ∀ i, q ^ i % 4 = 1 := by
      intro i
      rw [Nat.pow_mod, hq4, one_pow, Nat.mod_eq_of_lt (by decide : 1 < 4)]
    have hsumMod : (∑ i ∈ range p, q ^ i) ≡ 3 [MOD 4] := by
      rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
      simp_rw [Nat.cast_pow]
      have : ∑ i ∈ range p, (q : ZMod 4) ^ i = ∑ i ∈ range p, (1 : ZMod 4) := by
        refine sum_congr rfl ?_
        intro i _
        have : ((q ^ i : ℕ) : ZMod 4) = ((1 : ℕ) : ZMod 4) := by
          rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, hpow i, Nat.mod_eq_of_lt (by decide : 1 < 4)]
        simpa [Nat.cast_pow] using this
      rw [this, sum_const, card_range, nsmul_eq_mul, mul_one]
      rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, hp4, Nat.mod_eq_of_lt (by decide : 3 < 4)]
    rw [← hNsum, Nat.ModEq, Nat.mod_eq_of_lt (by decide : 3 < 4)] at hsumMod
    exact hsumMod
  have hNodd : Odd N := odd_iff.mpr (odd_of_mod_four_eq_three hN4)
  have hpodd : Odd p := odd_iff.mpr (odd_of_mod_four_eq_three hp4)
  have hNgt : 1 < N := by
    rw [hNsum]
    have hpair : q ^ 0 + q ^ 1 ≤ ∑ i ∈ range p, q ^ i := by
      have hsub : ({0, 1} : Finset ℕ) ⊆ range p := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact mem_range.mpr (by omega)
        · exact mem_range.mpr (by omega)
      have := sum_le_sum_of_subset_of_nonneg (s := ({0, 1} : Finset ℕ)) (t := range p)
        (f := fun i => q ^ i) hsub (fun _ _ _ => Nat.zero_le _)
      simpa using this
    simp at hpair
    omega
  have hmul : M * (p - 1) = p ^ q - 1 := by
    have h := geom_sum_mul_add (p - 1) q
    have hp1 : (p - 1) + 1 = p := by omega
    rw [hp1, ← hMsum] at h
    have hle : 1 ≤ p ^ q := one_le_pow _ _ (by omega)
    omega
  intro hdiv
  have hpowdvd : N ∣ p ^ q - 1 := by
    obtain ⟨t, ht⟩ := hdiv
    refine ⟨t * (p - 1), ?_⟩
    rw [← hmul, ht]
    ac_rfl
  have hrec : J(p | N) = -1 := by
    rw [jacobiSym.quadratic_reciprocity_three_mod_four hp4 hN4]
    have : J(N | p) = 1 := by
      rw [jacobiSym.mod_left, show ((N : ℤ) % p) = (1 : ℤ) by
        calc
          ((N : ℤ) % p) = ((N % p : ℕ) : ℤ) := (Int.natCast_mod N p).symm
          _ = 1 := by rw [hNmod]; rfl]
      exact jacobiSym.one_left p
    rw [this]
  have hdivsym : J(p | N) = 1 := by
    have hpowJ : J(p | N) ^ q = J((p : ℤ) ^ q | N) := (jacobiSym.pow_left (p : ℤ) q N).symm
    have hone : J((p : ℤ) ^ q | N) = 1 := by
      rw [← Int.natCast_pow, jacobiSym.mod_left']
      · exact jacobiSym.one_left N
      · have hle : 1 ≤ p ^ q := one_le_pow _ _ (by omega)
        have hmod0 : (p ^ q - 1) % N = 0 := mod_eq_zero_of_dvd hpowdvd
        have hsum : p ^ q = (p ^ q - 1) + 1 := by omega
        have h1 : 1 < N := hNgt
        have hnat : p ^ q % N = 1 := by
          rw [hsum, Nat.add_mod, hmod0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt h1]
        have hleft : (((p ^ q : ℕ) : ℤ) % (N : ℤ)) = ((1 : ℕ) : ℤ) := by
          rw [(Int.natCast_mod (p ^ q) N).symm, hnat]
        have hright : ((1 : ℤ) % (N : ℤ)) = (1 : ℤ) := by
          apply Int.emod_eq_of_lt
          · decide
          · exact_mod_cast h1
        exact hleft.trans hright.symm
    rw [← hpowJ] at hone
    have htri := jacobiSym.trichotomy (p : ℤ) N
    rcases htri with h0 | h1 | hn1
    · rw [h0, zero_pow (by omega : q ≠ 0)] at hone
      exact absurd hone (by decide)
    · exact h1
    · rw [hn1, (odd_iff.mpr (odd_of_mod_four_eq_one hq4)).neg_one_pow] at hone
      exact absurd hone (by decide)
  exact absurd hdivsym (by rw [hrec]; decide)
