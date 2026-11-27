import OMAReductions.R_ErdosMoser_erdos_moser_conjecture_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic

/-!
For an odd exponent the residues `j` and `m - j` cancel, so both `m - 1` and `m`
divide twice the power sum. They are coprime, hence `m - 1` divides 2. The only
remaining positive solution is `(k, m) = (1, 3)`.
-/

open Finset

lemma two_mul_powSum_zmod {k m : ℕ} (hk : Odd k) (_hm : 0 < m) :
    (2 : ZMod m) * ∑ j ∈ Ico 1 m, (j : ZMod m) ^ k = 0 := by
  let s := Ico 1 m
  have hmem : ∀ a ∈ s, m - a ∈ s := by
    intro a ha
    rw [mem_Ico] at ha ⊢
    omega
  have hinv : ∀ a ∈ s, m - (m - a) = a := by
    intro a ha
    have : a ≤ m := by
      rw [mem_Ico] at ha
      omega
    omega
  have hreindex :
      ∑ j ∈ s, ((m - j : ℕ) : ZMod m) ^ k = ∑ j ∈ s, (j : ZMod m) ^ k := by
    refine sum_nbij' (fun a => m - a) (fun a => m - a) hmem hmem hinv hinv ?_
    intro _ _
    rfl
  have hneg :
      ∑ j ∈ s, ((m - j : ℕ) : ZMod m) ^ k = -∑ j ∈ s, (j : ZMod m) ^ k := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl ?_
    intro j hj
    have hjle : j ≤ m := by
      rw [mem_Ico] at hj
      omega
    rw [Nat.cast_sub hjle, ZMod.natCast_self, zero_sub, hk.neg_pow]
  have hs : ∑ j ∈ s, (j : ZMod m) ^ k = -∑ j ∈ s, (j : ZMod m) ^ k := by
    nth_rw 1 [hreindex.symm]
    exact hneg
  rw [two_mul]
  nth_rw 1 [hs]
  exact neg_add_cancel _

lemma n_dvd_two_mul_powSum (k n : ℕ) (hk : Odd k) (hn : 0 < n) :
    n ∣ 2 * ∑ j ∈ Ico 1 (n + 1), j ^ k := by
  rw [← ZMod.natCast_eq_zero_iff]
  have hsplit : ∑ j ∈ Ico 1 (n + 1), j ^ k = ∑ j ∈ Ico 1 n, j ^ k + n ^ k := by
    have hins : Ico 1 (n + 1) = insert n (Ico 1 n) := by
      ext x
      simp only [mem_Ico, mem_insert]
      omega
    have hnot : n ∉ Ico 1 n := by
      simp only [mem_Ico]
      omega
    rw [hins, sum_insert hnot, add_comm]
  rw [hsplit]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_sum, Nat.cast_pow,
    ZMod.natCast_self, zero_pow (Odd.pos hk).ne.symm, add_zero]
  exact two_mul_powSum_zmod (k := k) (m := n) hk hn

lemma succ_dvd_two_mul_powSum (k n : ℕ) (hk : Odd k) (hn : 0 < n) :
    n + 1 ∣ 2 * ∑ j ∈ Ico 1 (n + 1), j ^ k := by
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_pow]
  exact two_mul_powSum_zmod (k := k) (m := n + 1) hk (by omega)

lemma mul_dvd_two_mul_powSum (k n : ℕ) (hk : Odd k) (hn : 0 < n) :
    n * (n + 1) ∣ 2 * ∑ j ∈ Ico 1 (n + 1), j ^ k := by
  have hcop : Nat.Coprime n (n + 1) :=
    (Nat.coprime_self_add_right).mpr (Nat.coprime_one_right n)
  exact hcop.mul_dvd_of_dvd_of_dvd (n_dvd_two_mul_powSum k n hk hn)
    (succ_dvd_two_mul_powSum k n hk hn)

theorem OMA.solution : OMA.R_ErdosMoser_erdos_moser_conjecture_R1.H1 := by
  intro k m hk hm hodd hsum
  by_cases hm1 : m = 1
  · simp [hm1, ErdosMoser.powerSum] at hsum
  have hm2 : 2 ≤ m := by omega
  let n := m - 1
  have hn : 0 < n := by omega
  have hnm : n + 1 = m := by omega
  have hdiv : n * m ∣ 2 * m ^ k := by
    have hdiv0 := mul_dvd_two_mul_powSum k n hodd hn
    rw [hnm] at hdiv0
    rwa [← ErdosMoser.powerSum, hsum] at hdiv0
  obtain ⟨t, ht⟩ := hdiv
  have hk0 : 1 ≤ k := hk
  have hcancel : 2 * m ^ (k - 1) = n * t := by
    have hpow : m ^ k = m * m ^ (k - 1) := by
      have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk0).symm
      nth_rw 1 [hk1]
      rw [Nat.pow_succ']
    have hmul : m * (2 * m ^ (k - 1)) = m * (n * t) := by
      calc
        m * (2 * m ^ (k - 1)) = 2 * (m * m ^ (k - 1)) := by ac_rfl
        _ = 2 * m ^ k := by rw [← hpow]
        _ = n * m * t := ht
        _ = m * (n * t) := by ac_rfl
    exact Nat.mul_left_cancel (by omega) hmul
  have hcop : Nat.Coprime n (m ^ (k - 1)) := by
    rw [← hnm]
    exact ((Nat.coprime_self_add_right).mpr (Nat.coprime_one_right n)).pow_right _
  have hn2 : n ∣ 2 := (hcop.dvd_mul_right).mp ⟨t, hcancel⟩
  have hnle : n ≤ 2 := Nat.le_of_dvd (by decide) hn2
  have hn1 : 1 ≤ n := hn
  interval_cases n
  · have hm2' : m = 2 := by omega
    have hleft : ErdosMoser.powerSum k m = 1 := by
      rw [hm2', ErdosMoser.powerSum]
      have : Ico 1 2 = insert 1 ∅ := by decide
      rw [this, sum_insert (by decide), sum_empty, Nat.one_pow, add_zero]
    rw [hleft, hm2'] at hsum
    exact absurd hsum (ne_of_lt (Nat.one_lt_pow (Odd.pos hodd).ne.symm (by decide : 1 < 2)))
  · have hm3 : m = 3 := by omega
    have hleft : ErdosMoser.powerSum k m = 1 + 2 ^ k := by
      rw [hm3, ErdosMoser.powerSum]
      have h2 : Ico 1 2 = insert 1 ∅ := by decide
      have h3 : Ico 1 3 = insert 2 (Ico 1 2) := by decide
      rw [h3, sum_insert (by decide), h2, sum_insert (by decide), sum_empty, Nat.one_pow, add_zero,
        add_comm]
    rw [hleft, hm3] at hsum
    have hk' : k = 1 ∨ 2 ≤ k := by omega
    rcases hk' with rfl | hk2
    · exact ⟨rfl, hm3⟩
    · have hlt : 1 + 2 ^ k < 3 ^ k := by
        have hbase : 2 ^ (k - 1) ≤ 3 ^ (k - 1) :=
          Nat.pow_le_pow_left (by decide : 2 ≤ 3) (k - 1)
        have htwo : 2 ≤ 2 ^ (k - 1) := by
          have : 2 ^ 1 ≤ 2 ^ (k - 1) :=
            Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ k - 1)
          simpa using this
        have hpow3 : 3 ^ k = 3 * 3 ^ (k - 1) := by
          have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
          nth_rw 1 [hk1]
          rw [Nat.pow_succ']
        have hpow2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
          have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
          nth_rw 1 [hk1]
          rw [Nat.pow_succ']
        have hthree : 2 * 2 ^ (k - 1) + 2 ^ (k - 1) = 3 * 2 ^ (k - 1) := by
          let x := 2 ^ (k - 1)
          change 2 * x + x = 3 * x
          omega
        calc
          1 + 2 ^ k < 2 + 2 ^ k := by omega
          _ ≤ 2 ^ (k - 1) + 2 ^ k := Nat.add_le_add_right htwo _
          _ = 2 ^ k + 2 ^ (k - 1) := by ac_rfl
          _ = 2 * 2 ^ (k - 1) + 2 ^ (k - 1) := by rw [hpow2]
          _ = 3 * 2 ^ (k - 1) := hthree
          _ ≤ 3 * 3 ^ (k - 1) := Nat.mul_le_mul_left 3 hbase
          _ = 3 ^ k := hpow3.symm
      exact absurd hsum (ne_of_lt hlt)
