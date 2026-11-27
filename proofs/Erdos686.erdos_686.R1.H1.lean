import OMAReductions.R_Erdos686_erdos_686_R1
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.NumberTheory.Pell

/-!
Every integer N ≥ 2 that is not a square is a ratio of two products of two
consecutive integers. From a positive solution of the Pell equation
x² - N y² = 1, the square of that solution has even y, and
(x + N y)² - N (x + y)² = 1 - N gives the two products.
-/

open Finset Nat Pell.Solution₁

theorem OMA.solution : OMA.R_Erdos686_erdos_686_R1.H1 := by
  intro N hN hsq
  have hd : ¬ IsSquare (N : ℤ) := by simpa [Int.isSquare_natCast_iff] using hsq
  have hpos : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨a, hax, hay⟩ := exists_pos_of_not_isSquare hpos hd
  let s : Pell.Solution₁ (N : ℤ) := a ^ 2
  have hy_form : s.y = 2 * (a.x * a.y) := by
    simp only [s, pow_two, y_mul]
    ring
  have hsy : 0 < s.y := by
    rw [hy_form]
    exact mul_pos (by decide : (0 : ℤ) < 2) (mul_pos (by omega : 0 < a.x) hay)
  have hsx : 0 < s.x := x_pow_pos (by omega : 0 < a.x) 2
  have hprop : s.x ^ 2 - (N : ℤ) * s.y ^ 2 = 1 := s.prop
  have hy_even : Even s.y := by
    rw [hy_form]
    exact even_two_mul (a.x * a.y)
  have hx_odd : Odd s.x := by
    have hy2 : Even (s.y ^ 2) := by
      rw [sq]
      exact hy_even.mul_left s.y
    have hyN : Even ((N : ℤ) * s.y ^ 2) := hy2.mul_left _
    have hx2 : ¬ Even (s.x ^ 2) := by
      rw [prop_x, Int.not_even_iff_odd]
      exact Odd.add_even odd_one hyN
    refine (Int.not_even_iff_odd).mp ?_
    intro h
    apply hx2
    rw [sq]
    exact h.mul_left s.x
  let A : ℤ := s.x + (N : ℤ) * s.y
  let B : ℤ := s.x + s.y
  have hAeq : A ^ 2 - (N : ℤ) * B ^ 2 = 1 - N := by
    calc
      A ^ 2 - (N : ℤ) * B ^ 2
          = (s.x + (N : ℤ) * s.y) ^ 2 - (N : ℤ) * (s.x + s.y) ^ 2 := rfl
      _ = (1 - (N : ℤ)) * (s.x ^ 2 - (N : ℤ) * s.y ^ 2) := by ring
      _ = 1 - N := by rw [hprop]; ring
  have hdiv_eq : A ^ 2 - 1 = (N : ℤ) * (B ^ 2 - 1) := by linarith
  have hAodd : Odd A := hx_odd.add_even (hy_even.mul_left _)
  have hBodd : Odd B := hx_odd.add_even hy_even
  have hAdiv : 2 ∣ A - 3 := (hAodd.sub_odd (by decide : Odd (3 : ℤ))).two_dvd
  have hBdiv : 2 ∣ B - 3 := (hBodd.sub_odd (by decide : Odd (3 : ℤ))).two_dvd
  let mZ : ℤ := (A - 3) / 2
  let nZ : ℤ := (B - 3) / 2
  have hm2 : 2 * mZ = A - 3 := by
    have := Int.ediv_mul_cancel hAdiv
    linarith
  have hn2 : 2 * nZ = B - 3 := by
    have := Int.ediv_mul_cancel hBdiv
    linarith
  have hAge : (6 : ℤ) ≤ A := by
    have hy4 : (4 : ℤ) ≤ s.y := by
      rw [hy_form]
      have : (2 : ℤ) ≤ a.x := by omega
      have : (1 : ℤ) ≤ a.y := by omega
      nlinarith
    have hx2 : (2 : ℤ) ≤ s.x := by
      have : (1 : ℤ) < s.x ^ 2 := by
        rw [prop_x]
        have : 0 < (N : ℤ) * s.y ^ 2 := mul_pos hpos (sq_pos_of_pos hsy)
        linarith
      nlinarith [hsx]
    nlinarith [hpos, hsy]
  have hBge : (6 : ℤ) ≤ B := by
    have hy4 : (4 : ℤ) ≤ s.y := by
      rw [hy_form]
      nlinarith [hax, hay]
    have hx2 : (2 : ℤ) ≤ s.x := by
      have : (1 : ℤ) < s.x ^ 2 := by
        rw [prop_x]
        have : 0 < (N : ℤ) * s.y ^ 2 := mul_pos hpos (sq_pos_of_pos hsy)
        linarith
      nlinarith [hsx]
    nlinarith
  have hm0 : 0 ≤ mZ := by nlinarith [hm2, hAge]
  have hn0 : 0 ≤ nZ := by nlinarith [hn2, hBge]
  have hgap : nZ + 2 ≤ mZ := by
    have hdiff : 2 * (mZ - nZ) = ((N : ℤ) - 1) * s.y := by
      have hAB : A - B = ((N : ℤ) - 1) * s.y := by
        simp only [A, B]
        ring
      linarith
    rw [hy_form] at hdiff
    have hmul : mZ - nZ = ((N : ℤ) - 1) * a.x * a.y := by
      have hfour : ((N : ℤ) - 1) * (2 * (a.x * a.y)) = 2 * (((N : ℤ) - 1) * a.x * a.y) := by
        ring
      have : 2 * (mZ - nZ) = 2 * (((N : ℤ) - 1) * a.x * a.y) := by rw [hdiff, hfour]
      exact Int.eq_of_mul_eq_mul_left (by decide : (2 : ℤ) ≠ 0) this
    have hbig : (2 : ℤ) ≤ ((N : ℤ) - 1) * a.x * a.y := by
      have hN1 : (1 : ℤ) ≤ (N : ℤ) - 1 := by omega
      have hx2 : (2 : ℤ) ≤ a.x := by omega
      have hy1 : (1 : ℤ) ≤ a.y := by omega
      nlinarith
    linarith
  let m : ℕ := mZ.toNat
  let n : ℕ := nZ.toNat
  have hmcast : (m : ℤ) = mZ := Int.toNat_of_nonneg hm0
  have hncast : (n : ℤ) = nZ := Int.toNat_of_nonneg hn0
  have hmn : n + 2 ≤ m := by
    have hcast : (n : ℤ) + 2 ≤ m := by
      rw [hncast, hmcast]
      exact hgap
    exact (Nat.cast_le (α := ℤ)).mp hcast
  have hprod : (m + 1) * (m + 2) = N * ((n + 1) * (n + 2)) := by
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [hmcast, hncast]
    have hAm : 4 * ((mZ + 1) * (mZ + 2)) = A ^ 2 - 1 := by
      have hA : A = 2 * mZ + 3 := by linarith
      rw [hA]
      ring
    have hBn : 4 * ((nZ + 1) * (nZ + 2)) = B ^ 2 - 1 := by
      have hB : B = 2 * nZ + 3 := by linarith
      rw [hB]
      ring
    have hm4 : (mZ + 1) * (mZ + 2) = (A ^ 2 - 1) / 4 :=
      Int.eq_ediv_of_mul_eq_right (by decide) hAm
    have hn4 : (nZ + 1) * (nZ + 2) = (B ^ 2 - 1) / 4 :=
      Int.eq_ediv_of_mul_eq_right (by decide) hBn
    have h4B : 4 ∣ B ^ 2 - 1 := ⟨(nZ + 1) * (nZ + 2), by
      have hB : B = 2 * nZ + 3 := by linarith
      rw [hB]
      ring⟩
    have hassoc : (A ^ 2 - 1) / 4 = (N : ℤ) * ((B ^ 2 - 1) / 4) := by
      rw [hdiv_eq]
      exact Int.mul_ediv_assoc (N : ℤ) h4B
    rw [hm4, hn4, hassoc]
  refine ⟨2, by omega, n, m, hmn, ?_⟩
  simp only [prod_Icc_succ_top (by decide : 1 ≤ 2), Icc_self, prod_singleton]
  rw [eq_div_iff (by positivity : (↑((n + 1) * (n + (1 + 1))) : ℚ) ≠ 0)]
  exact_mod_cast hprod.symm
