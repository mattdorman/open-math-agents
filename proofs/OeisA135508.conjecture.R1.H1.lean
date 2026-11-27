import OMAReductions.R_OeisA135508_conjecture_R1
import Mathlib.Data.Nat.GCD.Basic

-- Step OeisA135508.conjecture.R1.H1
-- Credit: @mattdorman
-- x 4 is divisible by 3, and x (n+1) = 2 x n + lcm(x n, n+1) preserves that.

open OeisA135508

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  refine Nat.le_induction ?base ?step n hn
  · decide
  · intro n _ ih
    have hx : x (n + 1) = 2 * x n + Nat.lcm (x n) (n + 1) := by
      cases n with
      | zero => omega
      | succ _ => rfl
    rw [hx]
    have h2 : 3 ∣ 2 * x n := dvd_mul_of_dvd_right ih 2
    have hl : 3 ∣ Nat.lcm (x n) (n + 1) := dvd_trans ih (Nat.dvd_lcm_left _ _)
    exact Nat.dvd_add h2 hl
