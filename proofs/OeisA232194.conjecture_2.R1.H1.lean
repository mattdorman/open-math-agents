import OMAReductions.R_OeisA232194_conjecture_2_R1

/-!
Each of 3, 4, 6, 20 and 24 has exactly one way to write n = x + y
with nx + y and ny - x both prime. The count is a finite primality check.
-/

theorem OMA.solution : OMA.R_OeisA232194_conjecture_2_R1.H1 := by
  intro n hn
  set_option maxRecDepth 10000 in
  fin_cases hn <;> decide
