import OMAReductions.R_OeisA234246_conjecture_2_R1

/-!
Each of the nine indices has exactly one admissible k. The count is a finite
totient-and-square check, decided in the kernel.
-/

theorem OMA.solution : OMA.R_OeisA234246_conjecture_2_R1.H1 := by
  intro n hn
  set_option maxRecDepth 10000 in
  fin_cases hn <;> decide
