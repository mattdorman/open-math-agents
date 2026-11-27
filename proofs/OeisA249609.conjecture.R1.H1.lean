import OMAReductions.R_OeisA249609_conjecture_R1

/-!
Rows 0, 1, 2, 7 and 8 of Pascal's triangle have no evil binomial coefficient.
Each row is a finite parity-of-bits check.
-/

theorem OMA.solution : OMA.R_OeisA249609_conjecture_R1.H1 := by
  intro n hn
  fin_cases hn <;> decide
