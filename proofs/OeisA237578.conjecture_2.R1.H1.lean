import OMAReductions.R_OeisA237578_conjecture_2_R1

/-!
π(k n) is prime for exactly one k below n, at n = 5, 8 and 13.
-/

theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl
  · decide
  · decide
  · set_option maxRecDepth 20000 in decide
