import OMAReductions.R_Erdos399_erdos_399_variants_sum_two_squares_R1

/-!
For each n from 7 to 100, one prime q ≡ 3 mod 4 satisfies q ≤ n < 2 q.
The eight primes 7, 11, 19, 23, 31, 43, 47 and 59 cover the whole interval.
-/

theorem OMA.solution :
    OMA.R_Erdos399_erdos_399_variants_sum_two_squares_R1.H1 := by
  intro n hn hle
  let q : ℕ :=
    if n < 14 then 7
    else if n < 22 then 11
    else if n < 38 then 19
    else if n < 46 then 23
    else if n < 62 then 31
    else if n < 86 then 43
    else if n < 94 then 47
    else 59
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  all_goals
    dsimp [q]
    set_option maxRecDepth 10000 in
    interval_cases n <;> decide
