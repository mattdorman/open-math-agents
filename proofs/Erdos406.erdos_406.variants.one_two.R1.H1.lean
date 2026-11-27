import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1

/-!
No power 2 ^ k with 15 < k ≤ 1000 has only digits 1 and 2 in base 3.
-/

open Nat

set_option maxHeartbeats 500000000 in
theorem OMA.solution : OMA.R_Erdos406_erdos_406_variants_one_two_R1.H1 := by
  intro k hk hle
  interval_cases k <;>
    set_option maxHeartbeats 20000000 in
      set_option maxRecDepth 200000 in
        decide
