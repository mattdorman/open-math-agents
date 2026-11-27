import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1

-- Step SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1.H1
-- Credit: @mattdorman
-- A cube is 0, 1, or -1 mod 9, so a sum of three cubes is never 4 or 5 mod 9.

theorem OMA.solution : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1.H1 :=
  SumOfThreeCubes.mod_9_of_isSumOfThreeCubes
