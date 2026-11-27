import OMAReductions.R_SternPrime_isSternPrime_iff_R1

/-!
The eight listed values are Stern primes by the finite verification already in the
SternPrime module. Membership in the set and membership in that list are the same
disjunction.
-/

theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  intro q hq
  apply SternPrime.isSternPrime_known_examples
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons, List.mem_nil_iff] using hq
