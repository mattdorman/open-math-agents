import OMAReductions.R_OeisA182126_conjecture3_R1
import Mathlib.Data.Nat.Nth

/-!
Among the first 61 terms, the only prime values are 2, 7, 11, 13 and 29.
Each term is a product of two consecutive primes modulo the next, read off
the first 63 primes.
-/

open Nat

namespace A182

def small (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ d ∈ List.range 20, 2 ≤ d → d * d ≤ n → n % d ≠ 0

instance : DecidablePred small := by
  unfold small
  infer_instance

lemma prime_iff_small (n : ℕ) (hn : n < 400) : Nat.Prime n ↔ small n := by
  rw [prime_def_le_sqrt]
  constructor
  · intro ⟨h2, H⟩
    refine ⟨h2, ?_⟩
    intro d _ hd hdd hmod
    exact H d hd (le_sqrt.mpr hdd) (dvd_of_mod_eq_zero hmod)
  · intro ⟨h2, H⟩
    refine ⟨h2, ?_⟩
    intro m hm hms hdvd
    have hmm : m * m ≤ n := le_sqrt.mp hms
    have hm20 : m < 20 := by
      by_contra hc
      have hc' : 20 ≤ m := by omega
      have : 400 ≤ m * m := Nat.mul_le_mul hc' hc'
      omega
    exact H m (List.mem_range.mpr hm20) hm hmm (mod_eq_zero_of_dvd hdvd)

lemma count_congr_lt {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] (n : ℕ)
    (h : ∀ k < n, p k ↔ q k) : count p n = count q n := by
  rw [count_eq_card_filter_range, count_eq_card_filter_range]
  congr 1
  exact Finset.filter_congr fun k hk => h k (Finset.mem_range.mp hk)

def primeAt : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307]

lemma nth_prime (i : ℕ) (hi : i < 63) : nth Nat.Prime i = primeAt.getD i 0 := by
  have hsmall : small (primeAt.getD i 0) := by interval_cases i <;> decide
  have hcount : count small (primeAt.getD i 0) = i := by
    interval_cases i <;>
      set_option maxHeartbeats 2000000 in
        set_option maxRecDepth 100000 in
          decide +kernel
  have hlt : primeAt.getD i 0 < 400 := by interval_cases i <;> decide
  have hprime : Nat.Prime (primeAt.getD i 0) := (prime_iff_small _ hlt).mpr hsmall
  have hcountP : count Nat.Prime (primeAt.getD i 0) = i :=
    (count_congr_lt _ fun k hk => prime_iff_small k (by omega)).trans hcount
  exact (congrArg (nth Nat.Prime) hcountP.symm).trans (nth_count hprime)

end A182

open A182 OeisA182126

theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 := by
  intro n hn hle hp
  have hi1 : n - 1 < 63 := by omega
  have hi2 : n < 63 := by omega
  have hi3 : n + 1 < 63 := by omega
  have h1 : n + 1 - 1 = n := by omega
  have h2 : n + 2 - 1 = n + 1 := by omega
  have hval : a n = (primeAt.getD (n - 1) 0 * primeAt.getD n 0) % primeAt.getD (n + 1) 0 := by
    unfold a prime
    rw [if_neg (by omega : n ≠ 0), h1, h2, nth_prime (n - 1) hi1, nth_prime n hi2,
      nth_prime (n + 1) hi3]
  interval_cases n
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · rw [hval]; set_option maxRecDepth 10000 in decide
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · rw [hval]; set_option maxRecDepth 10000 in decide
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · rw [hval]; set_option maxRecDepth 10000 in decide
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · rw [hval]; set_option maxRecDepth 10000 in decide
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · rw [hval]; set_option maxRecDepth 10000 in decide
  · rw [hval]; set_option maxRecDepth 10000 in decide
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · exact absurd hp (by rw [hval]; set_option maxRecDepth 10000 in decide)
  · rw [hval]; set_option maxRecDepth 10000 in decide
