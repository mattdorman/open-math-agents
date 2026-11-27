import OMAReductions.R_OeisA108129_conjecture_R1
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
509203 is a Riesel number. Every term 509203 * 2^m - 1 with m positive is
divisible by one of 3, 5, 7, 13, 17, 241.
-/

-- Credit: @mattdorman


open Nat

lemma zmod_period {k p a q t : ℕ} [NeZero p]
    (ha : (k * 2 ^ a : ZMod p) = 1) (hq : ((2 ^ q : ℕ) : ZMod p) = 1) :
    (k * 2 ^ (q * t + a) : ZMod p) = 1 := by
  have hq' : (2 : ZMod p) ^ q = 1 := by simpa [Nat.cast_pow] using hq
  have ha' : (k : ZMod p) * (2 : ZMod p) ^ a = 1 := by
    simpa [Nat.cast_mul, Nat.cast_pow] using ha
  calc
    (k * 2 ^ (q * t + a) : ZMod p)
        = (k : ZMod p) * (2 : ZMod p) ^ (q * t + a) := by
          rfl
    _ = (k : ZMod p) * ((2 : ZMod p) ^ q) ^ t * (2 : ZMod p) ^ a := by
          rw [pow_add, pow_mul]
          ring
    _ = (k : ZMod p) * (2 : ZMod p) ^ a := by
          rw [hq', one_pow, mul_one]
    _ = 1 := ha'

lemma mod_from_24 {m q a r : ℕ} (h : m % 24 = r) (hq : q ∣ 24) (hr : r % q = a) :
    m % q = a := by
  have hm : m = 24 * (m / 24) + r := by
    simpa [h] using (Nat.div_add_mod m 24).symm
  have h24 : 24 = q * (24 / q) := (Nat.mul_div_cancel' hq).symm
  have hcong : m ≡ r [MOD q] := by
    rw [hm, h24, mul_assoc, add_comm]
    exact (Nat.add_modulus_mul_modEq_iff).2 Nat.ModEq.rfl
  change m % q = a
  rw [hcong, hr]

lemma not_prime_cover (m : ℕ) (hm : m ≠ 0) {p a q : ℕ} (hp : p.Prime)
    (hr : m % q = a) (_hq : 0 < q) [NeZero p] (ha : (509203 * 2 ^ a : ZMod p) = 1)
    (hper : ((2 ^ q : ℕ) : ZMod p) = 1) (hsmall : p < 509203 * 2 - 1) :
    ¬ (509203 * 2 ^ m - 1).Prime := by
  have hsplit : m = q * (m / q) + a := by
    have h := Nat.div_add_mod m q
    rw [hr] at h
    exact h.symm
  have hone : (509203 * 2 ^ m : ZMod p) = 1 := by
    rw [hsplit]
    exact zmod_period ha hper
  have hpos : 1 ≤ 509203 * 2 ^ m := by
    have : 0 < 509203 * 2 ^ m := by positivity
    omega
  have hdvd : p ∣ 509203 * 2 ^ m - 1 := by
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    rw [Nat.cast_sub hpos]
    simp [hone]
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  have hpow : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm1
  have hmul : 509203 * 2 ^ 1 ≤ 509203 * 2 ^ m := Nat.mul_le_mul_left _ hpow
  have hsub : 509203 * 2 - 1 ≤ 509203 * 2 ^ m - 1 := Nat.sub_le_sub_right hmul 1
  have hlt : p < 509203 * 2 ^ m - 1 := lt_of_lt_of_le hsmall hsub
  intro hprime
  rcases hdvd with ⟨c, hc⟩
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, mul_one] at hc
    omega
  have hc0 : c ≠ 0 := by
    intro h
    simp [h] at hc
    omega
  exact Nat.not_prime_mul hp.ne_one hc1 (hc ▸ hprime)

lemma riesel_not_prime (m : ℕ) (hm : m ≠ 0) : ¬ (509203 * 2 ^ m - 1).Prime := by
  have hlt : m % 24 < 24 := Nat.mod_lt _ (by decide)
  obtain ⟨r, hr24, hrlt⟩ : ∃ r, m % 24 = r ∧ r < 24 := ⟨m % 24, rfl, hlt⟩
  interval_cases r
  · have hmod : m % 2 = 0 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (3 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 4 = 1 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (5 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 2 = 0 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (3 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 24 = 3 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (241 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 2 = 0 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (3 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 4 = 1 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (5 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 2 = 0 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (3 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 12 = 7 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (13 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 2 = 0 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (3 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 4 = 1 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (5 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 2 = 0 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (3 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 3 = 2 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (7 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 2 = 0 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (3 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 4 = 1 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (5 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 2 = 0 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (3 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 8 = 7 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (17 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 2 = 0 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (3 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 4 = 1 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (5 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 2 = 0 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (3 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 12 = 7 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (13 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 2 = 0 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (3 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 4 = 1 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (5 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 2 = 0 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (3 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)
  · have hmod : m % 3 = 2 := mod_from_24 hr24 (by decide) (by decide)
    exact not_prime_cover m hm (by norm_num : (7 : ℕ).Prime) hmod (by decide) (by decide) (by decide)
      (by decide)

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  classical
  show OeisA108129.a 254602 = -1
  rw [OeisA108129.a]
  have hn : (254602 : ℕ) ≠ 0 := by decide
  rw [if_neg hn]
  have hex : ¬ ∃ m, m ≠ 0 ∧ ((2 * 254602 - 1) * 2 ^ m - 1).Prime := by
    intro ⟨m, hm, hp⟩
    have hk : 2 * 254602 - 1 = 509203 := by decide
    rw [hk] at hp
    exact riesel_not_prime m hm hp
  rw [dif_neg hex]
