import OMAReductions.R_Erdos479_erdos_479_R1
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Ring

/-!
Known cases of Erdős 479. Powers of two give the residue 0, powers of three give -1,
the recurrence n ↦ 2 ^ n + 2 gives -2, and primes in a totient progression give every
positive power of two.
-/

open Nat

lemma pow_modEq_of_period {a d lam e f : ℕ} (hbase : a ^ lam ≡ 1 [MOD d]) (hf : f ≤ e)
    (hdvd : lam ∣ e - f) : a ^ e ≡ a ^ f [MOD d] := by
  obtain ⟨t, ht⟩ := hdvd
  have he : e = f + lam * t := by
    have := (Nat.sub_eq_iff_eq_add hf).mp ht
    rw [this, Nat.add_comm]
  rw [he, pow_add, pow_mul]
  have hpow : (a ^ lam) ^ t ≡ 1 [MOD d] := by simpa using hbase.pow t
  have : a ^ f * (a ^ lam) ^ t ≡ a ^ f * 1 [MOD d] := hpow.mul_left (a ^ f)
  simpa using this

lemma zModEq_neg_of_dvd_add (n c : ℕ) (h : n ∣ 2 ^ n + c) :
    (2 : ℤ) ^ n ≡ - (c : ℤ) [ZMOD (n : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  have : - (c : ℤ) - (2 : ℤ) ^ n = - ((2 ^ n + c : ℕ) : ℤ) := by
    push_cast
    ring
  rw [this, Int.dvd_neg]
  exact Int.natCast_dvd_natCast.mpr h

lemma zModEq_of_dvd_sub (n a : ℕ) (ha : a ≤ 2 ^ n) (h : n ∣ 2 ^ n - a) :
    (2 : ℤ) ^ n ≡ (a : ℤ) [ZMOD (n : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  have : (a : ℤ) - (2 : ℤ) ^ n = - ((2 ^ n - a : ℕ) : ℤ) := by
    rw [Nat.cast_sub ha]
    push_cast
    ring
  rw [this, Int.dvd_neg]
  exact Int.natCast_dvd_natCast.mpr h

lemma sq_pred_one (d : ℕ) (hd : 2 ≤ d) : (d - 1) ^ 2 ≡ 1 [MOD d] := by
  have h1 : 1 ≤ (d - 1) ^ 2 := Nat.one_le_pow 2 (d - 1) (by omega)
  have hsub : (d - 1) ^ 2 - 1 = d * (d - 2) := by
    apply Nat.cast_injective (R := ℤ)
    have h1d : ((d - 1 : ℕ) : ℤ) = d - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      simp
    have h2d : ((d - 2 : ℕ) : ℤ) = d - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ d)]
      simp
    rw [Nat.cast_sub h1, Nat.cast_mul, Nat.cast_pow, h1d, h2d]
    ring
  have hdiv : d ∣ (d - 1) ^ 2 - 1 := by
    rw [hsub]
    exact dvd_mul_right _ _
  exact ((Nat.modEq_iff_dvd' h1).mpr hdiv).symm

lemma two_period (n : ℕ) (_hn : 1 ≤ n) :
    2 ^ (2 * n) ≡ 1 [MOD (2 ^ n + 1)] := by
  have hd : 2 ≤ 2 ^ n + 1 := by
    have : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
    omega
  have hsub : 2 ^ n = 2 ^ n + 1 - 1 := by omega
  have hpow : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by ac_rfl, pow_mul]
  rw [hpow, hsub]
  exact sq_pred_one _ hd

lemma cube_add_one (x : ℕ) : (x + 1) * (x ^ 2 - x + 1) = x ^ 3 + 1 := by
  have hle : x ≤ x ^ 2 := by
    cases x with
    | zero => simp
    | succ y =>
      rw [pow_two]
      exact Nat.le_mul_of_pos_left (y + 1) (Nat.succ_pos y)
  apply Nat.cast_injective (R := ℤ)
  have hright : ((x ^ 2 - x + 1 : ℕ) : ℤ) = (x ^ 2 - x : ℕ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have hrhs : ((x ^ 3 + 1 : ℕ) : ℤ) = (x : ℤ) ^ 3 + 1 := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  rw [Nat.cast_mul, Nat.cast_add, hright, Nat.cast_sub hle, Nat.cast_pow, hrhs]
  ring

lemma three_pow_odd (b : ℕ) : Odd (3 ^ b) := by
  induction b with
  | zero => decide
  | succ b ih =>
    rw [pow_succ]
    exact ih.mul (by decide)

lemma three_pow_dvd (b : ℕ) : 3 ^ (b + 1) ∣ 2 ^ (3 ^ b) + 1 := by
  induction b with
  | zero => decide
  | succ b ih =>
    set x := 2 ^ (3 ^ b)
    have hxpow : 2 ^ (3 ^ (b + 1)) = x ^ 3 := by
      have : 3 ^ (b + 1) = 3 ^ b * 3 := by rw [pow_succ]
      rw [this, pow_mul]
    have hle : x ≤ x ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_left x (Nat.one_le_pow _ _ (by decide))
    rw [hxpow, ← cube_add_one x]
    refine mul_dvd_mul ih ?_
    rw [← ZMod.natCast_eq_zero_iff]
    have hx : (x : ZMod 3) = -1 := by
      have : (x : ZMod 3) = (2 : ZMod 3) ^ (3 ^ b) := by simp [x, Nat.cast_pow]
      rw [this, show (2 : ZMod 3) = -1 by decide, (three_pow_odd b).neg_one_pow]
    rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one, hx]
    decide

def negTwoChain : ℕ → ℕ
  | 0 => 2
  | j + 1 => 2 ^ negTwoChain j + 2

lemma mod_four_of_two_not_four (n : ℕ) (h2 : 2 ∣ n) (h4 : ¬ 4 ∣ n) : n % 4 = 2 := by
  have hlt : n % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 4
  · exact absurd (Nat.dvd_of_mod_eq_zero h) h4
  · have hmod : n % 2 = 1 := by
      have : (n % 4) % 2 = n % 2 := Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)
      omega
    exact absurd (Nat.mod_eq_zero_of_dvd h2) (by omega)
  · rfl
  · have hmod : n % 2 = 1 := by
      have : (n % 4) % 2 = n % 2 := Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)
      omega
    exact absurd (Nat.mod_eq_zero_of_dvd h2) (by omega)

lemma four_dvd_shift' (n : ℕ) (hn : 2 ≤ n) (h2 : 2 ∣ n) (h4 : ¬ 4 ∣ n) :
    4 ∣ 2 ^ n + 2 - n := by
  have hmod := mod_four_of_two_not_four n h2 h4
  have hn4 : n = 4 * (n / 4) + 2 := by
    have := Nat.div_add_mod n 4
    rw [hmod] at this
    exact this.symm
  have hsub : n - 2 = 4 * (n / 4) := by omega
  have hleN : n ≤ 2 ^ n := (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hA : n ≤ 2 ^ n + 2 := by omega
  have hB : n - 2 ≤ 2 ^ n := by omega
  have hS : 2 ^ n + 2 - n = 2 ^ n - (n - 2) := by
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_sub hA, Nat.cast_sub hB, Nat.cast_sub hn]
    push_cast
    ring
  have h4pow : 4 ∣ 2 ^ n := pow_dvd_pow 2 hn
  have h4n : 4 ∣ n - 2 := by
    rw [hsub]
    exact dvd_mul_right _ _
  rw [hS]
  exact Nat.dvd_sub h4pow h4n

def Good (n : ℕ) : Prop :=
  2 ≤ n ∧ 2 ∣ n ∧ ¬ 4 ∣ n ∧ n ∣ 2 ^ n + 2 ∧ 2 * (n - 1) ∣ 2 ^ n + 2 - n

lemma two_n_dvd_shift (n : ℕ) (hn : 2 ≤ n) (h2 : 2 ∣ n) (h4 : ¬ 4 ∣ n)
    (hP : n ∣ 2 ^ n + 2) : 2 * n ∣ 2 ^ n + 2 - n := by
  have hle : n ≤ 2 ^ n + 2 := by
    have : n ≤ 2 ^ n := (Nat.lt_pow_self (by decide : 1 < 2)).le
    omega
  have hS : n ∣ 2 ^ n + 2 - n := Nat.dvd_sub hP (dvd_refl n)
  have h4S : 4 ∣ 2 ^ n + 2 - n := four_dvd_shift' n hn h2 h4
  obtain ⟨t, ht⟩ := h2
  have hnot : ¬ 2 ∣ t := by
    intro ht2
    obtain ⟨k, hk⟩ := ht2
    have : 4 ∣ n := by
      refine ⟨k, ?_⟩
      rw [ht, hk]
      ac_rfl
    exact h4 this
  obtain ⟨r, hr⟩ := hS
  have h2r : 2 ∣ r := by
    have h4r : 4 ∣ 2 * (t * r) := by
      rw [← Nat.mul_assoc, ← ht, ← hr]
      exact h4S
    have h2tr : 2 ∣ t * r := Nat.dvd_of_mul_dvd_mul_left (by decide) h4r
    exact (Nat.prime_two.dvd_mul.mp h2tr).resolve_left hnot
  obtain ⟨s, hs⟩ := h2r
  refine ⟨s, ?_⟩
  rw [hr, ht, hs]
  ac_rfl

lemma good_two : Good 2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

lemma good_succ {n : ℕ} (hg : Good n) : Good (2 ^ n + 2) := by
  obtain ⟨hn, h2, h4, hP, hQ⟩ := hg
  set m := 2 ^ n + 2
  set d := 2 ^ (n - 1) + 1
  have hn1 : (n - 1) + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hm : m = 2 * d := by
    calc
      m = 2 ^ n + 2 := rfl
      _ = 2 ^ ((n - 1) + 1) + 2 := by rw [hn1]
      _ = 2 * 2 ^ (n - 1) + 2 := by rw [Nat.pow_succ']
      _ = 2 * (2 ^ (n - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = 2 * d := rfl
  have hPm : m ∣ 2 ^ m + 2 := by
    have hper : 2 ^ (2 * (n - 1)) ≡ 1 [MOD d] := by
      simpa [d] using two_period (n - 1) (by omega)
    have hf : n - 1 ≤ 2 ^ n + 1 := by
      have : n - 1 ≤ n := by omega
      have : n ≤ 2 ^ n := (Nat.lt_pow_self (by decide : 1 < 2)).le
      omega
    have hdiff : 2 ^ n + 1 - (n - 1) = 2 ^ n + 2 - n := by
      have hA : n - 1 ≤ 2 ^ n + 1 := hf
      have hB : n ≤ 2 ^ n + 2 := by
        have : n ≤ 2 ^ n := (Nat.lt_pow_self (by decide : 1 < 2)).le
        omega
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub hA, Nat.cast_sub hB, Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast
      ring
    have hdvd : 2 * (n - 1) ∣ 2 ^ n + 1 - (n - 1) := by rwa [hdiff]
    have hcong := pow_modEq_of_period hper hf hdvd
    have hneg : 2 ^ (n - 1) = d - 1 := by
      have : d = 2 ^ (n - 1) + 1 := rfl
      omega
    have hsum : 2 ^ (2 ^ n + 1) + 1 ≡ 0 [MOD d] := by
      have h1 : 2 ^ (2 ^ n + 1) ≡ d - 1 [MOD d] := by
        rw [← hneg]
        exact hcong
      have h2m : 2 ^ (2 ^ n + 1) + 1 ≡ (d - 1) + 1 [MOD d] := h1.add (Nat.ModEq.refl 1)
      have : (d - 1) + 1 = d := by omega
      rw [this] at h2m
      exact h2m.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl d))
    have hzero : d ∣ 2 ^ (2 ^ n + 1) + 1 := (Nat.modEq_zero_iff_dvd).mp hsum
    have hfac : 2 ^ m + 2 = 2 * (2 ^ (2 ^ n + 1) + 1) := by
      have hm1 : m = (2 ^ n + 1) + 1 := by
        have : (2 ^ n + 1) + 1 = 2 ^ n + 2 := by
          rw [Nat.add_assoc]
        simpa [m] using this.symm
      calc
        2 ^ m + 2 = 2 ^ ((2 ^ n + 1) + 1) + 2 := by rw [hm1]
        _ = 2 * 2 ^ (2 ^ n + 1) + 2 := by rw [Nat.pow_succ']
        _ = 2 * (2 ^ (2 ^ n + 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
    rw [hfac, hm]
    exact mul_dvd_mul_left 2 hzero
  have h24 : 2 ∣ m ∧ ¬ 4 ∣ m := by
    rw [hm]
    refine ⟨dvd_mul_right _ _, ?_⟩
    intro hmul
    have heven : Even (2 ^ (n - 1)) :=
      even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : n - 1 ≠ 0))
    have hodd : Odd d := by simpa [d] using heven.add_one
    have h2d : 2 ∣ d :=
      Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) (by simpa [Nat.mul_assoc] using hmul)
    exact (not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2d)
  have hQn : 2 * n ∣ 2 ^ n + 2 - n := two_n_dvd_shift n hn h2 h4 hP
  have hQm : 2 * (m - 1) ∣ 2 ^ m + 2 - m := by
    have hm1 : m - 1 = 2 ^ n + 1 := by simp [m]
    have hper : 2 ^ (2 * n) ≡ 1 [MOD (2 ^ n + 1)] := two_period n (by omega)
    obtain ⟨t, ht⟩ := hQn
    have hE : 2 ^ (2 ^ n + 2 - n) ≡ 1 [MOD (2 ^ n + 1)] := by
      rw [ht, pow_mul]
      simpa using hper.pow t
    have hone : 1 ≤ 2 ^ (2 ^ n + 2 - n) := Nat.one_le_pow _ _ (by decide)
    have hdvdE : 2 ^ n + 1 ∣ 2 ^ (2 ^ n + 2 - n) - 1 := by
      have hsym : 1 ≡ 2 ^ (2 ^ n + 2 - n) [MOD (2 ^ n + 1)] := hE.symm
      exact (Nat.modEq_iff_dvd' hone).mp hsym
    have hprod : 2 ^ m + 2 - m = 2 ^ n * (2 ^ (2 ^ n + 2 - n) - 1) := by
      have hC : n ≤ 2 ^ n + 2 := by
        have : n ≤ 2 ^ n := (Nat.lt_pow_self (by decide : 1 < 2)).le
        omega
      have hmE : m = n + (2 ^ n + 2 - n) := by
        simp [m]
        omega
      have hpow : 2 ^ m = 2 ^ n * 2 ^ (2 ^ n + 2 - n) := by
        rw [hmE, pow_add]
      have hsub : 2 ^ m + 2 - m = 2 ^ m - 2 ^ n := by
        simp [m]
      rw [hsub, hpow]
      have hmul := Nat.mul_sub (2 ^ n) (2 ^ (2 ^ n + 2 - n)) 1
      simpa [Nat.mul_one] using hmul.symm
    rw [hm1, hprod]
    have hcop : Nat.Coprime 2 (2 ^ n + 1) := by
      have hodd : Odd (2 ^ n + 1) :=
        (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : n ≠ 0))).add_one
      rw [Nat.coprime_comm, Nat.coprime_two_right]
      exact hodd
    have h2d : 2 ∣ 2 ^ n * (2 ^ (2 ^ n + 2 - n) - 1) :=
      dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega : n ≠ 0)) _
    have hodd : 2 ^ n + 1 ∣ 2 ^ n * (2 ^ (2 ^ n + 2 - n) - 1) :=
      dvd_mul_of_dvd_right hdvdE _
    exact hcop.mul_dvd_of_dvd_of_dvd h2d hodd
  exact ⟨by omega, h24.1, h24.2, hPm, hQm⟩

lemma negTwoChain_good (j : ℕ) : Good (negTwoChain j) := by
  induction j with
  | zero => simpa [negTwoChain] using good_two
  | succ j ih => simpa [negTwoChain] using good_succ ih

lemma infinite_zero :
    {n : ℕ | (2 : ℤ) ^ n ≡ (0 : ℤ) [ZMOD (n : ℤ)]}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  refine ⟨2 ^ (N + 1), ?_, ?_⟩
  · have hdv : 2 ^ (N + 1) ∣ 2 ^ (2 ^ (N + 1)) :=
      pow_dvd_pow 2 (Nat.lt_pow_self (by decide : 1 < 2)).le
    simpa using zModEq_neg_of_dvd_add (2 ^ (N + 1)) 0 hdv
  · have : N + 1 < 2 ^ (N + 1) := Nat.lt_pow_self (by decide : 1 < 2)
    omega

lemma infinite_neg_one :
    {n : ℕ | (2 : ℤ) ^ n ≡ (-1 : ℤ) [ZMOD (n : ℤ)]}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  refine ⟨3 ^ (N + 1), ?_, ?_⟩
  · have hdv : 3 ^ (N + 1) ∣ 2 ^ (3 ^ (N + 1)) + 1 :=
      (pow_dvd_pow 3 (Nat.le_succ (N + 1))).trans (three_pow_dvd (N + 1))
    exact zModEq_neg_of_dvd_add _ 1 hdv
  · have : N + 1 < 3 ^ (N + 1) := Nat.lt_pow_self (by decide : 1 < 3)
    omega

lemma infinite_neg_two :
    {n : ℕ | (2 : ℤ) ^ n ≡ (-2 : ℤ) [ZMOD (n : ℤ)]}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  have hge : ∀ k, k + 2 ≤ negTwoChain k := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hpow : negTwoChain k ≤ 2 ^ negTwoChain k :=
        (Nat.lt_pow_self (by decide : 1 < 2)).le
      have : k + 1 + 2 ≤ 2 ^ negTwoChain k + 2 := by omega
      simpa [negTwoChain] using this
  refine ⟨negTwoChain (N + 1), ?_, ?_⟩
  · exact zModEq_neg_of_dvd_add _ 2 (negTwoChain_good (N + 1)).2.2.2.1
  · have : N + 1 + 2 ≤ negTwoChain (N + 1) := hge (N + 1)
    omega

lemma infinite_two_pow (i : ℕ) (hi : 1 ≤ i) :
    {n : ℕ | (2 : ℤ) ^ n ≡ ((2 ^ i : ℕ) : ℤ) [ZMOD (n : ℤ)]}.Infinite := by
  set M := ordCompl[2] i
  have hMpos : 0 < M := ordCompl_pos 2 (by omega)
  have hφ : Nat.totient M ≠ 0 := (Nat.totient_pos.mpr hMpos).ne'
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨p, hpN, hpp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N (i + 2)) (q := Nat.totient M) (a := 1) hφ
      (Nat.coprime_one_left _)
  have hpgt : i + 2 < p := lt_of_le_of_lt (le_max_right _ _) hpN
  have hNlt : N < p := lt_of_le_of_lt (le_max_left _ _) hpN
  have hcopi : p.Coprime i := by
    rw [hpp.coprime_iff_not_dvd]
    intro hdiv
    exact absurd (le_of_dvd (by omega) hdiv) (by omega)
  have hp1 : 1 ≤ p := hpp.pos
  have hφdvd : Nat.totient M ∣ p - 1 := by
    have hsym : 1 ≡ p [MOD Nat.totient M] := hmod.symm
    have hle : 1 ≤ p := hp1
    exact (Nat.modEq_iff_dvd' hle).mp hsym
  obtain ⟨t, ht⟩ := hφdvd
  have heuler : 2 ^ Nat.totient M ≡ 1 [MOD M] :=
    Nat.ModEq.pow_totient (coprime_ordCompl (by decide : (2 : ℕ).Prime) (by omega))
  have hper : 2 ^ (p - 1) ≡ 1 [MOD M] := by
    rw [ht, pow_mul]
    simpa using heuler.pow t
  have hmul : 2 ^ (i * (p - 1)) ≡ 1 [MOD M] := by
    rw [mul_comm, pow_mul]
    simpa using hper.pow i
  have hone : 1 ≤ 2 ^ (i * (p - 1)) := Nat.one_le_pow _ _ (by decide)
  have hMdvd : M ∣ 2 ^ (i * (p - 1)) - 1 :=
    (Nat.modEq_iff_dvd' hone).mp hmul.symm
  have hv : i.factorization 2 ≤ i := by
    have hord : 2 ^ i.factorization 2 ∣ i := ordProj_dvd i 2
    have hle2 : 2 ^ i.factorization 2 ≤ i := le_of_dvd (by omega) hord
    exact ((Nat.lt_pow_self (by decide : 1 < 2)).le).trans hle2
  have h2i : 2 ^ i.factorization 2 ∣ 2 ^ i := pow_dvd_pow 2 hv
  have hexp : i * p = i + i * (p - 1) := by
    calc
      i * p = i * ((p - 1) + 1) := by rw [Nat.sub_add_cancel hp1]
      _ = i * (p - 1) + i := by rw [Nat.mul_add, Nat.mul_one]
      _ = i + i * (p - 1) := by ac_rfl
  have hsplit : 2 ^ (i * p) - 2 ^ i = 2 ^ i * (2 ^ (i * (p - 1)) - 1) := by
    have hpow : 2 ^ (i * p) = 2 ^ i * 2 ^ (i * (p - 1)) := by
      rw [hexp, pow_add]
    have hmul := (Nat.mul_sub (2 ^ i) (2 ^ (i * (p - 1))) 1).symm
    rw [hpow]
    simpa [Nat.mul_one] using hmul
  have hiDvd : i ∣ 2 ^ (i * p) - 2 ^ i := by
    have hproj : ordProj[2] i ∣ 2 ^ (i * p) - 2 ^ i := by
      refine h2i.trans ?_
      rw [hsplit]
      exact dvd_mul_right _ _
    have hcomp : ordCompl[2] i ∣ 2 ^ (i * p) - 2 ^ i := by
      rw [hsplit]
      exact dvd_mul_of_dvd_right hMdvd _
    have hcop : Nat.Coprime (ordProj[2] i) (ordCompl[2] i) := by
      simpa using
        (coprime_ordCompl (by decide : (2 : ℕ).Prime) (by omega)).pow_left (i.factorization 2)
    have := hcop.mul_dvd_of_dvd_of_dvd hproj hcomp
    simpa [ordProj_mul_ordCompl_eq_self] using this
  have hpdvd : p ∣ 2 ^ (i * p) - 2 ^ i := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : Fact p.Prime := ⟨hpp⟩
    have hle : 2 ^ i ≤ 2 ^ (i * p) :=
      pow_le_pow_right' (by decide : 1 ≤ 2) (Nat.le_mul_of_pos_right i hpp.pos)
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, pow_mul, ZMod.pow_card]
    ring
  have hboth : i * p ∣ 2 ^ (i * p) - 2 ^ i :=
    hcopi.symm.mul_dvd_of_dvd_of_dvd hiDvd hpdvd
  have hgt : N < i * p := by
    have : p ≤ i * p := Nat.le_mul_of_pos_left p (by omega)
    omega
  refine ⟨i * p, ?_, hgt⟩
  exact zModEq_of_dvd_sub (i * p) (2 ^ i)
    (pow_le_pow_right' (by decide : 1 ≤ 2) (Nat.le_mul_of_pos_right i hpp.pos)) hboth

theorem OMA.solution : OMA.R_Erdos479_erdos_479_R1.H1 := by
  intro k hk
  rcases hk with rfl | rfl | rfl | ⟨i, hi, rfl⟩
  · simpa using infinite_zero
  · simpa using infinite_neg_one
  · simpa using infinite_neg_two
  · simpa [Int.natCast_pow] using infinite_two_pow i hi
