import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1
import Mathlib.FieldTheory.Finite.Basic

-- Giuga (1950): a strong Giuga number is Carmichael. Reducing the power sum
-- modulo a prime factor forces Korselt's condition and squarefreeness.

lemma sum_range_zmod (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) :
    ∑ i ∈ Finset.range p, f (i : ZMod p) = ∑ x : ZMod p, f x := by
  refine Finset.sum_nbij' (fun i => (i : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · simp
  · intro x _; simpa using ZMod.val_lt x
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  · intro x _; simp
  · intro i _; rfl

lemma sum_range_mul_zmod (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) (m : ℕ) :
    ∑ i ∈ Finset.range (p * m), f (i : ZMod p) = m * ∑ x : ZMod p, f x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, ← sum_range_zmod]
    push_cast
    simp only [ZMod.natCast_self, zero_mul, zero_add]
    ring

lemma sum_pow_zmod (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0 < k) :
    ∑ x : ZMod p, x ^ k = if p - 1 ∣ k then -1 else 0 := by
  classical
  have h := FiniteField.sum_pow_units (ZMod p) k
  rw [ZMod.card] at h
  rw [← h]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)))]
  · symm
    refine Finset.sum_nbij' (fun u => (u : ZMod p))
        (fun x => if hx : x = 0 then 1 else Units.mk0 x hx) ?_ ?_ ?_ ?_ ?_
    · intro u _; simp
    · intro x _; simp
    · intro u _; simp
    · intro x hx; simp at hx; simp [hx]
    · intro u _; rfl
  · intro x _ hx
    simp at hx
    simp [hx, hk.ne']

lemma giuga_prime_cond (a p : ℕ) (ha2 : 1 < a)
    (hdvd : a ∣ 1 + ∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1))
    (hp : p.Prime) (hpa : p ∣ a) : (p - 1) ∣ (a - 1) ∧ ¬ p * p ∣ a := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, rfl⟩ := hpa
  have hk : 0 < p * m - 1 := by omega
  have h0 : ((1 + ∑ i ∈ Finset.Ioo 0 (p * m), i ^ (p * m - 1) : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact (Dvd.intro m rfl).trans hdvd
  have hrange : Finset.range (p * m) = insert 0 (Finset.Ioo 0 (p * m)) := by
    ext i; simp; omega
  have hsum : ∑ i ∈ Finset.Ioo 0 (p * m), ((i : ZMod p)) ^ (p * m - 1)
      = (m : ZMod p) * ∑ x : ZMod p, x ^ (p * m - 1) := by
    rw [← sum_range_mul_zmod p (fun x => x ^ (p * m - 1)) m, hrange, Finset.sum_insert (by simp)]
    simp [hk.ne']
  push_cast at h0
  rw [hsum, sum_pow_zmod p _ hk] at h0
  split_ifs at h0 with hd
  · refine ⟨hd, ?_⟩
    rintro ⟨c, hc⟩
    have hm : m = p * c := by
      exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [hc]; ring)
    subst hm
    push_cast at h0
    simp at h0
  · simp at h0

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H1 := by
  intro a ha
  obtain ⟨hc, hdvd⟩ := ha
  refine (AgohGiuga.korselts_criterion a hc).mpr ⟨?_, fun p hp hpa =>
    (giuga_prime_cond a p hc.1 hdvd hp hpa).1⟩
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  exact (giuga_prime_cond a p hc.1 hdvd hp ((Dvd.intro p rfl).trans hpp)).2 hpp
