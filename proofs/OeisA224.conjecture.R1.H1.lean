import OMAReductions.R_OeisA224_conjecture_R1

-- OEIS A224, reduction step H1: an odd prime power p^k with k ≥ 2 is not a
-- fixed point of n ↦ n^2 modulo a(n) * (a(n) - 1), where a(n) is the number of
-- squares modulo n. Squares modulo p^k are 0 together with p^{2m} times a unit
-- square modulo p^{k-2m}, and the unit group is cyclic of even order, so
-- a(p^k) has the closed form used below. That form makes a(a-1) share a factor
-- with (p^k)^2 - 1 only if p divides 1.
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

section

open Classical
open Finset

lemma totient_two_dvd (p e : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) :
    2 ∣ (p ^ e).totient := by
  rw [Nat.totient_prime_pow hp he]
  obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
  have hsub : p - 1 = 2 * t := by omega
  rw [hsub]
  exact ⟨p ^ (e - 1) * t, by ring⟩

lemma unitSquareCard (p e : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e)
    [NeZero (p ^ e)] :
    ((Finset.univ : Finset (ZMod (p ^ e))ˣ).image
        fun (u : (ZMod (p ^ e))ˣ) => ((u : ZMod (p ^ e)) ^ 2).val).card =
      (p ^ e).totient / 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcyc : IsCyclic (ZMod (p ^ e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  let f : (ZMod (p ^ e))ˣ →* (ZMod (p ^ e))ˣ := powMonoidHom 2
  have hcard : Nat.card f.range = (p ^ e).totient / 2 := by
    rw [IsCyclic.card_powMonoidHom_range (G := (ZMod (p ^ e))ˣ) 2]
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    rw [Nat.gcd_eq_right (totient_two_dvd p e hp hp2 he)]
  let toNat : f.range → ℕ := fun u => ((u : (ZMod (p ^ e))ˣ) : ZMod (p ^ e)).val
  have hinj : Function.Injective toNat := by
    intro x y hxy
    apply Subtype.ext
    exact Units.ext (ZMod.val_injective (p ^ e) hxy)
  have himg : ((Finset.univ : Finset f.range).image toNat).card = Nat.card f.range := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
  have heq :
      (Finset.univ : Finset (ZMod (p ^ e))ˣ).image
          (fun (u : (ZMod (p ^ e))ˣ) => ((u : ZMod (p ^ e)) ^ 2).val) =
        (Finset.univ : Finset f.range).image toNat := by
    ext s
    constructor
    · intro hs
      obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hs
      refine Finset.mem_image.mpr ⟨⟨f u, MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩, Finset.mem_univ _, ?_⟩
      simpa [toNat, f, powMonoidHom_apply, Units.val_pow_eq_pow_val] using hu
    · intro hs
      obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hs
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp u.property
      refine Finset.mem_image.mpr ⟨v, Finset.mem_univ _, ?_⟩
      have hv' : f v = u := by simpa [f, powMonoidHom_apply] using hv
      calc
        ((v : ZMod (p ^ e)) ^ 2).val
            = (((f v : (ZMod (p ^ e))ˣ) : ZMod (p ^ e))).val := by
              simp [f, powMonoidHom_apply, Units.val_pow_eq_pow_val]
        _ = ((u : (ZMod (p ^ e))ˣ) : ZMod (p ^ e)).val := by rw [hv']
        _ = s := by simpa [toNat] using hu
  rw [heq, himg, hcard]

lemma term_eq (p e : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) :
    (p ^ e).totient / 2 = p ^ (e - 1) * ((p - 1) / 2) := by
  rw [Nat.totient_prime_pow hp he]
  obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
  have hsub : p - 1 = 2 * t := by omega
  rw [hsub]
  exact Nat.mul_div_assoc (p ^ (e - 1)) (⟨t, rfl⟩ : 2 ∣ 2 * t)

lemma oddHalf_pos (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : 0 < (p - 1) / 2 := by
  obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
  have hp2 : 2 ≤ p := hp.two_le
  have : p - 1 = 2 * t := by omega
  have ht0 : 0 < t := by omega
  rw [this, Nat.mul_div_right _ (by decide : 0 < 2)]
  exact ht0

lemma exp_pos (k m : ℕ) (hk : 0 < k) (hm : m ≤ (k - 1) / 2) : 0 < k - 2 * m := by
  omega

lemma sum_pow_shift (p k : ℕ) (hp : 2 ≤ p) (hk : 0 < k) :
    ∑ m ∈ range ((k - 1) / 2 + 1), p ^ (k - 1 - 2 * m) =
      p ^ (k - 1 - 2 * ((k - 1) / 2)) *
        (((p ^ 2) ^ ((k - 1) / 2 + 1) - 1) / (p ^ 2 - 1)) := by
  let M := (k - 1) / 2
  have hsum :
      ∑ m ∈ range (M + 1), p ^ (k - 1 - 2 * m) =
        p ^ (k - 1 - 2 * M) * ∑ m ∈ range (M + 1), (p ^ 2) ^ (M - m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m < M + 1 := by simpa using hm
    have hexp : k - 1 - 2 * m = (k - 1 - 2 * M) + 2 * (M - m) := by omega
    rw [hexp, pow_add, pow_mul]
  have hreflect :
      ∑ m ∈ range (M + 1), (p ^ 2) ^ (M - m) =
        ∑ i ∈ range (M + 1), (p ^ 2) ^ i := by
    have h1 :
        ∑ m ∈ range (M + 1), (p ^ 2) ^ (M - m) =
          ∑ m ∈ range (M + 1), (p ^ 2) ^ (M + 1 - 1 - m) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      congr 1
    exact h1.trans (Finset.sum_range_reflect (fun i => (p ^ 2) ^ i) (M + 1))
  have hp2 : 2 ≤ p ^ 2 := by
    rw [pow_two]
    exact le_trans hp (Nat.le_mul_self p)
  rw [hsum, hreflect, Nat.geomSum_eq hp2]

lemma cancel_factor (a b c : ℕ) (hc : 0 < c) : c * a / (c * b) = a / b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · have hb0 : 0 < b := Nat.pos_of_ne_zero hb
    have hmod : a % b < b := Nat.mod_lt _ hb0
    have hlt : c * (a % b) < c * b := Nat.mul_lt_mul_of_pos_left hmod hc
    have hrepr : c * a = c * b * (a / b) + c * (a % b) := by
      calc
        c * a = c * (b * (a / b) + a % b) := by rw [Nat.div_add_mod]
        _ = c * (b * (a / b)) + c * (a % b) := by rw [Nat.mul_add]
        _ = c * b * (a / b) + c * (a % b) := by rw [Nat.mul_assoc]
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [hrepr, Nat.mul_comm (a / b)]
      exact Nat.le_add_right _ _
    · rw [hrepr]
      have hright : (a / b + 1) * (c * b) = c * b * (a / b) + c * b := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      rw [hright]
      exact Nat.add_lt_add_left hlt _

lemma sum_closed (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) :
    ∑ m ∈ range ((k - 1) / 2 + 1), (p ^ (k - 2 * m)).totient / 2 =
      if Even k then p * (p ^ k - 1) / (2 * (p + 1))
      else (p ^ (k + 1) - 1) / (2 * (p + 1)) := by
  have hp2' : 2 ≤ p := hp.two_le
  have hterms :
      ∑ m ∈ range ((k - 1) / 2 + 1), (p ^ (k - 2 * m)).totient / 2 =
        ((p - 1) / 2) * ∑ m ∈ range ((k - 1) / 2 + 1), p ^ (k - 1 - 2 * m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ (k - 1) / 2 := by
      simp only [mem_range] at hm
      omega
    have he : 0 < k - 2 * m := exp_pos k m hk hm'
    have hexp : (k - 2 * m) - 1 = k - 1 - 2 * m := by omega
    rw [term_eq p (k - 2 * m) hp hp2 he, hexp, Nat.mul_comm]
  rw [hterms, sum_pow_shift p k hp2' hk]
  let M := (k - 1) / 2
  let c := (p - 1) / 2
  have hc : 0 < c := oddHalf_pos p hp hp2
  have hsub : p - 1 = 2 * c := by
    obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
    have hp1 : p - 1 = 2 * t := by omega
    have hct : c = t := by
      simp only [c, hp1, Nat.mul_div_right _ (by decide : 0 < 2)]
    rw [hct, hp1]
  have hden : p ^ 2 - 1 = 2 * c * (p + 1) := by
    have hp1 : 1 ≤ p := hp.one_lt.le
    have hpp : 1 ≤ p * p := le_trans hp1 (Nat.le_mul_self p)
    have hmul : p * p - 1 = (p - 1) * (p + 1) := by
      apply (Nat.cast_injective (R := ℤ))
      rw [Nat.cast_sub hpp, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_add,
        Nat.cast_one]
      ring
    rw [pow_two, hmul, hsub]
  by_cases heven : Even k
  · rw [if_pos heven]
    obtain ⟨t, rfl⟩ := heven
    simp only [← two_mul]
    have hM : 2 * t - 1 - 2 * ((2 * t - 1) / 2) = 1 := by omega
    have hpow : 2 * (((2 * t - 1) / 2) + 1) = 2 * t := by omega
    rw [hM, pow_one]
    have hpow' : (p ^ 2) ^ ((2 * t - 1) / 2 + 1) = p ^ (2 * t) := by
      rw [← pow_mul, hpow]
    rw [hpow']
    have hdiv : p ^ 2 - 1 ∣ p ^ (2 * t) - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one p (even_two_mul t).two_dvd
    have h1 : c * (p * ((p ^ (2 * t) - 1) / (p ^ 2 - 1))) =
        (c * (p * (p ^ (2 * t) - 1))) / (p ^ 2 - 1) := by
      have hinner : p * ((p ^ (2 * t) - 1) / (p ^ 2 - 1)) =
          (p * (p ^ (2 * t) - 1)) / (p ^ 2 - 1) :=
        (Nat.mul_div_assoc p hdiv).symm
      rw [hinner]
      exact (Nat.mul_div_assoc c (dvd_mul_of_dvd_right hdiv p)).symm
    rw [h1, hden]
    have hassoc : 2 * c * (p + 1) = c * (2 * (p + 1)) := by
      rw [Nat.mul_assoc, Nat.mul_left_comm]
    rw [hassoc]
    exact cancel_factor (p * (p ^ (2 * t) - 1)) (2 * (p + 1)) c hc
  · rw [if_neg heven]
    have ho : Odd k := Nat.not_even_iff_odd.mp heven
    obtain ⟨t, rfl⟩ := ho
    have hM : 2 * t + 1 - 1 - 2 * ((2 * t + 1 - 1) / 2) = 0 := by omega
    have hpow : 2 * (((2 * t + 1 - 1) / 2) + 1) = 2 * t + 1 + 1 := by omega
    rw [hM, pow_zero, one_mul]
    have hpow' : (p ^ 2) ^ ((2 * t + 1 - 1) / 2 + 1) = p ^ (2 * t + 1 + 1) := by
      rw [← pow_mul, hpow]
    rw [hpow']
    have hdiv : p ^ 2 - 1 ∣ p ^ (2 * t + 1 + 1) - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one p (⟨t + 1, by omega⟩ : 2 ∣ 2 * t + 1 + 1)
    have h1 : c * ((p ^ (2 * t + 1 + 1) - 1) / (p ^ 2 - 1)) =
        (c * (p ^ (2 * t + 1 + 1) - 1)) / (p ^ 2 - 1) :=
      (Nat.mul_div_assoc c hdiv).symm
    rw [h1, hden]
    have hassoc : 2 * c * (p + 1) = c * (2 * (p + 1)) := by
      rw [Nat.mul_assoc, Nat.mul_left_comm]
    rw [hassoc]
    exact cancel_factor (p ^ (2 * t + 1 + 1) - 1) (2 * (p + 1)) c hc

def sqResidues (n : ℕ) : Finset ℕ := (range n).image fun i => i ^ 2 % n

lemma a_card (n : ℕ) (hn : n ≠ 0) : OeisA224.a n = (sqResidues n).card := by
  unfold OeisA224.a sqResidues
  rw [if_neg hn]

noncomputable def unitVals (p e : ℕ) [NeZero (p ^ e)] : Finset ℕ :=
  (Finset.univ : Finset (ZMod (p ^ e))ˣ).image fun (u : (ZMod (p ^ e))ˣ) =>
    ((u : ZMod (p ^ e)) ^ 2).val

noncomputable def piece (p k m : ℕ) [NeZero (p ^ (k - 2 * m))] : Finset ℕ :=
  (unitVals p (k - 2 * m)).image fun s => p ^ (2 * m) * s

lemma unitVals_card (p e : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e)
    [NeZero (p ^ e)] : (unitVals p e).card = (p ^ e).totient / 2 := by
  simpa [unitVals] using unitSquareCard p e hp hp2 he

lemma piece_card (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k)
    (hm : m ≤ (k - 1) / 2) [NeZero (p ^ (k - 2 * m))] :
    (piece p k m).card = (p ^ (k - 2 * m)).totient / 2 := by
  have he : 0 < k - 2 * m := exp_pos k m hk hm
  haveI : NeZero (p ^ (k - 2 * m)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  unfold piece
  rw [card_image_of_injective]
  · exact unitVals_card p (k - 2 * m) hp hp2 he
  · intro s₁ s₂ hs
    exact Nat.mul_left_cancel (pow_pos hp.pos _) hs

lemma zero_mem_sq (p k : ℕ) (hp : p.Prime) (hk : 0 < k) : 0 ∈ sqResidues (p ^ k) := by
  refine mem_image.mpr ⟨0, mem_range.mpr (pow_pos hp.pos _), ?_⟩
  simp

lemma piece_subset_sq (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k)
    (hm : m ≤ (k - 1) / 2) [NeZero (p ^ (k - 2 * m))] :
    piece p k m ⊆ sqResidues (p ^ k) := by
  intro r hr
  unfold piece unitVals at hr
  obtain ⟨s0, hs0, rfl⟩ := mem_image.mp hr
  obtain ⟨u, -, rfl⟩ := mem_image.mp hs0
  have he : 0 < k - 2 * m := exp_pos k m hk hm
  haveI : NeZero (p ^ (k - 2 * m)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let e := k - 2 * m
  set j : ℕ := (u : ZMod (p ^ e)).val
  set s : ℕ := ((u : ZMod (p ^ e)) ^ 2).val
  have hval : s < p ^ e := ZMod.val_lt _
  have hsqZ : ((j ^ 2 : ℕ) : ZMod (p ^ e)) = (s : ZMod (p ^ e)) := by
    rw [Nat.cast_pow, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hmod : j ^ 2 ≡ s [MOD p ^ e] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hsqZ
  have hmod_eq : j ^ 2 % p ^ e = s := by
    rw [Nat.ModEq] at hmod
    rwa [Nat.mod_eq_of_lt hval] at hmod
  have hsle : s ≤ j ^ 2 := by rw [← hmod_eq]; exact Nat.mod_le _ _
  obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hsle).mp hmod.symm
  have hj : j ^ 2 = s + p ^ e * q := by
    have hsub : j ^ 2 - s = p ^ e * q := hq
    omega
  have hkexp : 2 * m + e = k := by simp [e]; omega
  have hpow : (p ^ m * j) ^ 2 = p ^ (2 * m) * s + p ^ k * q := by
    calc
      (p ^ m * j) ^ 2 = p ^ (2 * m) * j ^ 2 := by
        have hpowm : (p ^ m) ^ 2 = p ^ (2 * m) := by
          rw [← pow_mul]
          congr 1
          omega
        rw [mul_pow, hpowm]
      _ = p ^ (2 * m) * (s + p ^ e * q) := by rw [hj]
      _ = p ^ (2 * m) * s + p ^ (2 * m) * (p ^ e * q) := by rw [Nat.mul_add]
      _ = p ^ (2 * m) * s + p ^ k * q := by
        rw [← Nat.mul_assoc, ← pow_add, hkexp]
  have hlt : p ^ (2 * m) * s < p ^ k := by
    calc
      p ^ (2 * m) * s < p ^ (2 * m) * p ^ e :=
        Nat.mul_lt_mul_of_pos_left hval (pow_pos hp.pos _)
      _ = p ^ k := by rw [← pow_add, hkexp]
  have hsqmod : (p ^ m * j) ^ 2 % p ^ k = p ^ (2 * m) * s := by
    rw [hpow, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  let i := (p ^ m * j) % p ^ k
  have hi : i < p ^ k := Nat.mod_lt _ (pow_pos hp.pos _)
  refine mem_image.mpr ⟨i, mem_range.mpr hi, ?_⟩
  have hpowmod : i ^ 2 % p ^ k = (p ^ m * j) ^ 2 % p ^ k := by
    simpa [i, Nat.ModEq] using (Nat.mod_modEq (p ^ m * j) (p ^ k)).pow 2
  rw [hpowmod, hsqmod]

noncomputable def pieceOf (p k m : ℕ) : Finset ℕ :=
  if h : p ≠ 0 ∧ 0 < k - 2 * m then
    haveI : NeZero (p ^ (k - 2 * m)) := ⟨pow_ne_zero _ h.1⟩
    piece p k m
  else
    ∅

lemma pieceOf_eq (p k m : ℕ) (hp : p ≠ 0) (he : 0 < k - 2 * m)
    [NeZero (p ^ (k - 2 * m))] : pieceOf p k m = piece p k m := by
  unfold pieceOf
  rw [dif_pos ⟨hp, he⟩]

lemma pieceOf_card (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k)
    (hm : m ≤ (k - 1) / 2) :
    (pieceOf p k m).card = (p ^ (k - 2 * m)).totient / 2 := by
  have he : 0 < k - 2 * m := exp_pos k m hk hm
  haveI : NeZero (p ^ (k - 2 * m)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [pieceOf_eq p k m hp.ne_zero he]
  exact piece_card p k m hp hp2 hk hm

lemma zero_not_mem_pieceOf (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    0 ∉ pieceOf p k m := by
  intro hz
  by_cases h : p ≠ 0 ∧ 0 < k - 2 * m
  · haveI : NeZero (p ^ (k - 2 * m)) := ⟨pow_ne_zero _ h.1⟩
    rw [pieceOf_eq p k m h.1 h.2] at hz
    unfold piece unitVals at hz
    obtain ⟨s, hs, hprod⟩ := mem_image.mp hz
    obtain ⟨u, -, rfl⟩ := mem_image.mp hs
    have hsame := (congrArg ZMod.val (Units.val_pow_eq_pow_val u 2)).symm
    have hs0 : ((u : ZMod (p ^ (k - 2 * m))) ^ 2).val ≠ 0 := by
      intro h0
      have hcop := ZMod.val_coe_unit_coprime (u ^ 2)
      rw [← hsame, h0, Nat.coprime_zero_left] at hcop
      have hone : p ^ (k - 2 * m) ≠ 1 :=
        (Nat.one_lt_pow h.2.ne' hp.one_lt).ne'
      exact hone hcop
    have : p ^ (2 * m) * ((u : ZMod (p ^ (k - 2 * m))) ^ 2).val ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hp.ne_zero) hs0
    exact this hprod
  · rw [pieceOf, dif_neg h] at hz
    simp at hz

lemma pieces_disjoint (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) :
    (range ((k - 1) / 2 + 1) : Set ℕ).PairwiseDisjoint (pieceOf p k) := by
  intro a ha b hb hab
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx hy
  haveI : Fact p.Prime := ⟨hp⟩
  have ha' : a ≤ (k - 1) / 2 := by
    have : a < (k - 1) / 2 + 1 := by simpa using ha
    omega
  have hb' : b ≤ (k - 1) / 2 := by
    have : b < (k - 1) / 2 + 1 := by simpa using hb
    omega
  haveI : NeZero (p ^ (k - 2 * a)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ (k - 2 * b)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [pieceOf_eq p k a hp.ne_zero (exp_pos k a hk ha')] at hx
  rw [pieceOf_eq p k b hp.ne_zero (exp_pos k b hk hb')] at hy
  unfold piece unitVals at hx hy
  obtain ⟨sa, hsa, hxa⟩ := mem_image.mp hx
  obtain ⟨sb, hsb, hxb⟩ := mem_image.mp hy
  obtain ⟨ua, -, rfl⟩ := mem_image.mp hsa
  obtain ⟨ub, -, rfl⟩ := mem_image.mp hsb
  have hcopa := ZMod.val_coe_unit_coprime (ua ^ 2)
  have hcopb := ZMod.val_coe_unit_coprime (ub ^ 2)
  have hsama := (congrArg ZMod.val (Units.val_pow_eq_pow_val ua 2)).symm
  have hsamb := (congrArg ZMod.val (Units.val_pow_eq_pow_val ub 2)).symm
  have hnota : ¬ p ∣ (↑(ua ^ 2) : ZMod (p ^ (k - 2 * a))).val :=
    hp.coprime_iff_not_dvd.mp
      ((hcopa.coprime_dvd_right (dvd_pow_self _ (exp_pos k a hk ha').ne')).symm)
  have hnotb : ¬ p ∣ (↑(ub ^ 2) : ZMod (p ^ (k - 2 * b))).val :=
    hp.coprime_iff_not_dvd.mp
      ((hcopb.coprime_dvd_right (dvd_pow_self _ (exp_pos k b hk hb').ne')).symm)
  have hvala : padicValNat p (p ^ (2 * a) *
      ((ua : ZMod (p ^ (k - 2 * a))) ^ 2).val) = 2 * a := by
    rw [hsama, padicValNat.mul (pow_ne_zero _ hp.ne_zero)
        (by intro h0; exact hnota (h0 ▸ dvd_zero p)),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hnota]
    omega
  have hvalb : padicValNat p (p ^ (2 * b) *
      ((ub : ZMod (p ^ (k - 2 * b))) ^ 2).val) = 2 * b := by
    rw [hsamb, padicValNat.mul (pow_ne_zero _ hp.ne_zero)
        (by intro h0; exact hnotb (h0 ▸ dvd_zero p)),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hnotb]
    omega
  have := hxa.trans hxb.symm
  rw [this] at hvala
  omega

lemma sq_covered (p k i : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) :
    i ^ 2 % p ^ k ∈ insert 0 ((range ((k - 1) / 2 + 1)).biUnion (pieceOf p k)) := by
  by_cases hr0 : i ^ 2 % p ^ k = 0
  · exact mem_insert.mpr (Or.inl hr0)
  haveI : Fact p.Prime := ⟨hp⟩
  set r := i ^ 2 % p ^ k
  have hi : i ≠ 0 := by
    intro h
    apply hr0
    simp [r, h]
  set m := padicValNat p i
  have hdivp : p ^ m ∣ i := (padicValNat_dvd_iff_le hi).mpr le_rfl
  have hv : padicValNat p (i ^ 2) = 2 * m := by simpa [m] using (padicValNat.pow i 2)
  have hvk : 2 * m < k := by
    by_contra hge
    have hd : p ^ k ∣ i ^ 2 := (padicValNat_dvd_iff_le (pow_ne_zero 2 hi)).mpr (by
      rw [hv]; omega)
    exact hr0 (Nat.mod_eq_zero_of_dvd hd)
  have hmbound : m ≤ (k - 1) / 2 := by omega
  have he : 0 < k - 2 * m := exp_pos k m hk hmbound
  set j := i / p ^ m
  have hij : p ^ m * j = i := Nat.mul_div_cancel' hdivp
  have hnd : ¬ p ∣ j := by
    intro hpj
    obtain ⟨t, ht⟩ := hpj
    have hdvd : p ^ (m + 1) ∣ i := by
      rw [← hij, ht, ← Nat.mul_assoc, ← pow_succ]
      exact dvd_mul_right _ _
    have := (padicValNat_dvd_iff_le hi).mp hdvd
    simp [m] at this
  have hcop : Nat.Coprime j p := ((hp.coprime_iff_not_dvd).mpr hnd).symm
  let e := k - 2 * m
  have hkexp : 2 * m + e = k := by simp [e]; omega
  have hsq : i ^ 2 = p ^ (2 * m) * j ^ 2 := by
    rw [← hij, mul_pow]
    have : (p ^ m) ^ 2 = p ^ (2 * m) := by
      rw [← pow_mul]
      congr 1
      exact Nat.mul_comm _ _
    rw [this]
  set s0 := j ^ 2 % p ^ e
  have hs0 : s0 < p ^ e := Nat.mod_lt _ (pow_pos hp.pos _)
  have hj2 : j ^ 2 = p ^ e * (j ^ 2 / p ^ e) + s0 := by
    simpa [s0] using (Nat.div_add_mod (j ^ 2) (p ^ e)).symm
  have hsplit : i ^ 2 = p ^ k * (j ^ 2 / p ^ e) + p ^ (2 * m) * s0 := by
    calc
      i ^ 2 = p ^ (2 * m) * j ^ 2 := hsq
      _ = p ^ (2 * m) * (p ^ e * (j ^ 2 / p ^ e) + j ^ 2 % p ^ e) :=
        congrArg (fun t => p ^ (2 * m) * t) (Nat.div_add_mod (j ^ 2) (p ^ e)).symm
      _ = p ^ (2 * m) * (p ^ e * (j ^ 2 / p ^ e)) + p ^ (2 * m) * (j ^ 2 % p ^ e) := by
        rw [Nat.mul_add]
      _ = p ^ k * (j ^ 2 / p ^ e) + p ^ (2 * m) * s0 := by
        rw [← Nat.mul_assoc, ← pow_add, hkexp]
  have hlt : p ^ (2 * m) * s0 < p ^ k := by
    calc
      p ^ (2 * m) * s0 < p ^ (2 * m) * p ^ e :=
        Nat.mul_lt_mul_of_pos_left hs0 (pow_pos hp.pos _)
      _ = p ^ k := by rw [← pow_add, hkexp]
  have hr : r = p ^ (2 * m) * s0 := by
    rw [show r = i ^ 2 % p ^ k from rfl, hsplit, Nat.add_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hlt]
  have hcopj : Nat.Coprime j (p ^ e) := hcop.pow_right e
  have hcopmod : Nat.Coprime (j % p ^ e) (p ^ e) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hg : Nat.gcd (p ^ e) j = Nat.gcd (j % p ^ e) (p ^ e) := Nat.gcd_rec (p ^ e) j
    rw [← hg, Nat.gcd_comm]
    exact (Nat.coprime_iff_gcd_eq_one).mp hcopj
  let u := ZMod.unitOfCoprime (j % p ^ e) hcopmod
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hu : ((u : ZMod (p ^ e)) ^ 2).val = s0 := by
    rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast]
    simpa [s0, Nat.pow_mod] 
  have hs0mem : s0 ∈ unitVals p e := by
    refine mem_image.mpr ⟨u, mem_univ _, hu⟩
  have hmem : p ^ (2 * m) * s0 ∈ piece p k m := by
    refine mem_image.mpr ⟨s0, hs0mem, rfl⟩
  have hmrange : m ∈ range ((k - 1) / 2 + 1) := by
    rw [mem_range]
    omega
  rw [hr]
  refine mem_insert_of_mem (mem_biUnion.mpr ⟨m, hmrange, ?_⟩)
  rw [pieceOf_eq p k m hp.ne_zero he]
  exact hmem

lemma a_formula (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) :
    OeisA224.a (p ^ k) =
      1 + if Even k then p * (p ^ k - 1) / (2 * (p + 1))
          else (p ^ (k + 1) - 1) / (2 * (p + 1)) := by
  rw [a_card (p ^ k) (pow_ne_zero _ hp.ne_zero)]
  let U := (range ((k - 1) / 2 + 1)).biUnion (pieceOf p k)
  have hsub : U ⊆ sqResidues (p ^ k) := by
    intro r hr
    obtain ⟨m, hm, hrm⟩ := mem_biUnion.mp hr
    have hm' : m ≤ (k - 1) / 2 := by
      have : m < (k - 1) / 2 + 1 := by simpa using hm
      omega
    have he := exp_pos k m hk hm'
    haveI : NeZero (p ^ (k - 2 * m)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [pieceOf_eq p k m hp.ne_zero he] at hrm
    exact piece_subset_sq p k m hp hp2 hk hm' hrm
  have hsup : sqResidues (p ^ k) ⊆ insert 0 U := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := mem_image.mp hr
    simpa [U] using sq_covered p k i hp hp2 hk
  have hzero : 0 ∉ U := by
    intro hz
    obtain ⟨m, _, hzm⟩ := mem_biUnion.mp hz
    exact zero_not_mem_pieceOf p k m hp hp2 hzm
  have heq : sqResidues (p ^ k) = insert 0 U :=
    Finset.Subset.antisymm hsup (by
      intro r hr
      rcases mem_insert.mp hr with rfl | hr
      · exact zero_mem_sq p k hp hk
      · exact hsub hr)
  rw [heq, card_insert_of_notMem hzero, card_biUnion (pieces_disjoint p k hp hp2 hk),
    Nat.add_comm]
  have hsum :
      ∑ m ∈ range ((k - 1) / 2 + 1), (pieceOf p k m).card =
        ∑ m ∈ range ((k - 1) / 2 + 1), (p ^ (k - 2 * m)).totient / 2 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ (k - 1) / 2 := by
      have : m < (k - 1) / 2 + 1 := by simpa using hm
      omega
    exact pieceOf_card p k m hp hp2 hk hm'
  rw [hsum]
  exact congrArg (fun n => 1 + n) (sum_closed p k hp hp2 hk)

lemma not_dvd_gap {M N lo : ℕ} (hM : 0 < M) (hlo : lo * M < N) (hhi : N < (lo + 1) * M) :
    ¬ M ∣ N := by
  intro ⟨t, ht⟩
  have hlt : t < lo + 1 := by
    by_contra h
    have : lo + 1 ≤ t := by omega
    have : (lo + 1) * M ≤ t * M := Nat.mul_le_mul_right _ this
    rw [ht, Nat.mul_comm M t] at hhi
    omega
  have hgt : lo < t := by
    by_contra h
    have : t ≤ lo := by omega
    have : t * M ≤ lo * M := Nat.mul_le_mul_right _ this
    rw [ht, Nat.mul_comm M t] at hlo
    omega
  omega


theorem OMA.solution : OMA.R_OeisA224_conjecture_R1.H1 := by
  intro p k hp hp2 hk
  have hk0 : 0 < k := by omega
  rw [a_formula p k hp hp2 hk0]
  intro hcong
  set D := 2 * (p + 1) with hDdef
  obtain ⟨c, hc⟩ := hp.odd_of_ne_two hp2
  have hc2 : p - 1 = 2 * c := by
    rw [hc]
    omega
  have hden : p ^ 2 - 1 = c * D := by
    have hp1 : 1 ≤ p := hp.one_lt.le
    have hpp : 1 ≤ p * p := le_trans hp1 (Nat.le_mul_self p)
    have hmul : p * p - 1 = (p - 1) * (p + 1) := by
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub hpp, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_add,
        Nat.cast_one]
      ring
    rw [pow_two, hmul, hc2, hDdef]
    ac_rfl
  by_cases heven : Even k
  · rw [if_pos heven] at hcong
    obtain ⟨t, rfl⟩ := heven
    simp only [← two_mul] at hcong
    set n := p ^ (2 * t)
    have hsqdvd : p ^ 2 - 1 ∣ n - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one p (even_two_mul t).two_dvd
    obtain ⟨q, hq⟩ := hsqdvd
    have hDdvd : D ∣ n - 1 := by
      rw [hq, hden]
      exact ⟨c * q, by ac_rfl⟩
    set b := p * (n - 1) / D
    have hDb : D * b = p * (n - 1) := by
      simpa [b] using Nat.mul_div_cancel' (dvd_mul_of_dvd_right hDdvd p)
    have hn1 : 1 ≤ n := Nat.one_le_pow _ _ hp.pos
    have hn2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega : 0 < n)
    have hfac : n ^ 2 - 1 = (n - 1) * (n + 1) := by
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub hn2, Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_add, Nat.cast_one,
        Nat.cast_pow]
      ring
    have hmod : (1 + b) * b ∣ n ^ 2 - 1 := by
      simpa [Nat.add_sub_cancel] using (Nat.modEq_iff_dvd' hn2).mp hcong.symm
    obtain ⟨s, hs⟩ := hmod
    have heq : (1 + b) * p * s * (n - 1) = D * (n + 1) * (n - 1) := by
      calc
        (1 + b) * p * s * (n - 1) = (1 + b) * (p * (n - 1)) * s := by ac_rfl
        _ = (1 + b) * (D * b) * s := by rw [← hDb]
        _ = D * ((1 + b) * b * s) := by ac_rfl
        _ = D * (n ^ 2 - 1) := by rw [hs]
        _ = D * ((n - 1) * (n + 1)) := by rw [hfac]
        _ = D * (n + 1) * (n - 1) := by ac_rfl
    have hpos : 0 < n - 1 := by
      have : 1 < n := Nat.one_lt_pow (by omega : 2 * t ≠ 0) hp.one_lt
      omega
    have hcancel : (1 + b) * p * s = D * (n + 1) := Nat.mul_right_cancel hpos heq
    have hdvd : p ∣ D * (n + 1) := by
      have : p ∣ (1 + b) * p * s := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
      rwa [hcancel] at this
    rcases hp.dvd_mul.mp hdvd with hDp | hnp
    · rcases hp.dvd_mul.mp hDp with h2 | hp1
      · have hp2le : p ≤ 2 := Nat.le_of_dvd (by decide) h2
        have : 2 < p := by
          have := hp.two_le
          omega
        omega
      · have h1 : p ∣ 1 := by
          simpa using (Nat.dvd_sub hp1 dvd_rfl : p ∣ p + 1 - p)
        have : p ≤ 1 := Nat.le_of_dvd (by decide) h1
        have := hp.two_le
        omega
    · have hpn : p ∣ n := dvd_pow_self p (by omega)
      have h1 : p ∣ 1 := by
          simpa using (Nat.dvd_sub hnp hpn : p ∣ n + 1 - n)
      have : p ≤ 1 := Nat.le_of_dvd (by decide) h1
      have := hp.two_le
      omega
  · rw [if_neg heven] at hcong
    have ho : Odd k := Nat.not_even_iff_odd.mp heven
    obtain ⟨t, rfl⟩ := ho
    have ht1 : 1 ≤ t := by omega
    set z := p ^ (2 * t + 1)
    have hsqdvd : p ^ 2 - 1 ∣ p ^ (2 * t + 2) - 1 := by
      have hexp : 2 * (t + 1) = 2 * t + 2 := by omega
      simpa [hexp] using
        Nat.pow_sub_one_dvd_pow_sub_one p (⟨t + 1, rfl⟩ : 2 ∣ 2 * (t + 1))
    obtain ⟨q, hq⟩ := hsqdvd
    have hDdvd : D ∣ p ^ (2 * t + 2) - 1 := by
      rw [hq, hden]
      exact ⟨c * q, by ac_rfl⟩
    set B := p ^ (2 * t + 2) - 1
    set b := B / D
    have hDb : D * b = B := by simpa [b, B] using Nat.mul_div_cancel' hDdvd
    set A := p * z + 2 * p + 1
    have hA : D * (1 + b) = A := by
      calc
        D * (1 + b) = D + D * b := by rw [Nat.mul_add, Nat.mul_one]
        _ = D + B := by rw [hDb]
        _ = A := by
          have hpow : p ^ (2 * t + 2) = p * z := by
            rw [pow_succ, Nat.mul_comm]
          have hsum : D + B = 2 * (p + 1) + (p * z - 1) := by
            simp [D, B, hDdef, hpow]
          calc
            D + B = 2 * (p + 1) + (p * z - 1) := hsum
            _ = p * z + 2 * p + 1 := by
              have hz : 1 ≤ p * z :=
                Nat.succ_le_of_lt (Nat.mul_pos hp.pos (pow_pos hp.pos _))
              zify [hz]
              ring
            _ = A := by simp [A]
    set M := A * B
    have hM : D * D * ((1 + b) * b) = M := by
      calc
        D * D * ((1 + b) * b) = (D * (1 + b)) * (D * b) := by ac_rfl
        _ = A * B := by rw [hA, hDb]
        _ = M := rfl
    have hz2 : 1 ≤ z ^ 2 := Nat.one_le_pow _ _ (by
      have : 0 < z := pow_pos hp.pos _
      omega)
    have hfac : z ^ 2 - 1 = (z - 1) * (z + 1) := by
      have hz1 : 1 ≤ z := Nat.one_le_pow _ _ hp.pos
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub hz2, Nat.cast_mul, Nat.cast_sub hz1, Nat.cast_add, Nat.cast_one,
        Nat.cast_pow]
      ring
    have hmod : (1 + b) * b ∣ z ^ 2 - 1 := by
      simpa [z, Nat.add_sub_cancel] using (Nat.modEq_iff_dvd' hz2).mp hcong.symm
    obtain ⟨s, hs⟩ := hmod
    have hdivM : M ∣ 4 * (p + 1) ^ 2 * (z ^ 2 - 1) := by
      have hDsq : D * D = 4 * (p + 1) ^ 2 := by
        rw [hDdef, pow_two, show (4 : ℕ) = 2 * 2 by decide]
        ac_rfl
      refine ⟨s, ?_⟩
      calc
        4 * (p + 1) ^ 2 * (z ^ 2 - 1) = D * D * ((1 + b) * b * s) := by
          rw [← hDsq, hs]
        _ = M * s := by
          have hassoc : D * D * ((1 + b) * b * s) = D * D * ((1 + b) * b) * s := by ac_rfl
          rw [hassoc, hM]
    set N := 4 * (p + 1) ^ 2 * (z ^ 2 - 1)
    have hMpos : 0 < M := by
      have hB : 0 < B := by
        have h1 : 1 < p ^ (2 * t + 2) := Nat.one_lt_pow (by omega : 2 * t + 2 ≠ 0) hp.one_lt
        simpa [B] using Nat.sub_pos_of_lt h1
      have hApos : 0 < A := by simp [A]
      exact Nat.mul_pos hApos hB
    have hpow : p ^ (2 * t + 2) = p * z := by
      rw [pow_succ, Nat.mul_comm]
    have hpowB : B = p * z - 1 := by
      simpa [B] using congrArg (fun n => n - 1) hpow
    have hMeq : M = (p * z + 2 * p + 1) * (p * z - 1) := by
      simp [M, A, hpowB]
    have hNeq : N = 4 * ((p + 1) ^ 2 * (z ^ 2 - 1)) := by
      simp [N, Nat.mul_assoc]
    have hpoly :
        (p + 1) ^ 2 * z ^ 2 + (p * z + 2 * p + 1) + p ^ 2 * (2 * z + 1) =
          (p * z + 2 * p + 1) * (p * z) + (2 * p + 1) * z ^ 2 + (p + 1) ^ 2 := by
      zify
      ring
    have hδ : p ^ 2 * (2 * z + 1) < (2 * p + 1) * z ^ 2 := by
      have hz3 : p ^ 3 ≤ z := by
        have hexp : 3 ≤ 2 * t + 1 := by omega
        exact Nat.pow_le_pow_right (hp.one_lt.le) hexp
      have hstep : 2 * p ^ 2 < (2 * p + 1) * p ^ 3 := by
        have hle : 2 * p ^ 2 ≤ p ^ 3 := by
          have hmul : 2 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ hp.two_le
          have heq : p * p ^ 2 = p ^ 3 := (pow_succ' p 2).symm
          rw [← heq]
          exact hmul
        have hone : 1 < 2 * p + 1 := by omega
        have hlt : p ^ 3 < (2 * p + 1) * p ^ 3 := by
          simpa [Nat.one_mul] using
            Nat.mul_lt_mul_of_pos_right hone (pow_pos hp.pos 3)
        exact lt_of_le_of_lt hle hlt
      have hltz : 2 * p ^ 2 < (2 * p + 1) * z :=
        lt_of_lt_of_le hstep (Nat.mul_le_mul_left _ hz3)
      have hmain : 2 * p ^ 2 * z < (2 * p + 1) * z ^ 2 := by
        have hz0 : 0 < z := by simpa [z] using pow_pos hp.pos (2 * t + 1)
        have := Nat.mul_lt_mul_of_pos_right hltz hz0
        simpa [pow_two, Nat.mul_assoc] using this
      have hsum : 2 * p ^ 2 * z + p ^ 2 < (2 * p + 1) * z ^ 2 := by
        have hsmall : p ^ 2 < 2 * p ^ 2 * z := by
          have h2z : 1 < 2 * z := by
            have hz1 : 1 ≤ z := by
              simpa [z] using Nat.one_le_pow (2 * t + 1) p hp.pos
            exact lt_of_lt_of_le (by decide : 1 < 2)
              (by simpa [Nat.mul_one] using Nat.mul_le_mul_left 2 hz1)
          have : p ^ 2 * 1 < p ^ 2 * (2 * z) :=
            Nat.mul_lt_mul_of_pos_left h2z (pow_pos hp.pos _)
          simpa [Nat.mul_one, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
        have hdouble : 2 * p ^ 2 * z + p ^ 2 < 4 * p ^ 2 * z := by
          have : 2 * p ^ 2 * z + 2 * p ^ 2 * z = 4 * p ^ 2 * z := by
            let a := p ^ 2 * z
            have : 2 * a + 2 * a = 4 * a := by omega
            simpa [a, Nat.mul_assoc] using this
          have : 2 * p ^ 2 * z + p ^ 2 < 2 * p ^ 2 * z + 2 * p ^ 2 * z :=
            Nat.add_lt_add_left hsmall _
          omega
        have h4 : 4 * p ^ 2 * z ≤ (2 * p + 1) * z ^ 2 := by
          rw [pow_two]
          have hcoef : 4 * p ^ 2 ≤ (2 * p + 1) * z := by
            have hcoef3 : 4 * p ^ 2 ≤ (2 * p + 1) * p ^ 3 := by
              have h4p : 4 ≤ (2 * p + 1) * p := by
                calc
                  4 = 2 * 2 := by decide
                  _ ≤ 2 * p := Nat.mul_le_mul_left _ hp.two_le
                  _ ≤ 2 * p * p := Nat.le_mul_of_pos_right (2 * p) hp.pos
                  _ ≤ 2 * p * p + p := Nat.le_add_right _ _
                  _ = (2 * p + 1) * p := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
              calc
                4 * p ^ 2 ≤ ((2 * p + 1) * p) * p ^ 2 := Nat.mul_le_mul_right _ h4p
                _ = (2 * p + 1) * p ^ 3 := by
                  rw [Nat.mul_assoc, ← pow_succ']
            exact le_trans hcoef3 (Nat.mul_le_mul_left _ hz3)
          simpa [pow_two, Nat.mul_assoc] using Nat.mul_le_mul_right z hcoef
        omega
      rw [Nat.mul_add, Nat.mul_one]
      have htwo : p ^ 2 * (2 * z) = 2 * p ^ 2 * z := by ac_rfl
      rw [htwo]
      exact hsum
    set S := p * z + 2 * p + 1
    set qn := (p + 1) ^ 2
    have hA1 : qn * z ^ 2 + S > S * (p * z) + qn := by
      have hlt : qn * z ^ 2 + S + p ^ 2 * (2 * z + 1) <
          qn * z ^ 2 + S + (2 * p + 1) * z ^ 2 :=
        Nat.add_lt_add_left hδ _
      have hpolyL : qn * z ^ 2 + S + p ^ 2 * (2 * z + 1) =
          S * (p * z) + (2 * p + 1) * z ^ 2 + qn := by
        simpa [S, qn, Nat.add_assoc] using hpoly
      rw [hpolyL] at hlt
      have hlt' : S * (p * z) + qn + (2 * p + 1) * z ^ 2 <
          qn * z ^ 2 + S + (2 * p + 1) * z ^ 2 := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
      exact Nat.lt_of_add_lt_add_right hlt'
    have hmul : S * (p * z - 1) < qn * (z ^ 2 - 1) := by
      have hL : qn * z ^ 2 = qn * (z ^ 2 - 1) + qn := by
        have h := Nat.sub_add_cancel hz2
        conv_lhs => arg 2; rw [← h]
        rw [Nat.mul_add, Nat.mul_one]
      have hR : S * (p * z) = S * (p * z - 1) + S := by
        have hxz : 1 ≤ p * z :=
          Nat.succ_le_of_lt (Nat.mul_pos hp.pos (by simpa [z] using pow_pos hp.pos (2 * t + 1)))
        have h := Nat.sub_add_cancel hxz
        conv_lhs => arg 2; rw [← h]
        rw [Nat.mul_add, Nat.mul_one]
      have hgt : S * (p * z - 1) + qn + S < qn * (z ^ 2 - 1) + qn + S := by
        have h := hA1
        rw [hL, hR] at h
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      exact Nat.lt_of_add_lt_add_right (Nat.lt_of_add_lt_add_right hgt)
    have hlo4 : 4 * M < N := by
      rw [hMeq, hNeq]
      exact Nat.mul_lt_mul_of_pos_left hmul (by decide : 0 < 4)
    have hclear {a b : ℕ} (h : a * qn * z ^ 2 + b * S < b * S * (p * z) + a * qn) :
        a * qn * (z ^ 2 - 1) < b * S * (p * z - 1) := by
      have hL : a * qn * z ^ 2 = a * qn * (z ^ 2 - 1) + a * qn := by
        have h := Nat.sub_add_cancel hz2
        conv_lhs => arg 2; rw [← h]
        rw [Nat.mul_add, Nat.mul_one]
      have hR : b * S * (p * z) = b * S * (p * z - 1) + b * S := by
        have hxz : 1 ≤ p * z :=
          Nat.succ_le_of_lt (Nat.mul_pos hp.pos (by simpa [z] using pow_pos hp.pos (2 * t + 1)))
        have h := Nat.sub_add_cancel hxz
        conv_lhs => arg 2; rw [← h]
        rw [Nat.mul_add, Nat.mul_one]
      have h' := h
      rw [hL, hR] at h'
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'
    by_cases hp11 : 11 ≤ p
    · have hlead : 8 * p + 4 ≤ p ^ 2 := by
        have h9 : 9 ≤ p := le_trans (by decide : 9 ≤ 11) hp11
        have h8 : 8 * p + 4 ≤ 9 * p := by
          have h4 : 4 ≤ p := le_trans (by decide : 4 ≤ 11) hp11
          calc
            8 * p + 4 ≤ 8 * p + p := Nat.add_le_add_left h4 _
            _ = 9 * p := by omega
        have hsq : 9 * p ≤ p ^ 2 := by
          rw [pow_two]
          exact Nat.mul_le_mul_right p h9
        exact le_trans h8 hsq
      have htail : 2 * p + 1 ≤ 4 * p ^ 2 := by
        calc
          2 * p + 1 ≤ 3 * p := by omega
          _ ≤ p * p := Nat.mul_le_mul_right p (le_trans (by decide : 3 ≤ 11) hp11)
          _ ≤ 4 * p * p := by
            have : p * p ≤ 4 * (p * p) := by
              simpa [Nat.one_mul, Nat.mul_comm] using
                Nat.mul_le_mul_left (p * p) (by decide : 1 ≤ 4)
            simpa [Nat.mul_assoc] using this
          _ = 4 * p ^ 2 := by rw [pow_two, Nat.mul_assoc]
      have hsum : 4 * qn * z ^ 2 + 5 * S + ((p ^ 2 - (8 * p + 4)) * z ^ 2
          + 10 * p ^ 2 * z + (4 * p ^ 2 - (2 * p + 1))) =
          5 * S * (p * z) + 4 * qn := by
        zify [hlead, htail]
        simp only [S, qn]
        push_cast
        ring
      have hstrict : 2 * p + 1 < 4 * p ^ 2 := by
        have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 11) hp11
        have h3 : 2 * p + 1 ≤ 3 * p := by
          have : 1 ≤ p := hp1
          omega
        have h4p : 3 < 4 * p := by
          have : 4 * 11 ≤ 4 * p := Nat.mul_le_mul_left 4 hp11
          omega
        calc
          2 * p + 1 ≤ 3 * p := h3
          _ < 4 * p * p := Nat.mul_lt_mul_of_pos_right h4p hp.pos
          _ = 4 * p ^ 2 := by rw [pow_two, Nat.mul_assoc]
      have hpos : 0 < (p ^ 2 - (8 * p + 4)) * z ^ 2 + 10 * p ^ 2 * z +
          (4 * p ^ 2 - (2 * p + 1)) := by
        have hlast : 0 < 4 * p ^ 2 - (2 * p + 1) := Nat.sub_pos_of_lt hstrict
        exact lt_of_lt_of_le hlast (Nat.le_add_left _ _)
      have hlt : 4 * qn * z ^ 2 + 5 * S < 5 * S * (p * z) + 4 * qn := by
        have hlt' : 4 * qn * z ^ 2 + 5 * S <
            (4 * qn * z ^ 2 + 5 * S) + ((p ^ 2 - (8 * p + 4)) * z ^ 2 +
              10 * p ^ 2 * z + (4 * p ^ 2 - (2 * p + 1))) :=
          Nat.lt_add_of_pos_right hpos
        rwa [hsum] at hlt'
      have hupper : N < 5 * M := by
        rw [hNeq, hMeq]
        simpa [Nat.mul_assoc] using hclear hlt
      exact absurd hdivM (not_dvd_gap hMpos hlo4 hupper)
    · have hpge : 3 ≤ p := by
        have := hp.two_le
        exact Nat.lt_of_le_of_ne this (Ne.symm hp2)
      have hplt : p < 11 := lt_of_not_ge hp11
      interval_cases p
      · -- p = 3. Exponent 3 sits in (6, 7); every larger odd exponent sits in (7, 8).
        by_cases ht1 : t = 1
        · have hp3 : p = 3 := by omega
          subst hp3
          subst ht1
          have hNlt : N < 7 * M := by
            rw [hNeq, hMeq]
            simp only [z]
            decide
          have hNgt : 6 * M < N := by
            rw [hNeq, hMeq]
            simp only [z]
            decide
          exact absurd hdivM (not_dvd_gap hMpos hNgt hNlt)
        · have ht2 : 2 ≤ t := by omega
          have hup : 4 * qn * z ^ 2 + 8 * S < 8 * S * (p * z) + 4 * qn := by
            have hsum : 4 * qn * z ^ 2 + 8 * S + (8 * z ^ 2 + 144 * z + 8) =
                8 * S * (p * z) + 4 * qn := by
              have hp3 : p = 3 := by omega
              simp only [hp3, S, qn]
              zify
              ring
            have hpos : 0 < 8 * z ^ 2 + 144 * z + 8 :=
              lt_of_lt_of_le (by decide : 0 < 8) (Nat.le_add_left _ _)
            have hlt' : 4 * qn * z ^ 2 + 8 * S <
                (4 * qn * z ^ 2 + 8 * S) + (8 * z ^ 2 + 144 * z + 8) :=
              Nat.lt_add_of_pos_right hpos
            rwa [hsum] at hlt'
          have hlow : 7 * S * (p * z) + 4 * qn < 4 * qn * z ^ 2 + 7 * S := by
            have hz243 : 243 ≤ z := by
              have hp3 : p = 3 := by omega
              have h5 : (3 : ℕ) ^ 5 = 243 := by decide
              have : (3 : ℕ) ^ 5 ≤ 3 ^ (2 * t + 1) :=
                Nat.pow_le_pow_right (by decide : 1 ≤ 3) (by omega : 5 ≤ 2 * t + 1)
              simpa [z, hp3, h5] using this
            have hrest : 126 * z + 15 ≤ z ^ 2 := by
              have hmul : 243 * z ≤ z ^ 2 := by
                rw [pow_two, Nat.mul_comm]
                exact Nat.mul_le_mul_left z hz243
              have h15 : 15 ≤ 117 * z := by
                have : 15 ≤ 117 * 243 := by decide
                exact le_trans this (Nat.mul_le_mul_left _ hz243)
              omega
            have hsum : 7 * S * (p * z) + 4 * qn + (z ^ 2 - (126 * z + 15)) =
                4 * qn * z ^ 2 + 7 * S := by
              have hp3 : p = 3 := by omega
              simp only [hp3, S, qn]
              zify [hrest]
              ring
            have hstrict : 126 * z + 15 < z ^ 2 := by
              have hmul : 243 * z ≤ z ^ 2 := by
                rw [pow_two, Nat.mul_comm]
                exact Nat.mul_le_mul_left z hz243
              have h15 : 15 < 117 * z := by
                have : 15 < 117 * 243 := by decide
                exact lt_of_lt_of_le this (Nat.mul_le_mul_left _ hz243)
              have hsumz : 126 * z + 15 < 243 * z := by
                have hlt := Nat.add_lt_add_left h15 (126 * z)
                have heq : 126 * z + 117 * z = 243 * z := by
                  have : (126 + 117) = 243 := by decide
                  rw [← Nat.add_mul, this]
                simpa [heq] using hlt
              exact lt_of_lt_of_le hsumz hmul
            have hpos : 0 < z ^ 2 - (126 * z + 15) := Nat.sub_pos_of_lt hstrict
            have hlt' : 7 * S * (p * z) + 4 * qn <
                (7 * S * (p * z) + 4 * qn) + (z ^ 2 - (126 * z + 15)) :=
              Nat.lt_add_of_pos_right hpos
            rwa [hsum] at hlt'
          have hp3 : p = 3 := by omega
          have hup3 : 4 * qn * z ^ 2 + 8 * S < 8 * S * (3 * z) + 4 * qn := by
            simpa [hp3] using hup
          have hlow3 : 7 * S * (3 * z) + 4 * qn < 4 * qn * z ^ 2 + 7 * S := by
            simpa [hp3] using hlow
          have hNlt : N < 8 * M := by
            rw [hNeq, hMeq]
            simpa [Nat.mul_assoc] using hclear hup3
          have hNgt : 7 * M < N := by
            rw [hMeq, hNeq]
            have hL : 4 * qn * z ^ 2 = 4 * qn * (z ^ 2 - 1) + 4 * qn := by
              have h := Nat.sub_add_cancel hz2
              conv_lhs => arg 2; rw [← h]
              rw [Nat.mul_add, Nat.mul_one]
            have hR : 7 * S * (3 * z) = 7 * S * (3 * z - 1) + 7 * S := by
              have hzpos : 0 < z := by
                have hne : z ≠ 0 := by
                  intro h
                  have : z ^ 2 = 0 := by simp [h, pow_two]
                  omega
                omega
              have hxz : 1 ≤ 3 * z := Nat.succ_le_of_lt (Nat.mul_pos (by decide : 0 < 3) hzpos)
              have h := Nat.sub_add_cancel hxz
              conv_lhs => arg 2; rw [← h]
              rw [Nat.mul_add, Nat.mul_one]
            have h' := hlow3
            rw [hL, hR] at h'
            have h'' : 7 * S * (3 * z - 1) + (7 * S + 4 * qn) <
                4 * qn * (z ^ 2 - 1) + (7 * S + 4 * qn) := by
              have hcomm : 4 * qn + 7 * S = 7 * S + 4 * qn := by ac_rfl
              simpa [Nat.add_assoc, hcomm] using h'
            have hlt : 7 * S * (3 * z - 1) < 4 * qn * (z ^ 2 - 1) :=
              Nat.lt_of_add_lt_add_right h''
            simpa [Nat.mul_assoc] using hlt
          exact absurd hdivM (not_dvd_gap hMpos hNgt hNlt)
      · exact absurd hp (by decide : ¬ Nat.Prime 4)
      · -- p = 5. 5 M < N < 6 M.
        have hup : 4 * qn * z ^ 2 + 6 * S < 6 * S * (p * z) + 4 * qn := by
          have hsum : 4 * qn * z ^ 2 + 6 * S + (6 * z ^ 2 + 300 * z + 78) =
              6 * S * (p * z) + 4 * qn := by
            have hp5 : p = 5 := by omega
            simp only [hp5, S, qn]
            zify
            ring
          have hpos : 0 < 6 * z ^ 2 + 300 * z + 78 :=
            lt_of_lt_of_le (by decide : 0 < 78) (Nat.le_add_left _ _)
          have hlt' : 4 * qn * z ^ 2 + 6 * S <
              (4 * qn * z ^ 2 + 6 * S) + (6 * z ^ 2 + 300 * z + 78) :=
            Nat.lt_add_of_pos_right hpos
          rwa [hsum] at hlt'
        have hlow : 5 * S * (p * z) + 4 * qn < 4 * qn * z ^ 2 + 5 * S := by
          have hz125 : 125 ≤ z := by
            have hp5 : p = 5 := by omega
            have h3 : (5 : ℕ) ^ 3 = 125 := by decide
            have : (5 : ℕ) ^ 3 ≤ 5 ^ (2 * t + 1) :=
              Nat.pow_le_pow_right (by decide : 1 ≤ 5) (by omega : 3 ≤ 2 * t + 1)
            simpa [z, hp5, h3] using this
          have hrest : 250 * z + 89 ≤ 19 * z ^ 2 := by
            have hmul : 19 * 125 * z ≤ 19 * z ^ 2 := by
              rw [pow_two]
              simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
                Nat.mul_le_mul_left (19 * z) hz125
            have h89 : 89 ≤ 2125 * z := by
              have : 89 ≤ 2125 * 125 := by decide
              exact le_trans this (Nat.mul_le_mul_left _ hz125)
            omega
          have hsum : 5 * S * (p * z) + 4 * qn + (19 * z ^ 2 - (250 * z + 89)) =
              4 * qn * z ^ 2 + 5 * S := by
            have hp5 : p = 5 := by omega
            simp only [hp5, S, qn]
            zify [hrest]
            ring
          have hstrict : 250 * z + 89 < 19 * z ^ 2 := by
            have hmul : 19 * 125 * z ≤ 19 * z ^ 2 := by
              rw [pow_two]
              simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
                Nat.mul_le_mul_left (19 * z) hz125
            have h89 : 89 < 2125 * z := by
              have : 89 < 2125 * 125 := by decide
              exact lt_of_lt_of_le this (Nat.mul_le_mul_left _ hz125)
            have hsumz : 250 * z + 89 < 19 * 125 * z := by
              have hlt := Nat.add_lt_add_left h89 (250 * z)
              have heq : 250 * z + 2125 * z = 19 * 125 * z := by
                have : (250 + 2125) = 19 * 125 := by decide
                rw [← Nat.add_mul, this]
              simpa [heq] using hlt
            exact lt_of_lt_of_le hsumz hmul
          have hpos : 0 < 19 * z ^ 2 - (250 * z + 89) := Nat.sub_pos_of_lt hstrict
          have hlt' : 5 * S * (p * z) + 4 * qn <
              (5 * S * (p * z) + 4 * qn) + (19 * z ^ 2 - (250 * z + 89)) :=
            Nat.lt_add_of_pos_right hpos
          rwa [hsum] at hlt'
        have hp5 : p = 5 := by omega
        have hup5 : 4 * qn * z ^ 2 + 6 * S < 6 * S * (5 * z) + 4 * qn := by
          simpa [hp5] using hup
        have hlow5 : 5 * S * (5 * z) + 4 * qn < 4 * qn * z ^ 2 + 5 * S := by
          simpa [hp5] using hlow
        have hNlt : N < 6 * M := by
          rw [hNeq, hMeq]
          simpa [Nat.mul_assoc] using hclear hup5
        have hNgt : 5 * M < N := by
          rw [hMeq, hNeq]
          have hL : 4 * qn * z ^ 2 = 4 * qn * (z ^ 2 - 1) + 4 * qn := by
            have h := Nat.sub_add_cancel hz2
            conv_lhs => arg 2; rw [← h]
            rw [Nat.mul_add, Nat.mul_one]
          have hR : 5 * S * (5 * z) = 5 * S * (5 * z - 1) + 5 * S := by
            have hzpos : 0 < z := by
              have hne : z ≠ 0 := by
                intro h
                have : z ^ 2 = 0 := by simp [h, pow_two]
                omega
              omega
            have hxz : 1 ≤ 5 * z := Nat.succ_le_of_lt (Nat.mul_pos (by decide : 0 < 5) hzpos)
            have h := Nat.sub_add_cancel hxz
            conv_lhs => arg 2; rw [← h]
            rw [Nat.mul_add, Nat.mul_one]
          have h' := hlow5
          rw [hL, hR] at h'
          have h'' : 5 * S * (5 * z - 1) + (5 * S + 4 * qn) <
              4 * qn * (z ^ 2 - 1) + (5 * S + 4 * qn) := by
            have hcomm : 4 * qn + 5 * S = 5 * S + 4 * qn := by ac_rfl
            simpa [Nat.add_assoc, hcomm] using h'
          have hlt : 5 * S * (5 * z - 1) < 4 * qn * (z ^ 2 - 1) :=
            Nat.lt_of_add_lt_add_right h''
          simpa [Nat.mul_assoc] using hlt
        exact absurd hdivM (not_dvd_gap hMpos hNgt hNlt)
      · exact absurd hp (by decide : ¬ Nat.Prime 6)
      · -- p = 7. 5 M < N < 6 M.
        have hup : 4 * qn * z ^ 2 + 6 * S < 6 * S * (p * z) + 4 * qn := by
          have hsum : 4 * qn * z ^ 2 + 6 * S + (38 * z ^ 2 + 588 * z + 166) =
              6 * S * (p * z) + 4 * qn := by
            have hp7 : p = 7 := by omega
            simp only [hp7, S, qn]
            zify
            ring
          have hpos : 0 < 38 * z ^ 2 + 588 * z + 166 :=
            lt_of_lt_of_le (by decide : 0 < 166) (Nat.le_add_left _ _)
          have hlt' : 4 * qn * z ^ 2 + 6 * S <
              (4 * qn * z ^ 2 + 6 * S) + (38 * z ^ 2 + 588 * z + 166) :=
            Nat.lt_add_of_pos_right hpos
          rwa [hsum] at hlt'
        have hlow : 5 * S * (p * z) + 4 * qn < 4 * qn * z ^ 2 + 5 * S := by
          have hz343 : 343 ≤ z := by
            have hp7 : p = 7 := by omega
            have h3 : (7 : ℕ) ^ 3 = 343 := by decide
            have : (7 : ℕ) ^ 3 ≤ 7 ^ (2 * t + 1) :=
              Nat.pow_le_pow_right (by decide : 1 ≤ 7) (by omega : 3 ≤ 2 * t + 1)
            simpa [z, hp7, h3] using this
          have hrest : 490 * z + 181 ≤ 11 * z ^ 2 := by
            have hmul : 11 * 343 * z ≤ 11 * z ^ 2 := by
              rw [pow_two]
              simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
                Nat.mul_le_mul_left (11 * z) hz343
            have h181 : 181 ≤ 3283 * z := by
              have : 181 ≤ 3283 * 343 := by decide
              exact le_trans this (Nat.mul_le_mul_left _ hz343)
            omega
          have hsum : 5 * S * (p * z) + 4 * qn + (11 * z ^ 2 - (490 * z + 181)) =
              4 * qn * z ^ 2 + 5 * S := by
            have hp7 : p = 7 := by omega
            simp only [hp7, S, qn]
            zify [hrest]
            ring
          have hstrict : 490 * z + 181 < 11 * z ^ 2 := by
            have hmul : 11 * 343 * z ≤ 11 * z ^ 2 := by
              rw [pow_two]
              simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
                Nat.mul_le_mul_left (11 * z) hz343
            have h181 : 181 < 3283 * z := by
              have : 181 < 3283 * 343 := by decide
              exact lt_of_lt_of_le this (Nat.mul_le_mul_left _ hz343)
            have hsumz : 490 * z + 181 < 11 * 343 * z := by
              have hlt := Nat.add_lt_add_left h181 (490 * z)
              have heq : 490 * z + 3283 * z = 11 * 343 * z := by
                have : (490 + 3283) = 11 * 343 := by decide
                rw [← Nat.add_mul, this]
              simpa [heq] using hlt
            exact lt_of_lt_of_le hsumz hmul
          have hpos : 0 < 11 * z ^ 2 - (490 * z + 181) := Nat.sub_pos_of_lt hstrict
          have hlt' : 5 * S * (p * z) + 4 * qn <
              (5 * S * (p * z) + 4 * qn) + (11 * z ^ 2 - (490 * z + 181)) :=
            Nat.lt_add_of_pos_right hpos
          rwa [hsum] at hlt'
        have hp7 : p = 7 := by omega
        have hup7 : 4 * qn * z ^ 2 + 6 * S < 6 * S * (7 * z) + 4 * qn := by
          simpa [hp7] using hup
        have hlow7 : 5 * S * (7 * z) + 4 * qn < 4 * qn * z ^ 2 + 5 * S := by
          simpa [hp7] using hlow
        have hNlt : N < 6 * M := by
          rw [hNeq, hMeq]
          simpa [Nat.mul_assoc] using hclear hup7
        have hNgt : 5 * M < N := by
          rw [hMeq, hNeq]
          have hL : 4 * qn * z ^ 2 = 4 * qn * (z ^ 2 - 1) + 4 * qn := by
            have h := Nat.sub_add_cancel hz2
            conv_lhs => arg 2; rw [← h]
            rw [Nat.mul_add, Nat.mul_one]
          have hR : 5 * S * (7 * z) = 5 * S * (7 * z - 1) + 5 * S := by
            have hzpos : 0 < z := by
              have hne : z ≠ 0 := by
                intro h
                have : z ^ 2 = 0 := by simp [h, pow_two]
                omega
              omega
            have hxz : 1 ≤ 7 * z := Nat.succ_le_of_lt (Nat.mul_pos (by decide : 0 < 7) hzpos)
            have h := Nat.sub_add_cancel hxz
            conv_lhs => arg 2; rw [← h]
            rw [Nat.mul_add, Nat.mul_one]
          have h' := hlow7
          rw [hL, hR] at h'
          have h'' : 5 * S * (7 * z - 1) + (5 * S + 4 * qn) <
              4 * qn * (z ^ 2 - 1) + (5 * S + 4 * qn) := by
            have hcomm : 4 * qn + 5 * S = 5 * S + 4 * qn := by ac_rfl
            simpa [Nat.add_assoc, hcomm] using h'
          have hlt : 5 * S * (7 * z - 1) < 4 * qn * (z ^ 2 - 1) :=
            Nat.lt_of_add_lt_add_right h''
          simpa [Nat.mul_assoc] using hlt
        exact absurd hdivM (not_dvd_gap hMpos hNgt hNlt)
      · exact absurd hp (by decide : ¬ Nat.Prime 8)
      · exact absurd hp (by decide : ¬ Nat.Prime 9)
      · exact absurd hp (by decide : ¬ Nat.Prime 10)

end
