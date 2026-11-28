import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-! # Generic rank of six-slice complex tensors with consecutive sides

For 6 ≤ m < 20 the complex generic CP rank of format 6 × m × (m+1) is
3m−3. For m ≥ 20 it is 3m−4. The theorem
`CriticalTensor.SixConsecutive.generic_rank` gives the dimension-count
formula on a dense open subset of the tensor space.

This is the six-slice consecutive family in Shmuel Friedland,
[On the generic and typical ranks of 3-tensors, Conjecture 5.1](https://arxiv.org/abs/0805.3777).
The tensor and generic-rank definitions come from the Formal Conjectures
Authors' TensorRank module. The dense-open tangent upper bound and
dimension-count lower bound reuse the [first critical-format reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3300).
The rectangular growth theorem and the two-coordinate cross construction
also appear in the [three- and five-slice consecutive proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/13485).
Here a tiled border propagates four finite configurations, at m = 6, 7, 20,
and 21. Their binary rank certificates lift to the same configurations over
the complex numbers.
-/

namespace CriticalReduction

open Arxiv.«0805.3777» Set Filter
open scoped Topology

lemma interior_polynomial_zero_locus {J : Type} (P : MvPolynomial J ℂ) (hP : P ≠ 0) :
    interior {y : J → ℂ | MvPolynomial.eval y P = 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hn := mem_interior_iff_mem_nhds.mp ha
  rw [nhds_pi, Filter.mem_pi] at hn
  obtain ⟨I, _, box, hin, hsub⟩ := hn
  apply hP
  apply MvPolynomial.funext_set box (fun j => infinite_of_mem_nhds (a j) (hin j))
  intro y hy
  have hyI : y ∈ I.pi box := fun j _ => hy j (Set.mem_univ _)
  have hzero : MvPolynomial.eval y P = 0 := hsub hyI
  simpa only [map_zero] using hzero

lemma eval_substitution {I J : Type} (F : J → MvPolynomial I ℂ) (x : I → ℂ)
    (P : MvPolynomial J ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval F P) =
      MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P := by
  have he : (MvPolynomial.aeval x).comp (MvPolynomial.aeval F) =
      MvPolynomial.aeval (fun j => MvPolynomial.eval x (F j)) := by
    ext j
    simp [MvPolynomial.aeval_eq_eval]
  exact DFunLike.congr_fun he P

lemma vanishing_on_polynomial_image {I J : Type} [Fintype I] [Fintype J]
    (hd : Fintype.card I < Fintype.card J) (F : J → MvPolynomial I ℂ) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ x : I → ℂ, MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P = 0 := by
  classical
  have hn : ¬ AlgebraicIndependent ℂ F := by
    intro h
    have hc := h.cardinalMk_le_trdeg
    rw [MvPolynomial.trdeg_of_isDomain] at hc
    have : Fintype.card J ≤ Fintype.card I := by simpa [Cardinal.mk_fintype] using hc
    omega
  rw [algebraicIndependent_iff] at hn
  push Not at hn
  obtain ⟨P, ha, hP⟩ := hn
  refine ⟨P, hP, ?_⟩
  intro x
  rw [← eval_substitution F x P, ha, map_zero]

/-- Agreement with a lower-dimensional chart on a product of infinite subsets
extends to a polynomial identity on the entire parameter space. -/
lemma generic_chart_relation {I J K : Type} [Fintype I] [Fintype J]
    (hd : Fintype.card I < Fintype.card J) (chart : J → MvPolynomial I ℂ)
    (full : J → MvPolynomial K ℂ)
    (hnormal : ∀ x : K → ℂ, (∀ i, x i ≠ 0) →
      ∃ y : I → ℂ, ∀ j, MvPolynomial.eval x (full j) = MvPolynomial.eval y (chart j)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ x : K → ℂ, MvPolynomial.eval (fun j => MvPolynomial.eval x (full j)) P = 0 := by
  classical
  obtain ⟨P, hP, hvanish⟩ := vanishing_on_polynomial_image hd chart
  have hpoly : MvPolynomial.aeval full P = 0 := by
    apply MvPolynomial.funext_set (fun _ : K => ({0}ᶜ : Set ℂ))
      (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl)
    intro x hx
    have hx0 (i : K) : x i ≠ 0 := hx i (Set.mem_univ _)
    obtain ⟨y, hy⟩ := hnormal x hx0
    rw [eval_substitution full x P, funext hy, map_zero]
    exact hvanish y
  refine ⟨P, hP, fun x => ?_⟩
  rw [← eval_substitution full x P, hpoly, map_zero]

lemma zero_is_simple (ds : List ℕ) : Holor.CPRankMax1 (0 : Holor ℂ ds) := by
  induction ds with
  | nil => exact .nil _
  | cons n ds ih =>
    have h := Holor.CPRankMax1.cons (0 : Holor ℂ [n]) (0 : Holor ℂ ds) ih
    have he : Holor.mul (0 : Holor ℂ [n]) (0 : Holor ℂ ds) = (0 : Holor ℂ (n :: ds)) := by
      funext i
      change (0 : ℂ) * 0 = 0
      simp
    rwa [he] at h

lemma decomposition_of_rank_bound {ds : List ℕ} (T : Holor ℂ ds) (r : ℕ) (hr : T.cprank ≤ r) :
    Holor.CPRankMax r T := by
  classical
  have hmin : Holor.CPRankMax T.cprank T :=
    Nat.find_spec (p := fun k => Holor.CPRankMax k T) ⟨ds.prod, Holor.cprankMax_upper_bound T⟩
  induction r, hr using Nat.le_induction with
  | base => exact hmin
  | succ k _ ih => simpa using Holor.CPRankMax.succ k 0 T (zero_is_simple ds) ih

lemma finite_sum_of_simple {ds : List ℕ} {r : ℕ} {T : Holor ℂ ds} (h : Holor.CPRankMax r T) :
    ∃ u : Fin r → Holor ℂ ds, (∀ i, Holor.CPRankMax1 (u i)) ∧ ∑ i, u i = T := by
  induction h with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | succ k x y hx hy ih =>
    obtain ⟨u, hu, hs⟩ := ih
    refine ⟨Fin.cons x u, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using hu j
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hs]

/-- The explicit triple of natural-number indices in a rectangular holor. -/
lemma rectangular_indices (d e f : ℕ) :
    ∃ E : HolorIndex [d,e,f] ≃ Fin d × Fin e × Fin f, ∀ (i : Fin d) (j : Fin e) (k : Fin f),
      E.symm (i,j,k) = ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩ := by
  let mk (z : Fin d × Fin e × Fin f) : HolorIndex [d,e,f] :=
    ⟨[z.1.val,z.2.1.val,z.2.2.val],.cons z.1.isLt (.cons z.2.1.isLt (.cons z.2.2.isLt .nil))⟩
  have hb : Function.Bijective mk := by
    constructor
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
      have he := congrArg Subtype.val h
      simp [mk] at he
      exact Prod.ext (Fin.ext he.1) (Prod.ext (Fin.ext he.2.1) (Fin.ext he.2.2))
    · rintro ⟨is,h⟩
      cases h with | cons hi h =>
        cases h with | cons hj h =>
          cases h with | cons hk h =>
            cases h
            exact ⟨(⟨_,hi⟩,⟨_,hj⟩,⟨_,hk⟩),rfl⟩
  exact ⟨(Equiv.ofBijective mk hb).symm, fun _ _ _ => rfl⟩

/-- Absorb the trailing scalar of a simple holor into its last vector. -/
lemma simple_coordinates {d e f : ℕ} {T : Holor ℂ [d,e,f]} (h : Holor.CPRankMax1 T) :
    ∃ (a : Fin d → ℂ) (b : Fin e → ℂ) (c : Fin f → ℂ), ∀ i j k,
      T ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩ = a i * b j * c k := by
  cases h with
  | cons a yz hyz =>
    cases hyz with
    | cons b zs hzs =>
      cases hzs with
      | cons c z hz =>
        refine ⟨fun i => a ⟨[i.val],.cons i.isLt .nil⟩,
          fun j => b ⟨[j.val],.cons j.isLt .nil⟩,
          fun k => c ⟨[k.val],.cons k.isLt .nil⟩ * z ⟨[],.nil⟩, ?_⟩
        intro i j k
        change a _ * (b _ * (c _ * z _)) = a _ * b _ * (c _ * z _)
        rw [mul_assoc]
        rfl

/-- A low-rank holor is a coordinatewise sum of products of vector entries. -/
lemma sum_coordinates {d e f : ℕ} (E : HolorIndex [d,e,f] ≃ Fin d × Fin e × Fin f)
    (hE : ∀ (i : Fin d) (j : Fin e) (k : Fin f),
      E.symm (i,j,k) = ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩)
    (T : Holor ℂ [d,e,f]) (r : ℕ) (hr : T.cprank ≤ r) :
    ∃ (a : Fin r → Fin d → ℂ) (b : Fin r → Fin e → ℂ) (c : Fin r → Fin f → ℂ),
      ∀ q, (∑ t, a t (E q).1 * b t (E q).2.1 * c t (E q).2.2) = T q := by
  classical
  obtain ⟨u,hu,hT⟩ := finite_sum_of_simple (decomposition_of_rank_bound T r hr)
  choose a b c habc using fun t => simple_coordinates (hu t)
  refine ⟨a,b,c,fun q => ?_⟩
  have term (t : Fin r) := habc t (E q).1 (E q).2.1 (E q).2.2
  have at_q := Finset.sum_apply (M := fun _ : HolorIndex [d,e,f] => ℂ) q
    (Finset.univ : Finset (Fin r)) (fun t => fun v => u t v)
  refine (Finset.sum_congr rfl (fun t _ => ?_)).trans (at_q.symm.trans (congrFun hT q))
  simpa only [← hE,Prod.mk.eta,Equiv.symm_apply_apply] using (term t).symm

/-- Scaling the first two factors to first coordinate one removes two
parameters per summand. Their product is absorbed into the third factor. -/
lemma rectangular_polynomial {J : Type} [Fintype J] (d e f r : ℕ)
    (E : J ≃ Fin (d+1) × Fin (e+1) × Fin f) (hd : r*(d+(e+f)) < Fintype.card J) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ (a : Fin r → Fin (d+1) → ℂ) (b : Fin r → Fin (e+1) → ℂ) (c : Fin r → Fin f → ℂ),
        MvPolynomial.eval (fun q => ∑ t, a t (E q).1 * b t (E q).2.1 * c t (E q).2.2) P = 0 := by
  classical
  let Raw := Fin r × (Fin (d+1) ⊕ (Fin (e+1) ⊕ Fin f))
  let Chart := Fin r × (Fin d ⊕ (Fin e ⊕ Fin f))
  let raw (q : J) : MvPolynomial Raw ℂ :=
    ∑ t : Fin r, MvPolynomial.X (t,Sum.inl (E q).1) * MvPolynomial.X (t,Sum.inr (Sum.inl (E q).2.1)) *
      MvPolynomial.X (t,Sum.inr (Sum.inr (E q).2.2))
  let chart (q : J) : MvPolynomial Chart ℂ :=
    ∑ t : Fin r, Fin.cases 1 (fun i => MvPolynomial.X (t,Sum.inl i)) (E q).1 *
      Fin.cases 1 (fun j => MvPolynomial.X (t,Sum.inr (Sum.inl j))) (E q).2.1 *
      MvPolynomial.X (t,Sum.inr (Sum.inr (E q).2.2))
  have hnorm (x : Raw → ℂ) (hx : ∀ j, x j ≠ 0) :
      ∃ y : Chart → ℂ, ∀ q, MvPolynomial.eval x (raw q) = MvPolynomial.eval y (chart q) := by
    let y : Chart → ℂ := fun (t,s) => match s with
      | .inl i => x (t,.inl i.succ) / x (t,.inl 0)
      | .inr (.inl j) => x (t,.inr (.inl j.succ)) / x (t,.inr (.inl 0))
      | .inr (.inr k) => x (t,.inr (.inr k)) * x (t,.inl 0) * x (t,.inr (.inl 0))
    refine ⟨y,fun q => ?_⟩
    simp only [raw,chart,map_sum,map_mul,MvPolynomial.eval_X]
    apply Finset.sum_congr rfl
    intro t _
    have ha (i : Fin (d+1)) :
        MvPolynomial.eval y (Fin.cases 1 (fun i : Fin d => MvPolynomial.X (t,Sum.inl i)) i) =
          x (t,.inl i) / x (t,.inl 0) := by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hx]
      · simp [y]
    have hb (j : Fin (e+1)) :
        MvPolynomial.eval y (Fin.cases 1 (fun j : Fin e => MvPolynomial.X (t,Sum.inr (Sum.inl j))) j) =
          x (t,.inr (.inl j)) / x (t,.inr (.inl 0)) := by
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [hx]
      · simp [y]
    rw [ha,hb]
    dsimp only [y]
    field_simp [hx]
  have hcard : Fintype.card Chart < Fintype.card J := by
    simpa only [Chart,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin] using hd
  obtain ⟨P,hP,hzero⟩ := generic_chart_relation hcard chart raw hnorm
  refine ⟨P,hP,fun a b c => ?_⟩
  let x : Raw → ℂ := fun (t,s) => match s with
    | .inl i => a t i
    | .inr (.inl j) => b t j
    | .inr (.inr k) => c t k
  simpa only [raw,x,map_sum,map_mul,MvPolynomial.eval_X] using hzero x

/-- For any rectangular format, ranks whose normalized parameter count falls
below the number of tensor entries have nowhere dense closure. -/
theorem lower_of_count (a b c r : ℕ) (hdim : (a+b+c-2)*r < a*b*c) :
    interior (closure {T : Holor ℂ [a,b,c] | T.cprank ≤ r}) = ∅ := by
  classical
  obtain _|d := a
  · simp at hdim
  obtain _|e := b
  · simp at hdim
  obtain ⟨E,hE⟩ := rectangular_indices (d+1) (e+1) c
  let _ : Fintype (HolorIndex [d+1,e+1,c]) := Fintype.ofEquiv _ E.symm
  have hd : r*(d+(e+c)) < Fintype.card (HolorIndex [d+1,e+1,c]) := by
    rw [Fintype.card_congr E]
    have h : d.succ+e.succ+c-2 = d+(e+c) := by omega
    simpa only [Fintype.card_prod,Fintype.card_fin,h,Nat.mul_comm (d+(e+c)) r,Nat.mul_assoc,
      Nat.succ_eq_add_one] using hdim
  obtain ⟨P,hP,hzero⟩ := rectangular_polynomial d e c r E hd
  let Z := {T : Holor ℂ [d+1,e+1,c] | MvPolynomial.eval T P = 0}
  have hclosed : IsClosed Z := isClosed_eq (MvPolynomial.continuous_eval P) continuous_const
  have hsub : {T : Holor ℂ [d+1,e+1,c] | T.cprank ≤ r} ⊆ Z := by
    intro T hT
    obtain ⟨x,y,z,h⟩ := sum_coordinates E hE T r hT
    change MvPolynomial.eval T P = 0
    simpa only [funext h] using hzero x y z
  have hempty : interior Z = ∅ := interior_polynomial_zero_locus P hP
  apply Set.subset_empty_iff.mp
  simpa only [hempty] using interior_mono (closure_minimal hsub hclosed)

end CriticalReduction

namespace CriticalReduction.Dominance

open Set Filter
open scoped Topology Classical

lemma vector_is_simple {n : ℕ} (v : Holor ℂ [n]) : Holor.CPRankMax1 v := by
  let oneScalar : Holor ℂ [] := fun _ => 1
  have he : Holor.mul v oneScalar = v := by
    funext t
    change v t.take * (1 : ℂ) = v t
    rw [mul_one]
    congr 1
    apply Subtype.ext
    exact List.take_of_length_le t.property.length_eq.le
  rw [← he]
  exact Holor.CPRankMax1.cons _ _ (.nil _)

lemma tensor_sum_rank {d e f r : ℕ} (a : Fin r → Holor ℂ [d])
    (b : Fin r → Holor ℂ [e]) (c : Fin r → Holor ℂ [f]) :
    Holor.CPRankMax r (∑ i, Holor.mul (a i) (Holor.mul (b i) (c i))) := by
  have hs (i : Fin r) : Holor.CPRankMax1 (Holor.mul (a i) (Holor.mul (b i) (c i))) :=
    .cons _ _ (.cons _ _ (vector_is_simple (c i)))
  simpa using Holor.cprankMax_sum (n := 1) Finset.univ
    (fun i => Holor.mul (a i) (Holor.mul (b i) (c i))) (fun i _ => Holor.cprankMax_1 (hs i))

/-- A constructible spectral image containing the generic point contains a
principal open neighborhood of it. -/
lemma open_in_spectral_image {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hfp : φ.FinitePresentation) :
    ∃ f : A, f ≠ 0 ∧ ∀ q : PrimeSpectrum A, f ∉ q.asIdeal →
      q ∈ Set.range (PrimeSpectrum.comap φ) := by
  classical
  let z : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let w : PrimeSpectrum B := ⟨⊥, inferInstance⟩
  have hg : PrimeSpectrum.comap φ w = z := by
    apply PrimeSpectrum.ext
    change Ideal.comap φ ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp hinj
  obtain ⟨T, hT⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_range_comap hfp)
  have hz : z ∈ T.toSet := by rw [hT]; exact ⟨w, hg⟩
  obtain ⟨C, hC, hzC⟩ := Set.mem_iUnion₂.mp hz
  change z ∈ PrimeSpectrum.zeroLocus (Set.range C.g) ∧
    z ∉ PrimeSpectrum.zeroLocus {C.f} at hzC
  have hg0 (i : Fin C.n) : C.g i = 0 := by
    have h := (PrimeSpectrum.mem_zeroLocus z _).mp hzC.1 (Set.mem_range_self i)
    exact (Ideal.mem_bot : C.g i ∈ (⊥ : Ideal A) ↔ _).mp h
  have hf0 : C.f ≠ 0 := by
    intro e
    apply hzC.2
    exact (PrimeSpectrum.mem_zeroLocus z _).mpr (Set.singleton_subset_iff.mpr (e ▸ z.asIdeal.zero_mem))
  refine ⟨C.f, hf0, ?_⟩
  intro q hq
  rw [← hT]
  apply Set.mem_iUnion₂.mpr
  refine ⟨C, hC, ?_⟩
  constructor
  · apply (PrimeSpectrum.mem_zeroLocus q _).mpr
    rintro _ ⟨i, rfl⟩
    rw [hg0 i]
    exact q.asIdeal.zero_mem
  · intro e
    exact hq ((PrimeSpectrum.mem_zeroLocus q _).mp e (Set.mem_singleton _))

/-- Hilbert's Nullstellensatz converts the principal open in the spectral image
to actual complex points in the image of the polynomial map. -/
lemma principal_open_in_image {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧ ∀ y : J → ℂ, MvPolynomial.eval y P ≠ 0 →
      ∃ x : I → ℂ, ∀ j, MvPolynomial.eval x (F j) = y j := by
  classical
  let φ : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ := MvPolynomial.aeval F
  have hfp : φ.toRingHom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial J ℂ))
    have he : φ.toRingHom.comp (algebraMap ℂ (MvPolynomial J ℂ)) =
        algebraMap ℂ (MvPolynomial I ℂ) :=
      RingHom.ext (fun a => φ.commutes a)
    rw [he]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨P, hP, hU⟩ := open_in_spectral_image φ.toRingHom hinj hfp
  refine ⟨P, hP, ?_⟩
  intro y hy
  let m := MvPolynomial.pointToPoint (k := ℂ) y
  have hy' : P ∉ m.asIdeal := fun h => hy ((MvPolynomial.mem_vanishingIdeal_singleton_iff y P).mp h)
  obtain ⟨q, hq⟩ := hU m hy'
  obtain ⟨M, hM, hle⟩ := q.asIdeal.exists_le_maximal q.isPrime.ne_top
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨x, ?_⟩
  intro j
  let v : MvPolynomial J ℂ := MvPolynomial.X j - MvPolynomial.C (y j)
  have hv : v ∈ m.asIdeal := by
    apply (MvPolynomial.mem_vanishingIdeal_singleton_iff y _).mpr
    simp [v]
  have hvq : φ v ∈ q.asIdeal := by
    change v ∈ (PrimeSpectrum.comap φ.toRingHom q).asIdeal
    rwa [hq]
  have hMx := hle hvq
  rw [hx] at hMx
  have he := (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).mp hMx
  simpa [φ, v, MvPolynomial.aeval_eq_eval, sub_eq_zero] using he

lemma dense_image_interior_of_nonempty {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (h : (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))).Nonempty) :
    Dense (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))) := by
  classical
  let image := Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j))
  have hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ) := by
    apply algebraicIndependent_iff_injective_aeval.mp
    apply algebraicIndependent_iff.mpr
    intro Q hQ
    by_contra hne
    have hs : image ⊆ {y : J → ℂ | MvPolynomial.eval y Q = 0} := by
      rintro _ ⟨x, rfl⟩
      change MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) Q = 0
      rw [← eval_substitution F x Q, hQ, map_zero]
    obtain ⟨y, hy⟩ := h
    have bad := interior_mono hs hy
    rw [interior_polynomial_zero_locus Q hne] at bad
    exact bad
  obtain ⟨P, hP, hsurj⟩ := principal_open_in_image F hinj
  let Z := {y : J → ℂ | MvPolynomial.eval y P = 0}
  have ho : IsOpen Zᶜ := (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).isOpen_compl
  have hd : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp (interior_polynomial_zero_locus P hP)
  apply hd.mono
  apply interior_maximal _ ho
  intro y hy
  obtain ⟨x, hx⟩ := hsurj y hy
  exact ⟨x, funext hx⟩

/-- The derivative of each coordinate is the sum of its three factor variations. -/
lemma trilinear_image_has_interior {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    (a b c : S → J → I) (base : I → ℂ)
    (hspan : ∀ y : J → ℂ, ∃ z : I → ℂ, ∀ j,
      y j = ∑ t : S, (z (a t j) * (base (b t j) * base (c t j)) +
        base (a t j) * (z (b t j) * base (c t j)) +
        base (a t j) * (base (b t j) * z (c t j)))) :
    (interior (Set.range (fun x : I → ℂ => fun j : J =>
      ∑ t : S, x (a t j) * (x (b t j) * x (c t j))))).Nonempty := by
  classical
  let φ (x : I → ℂ) (j : J) := ∑ t : S, x (a t j) * (x (b t j) * x (c t j))
  let pr (i : I) : (I → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  let D : (I → ℂ) →L[ℂ] (J → ℂ) := ContinuousLinearMap.pi fun j =>
    ∑ t : S, (base (a t j) • (base (b t j) • pr (c t j) + base (c t j) • pr (b t j)) +
      (base (b t j) * base (c t j)) • pr (a t j))
  have hder : HasStrictFDerivAt φ D base := by
    apply hasStrictFDerivAt_pi.mpr
    intro j
    apply HasStrictFDerivAt.fun_sum
    intro t _
    exact (pr (a t j)).hasStrictFDerivAt.fun_mul
      ((pr (b t j)).hasStrictFDerivAt.fun_mul (pr (c t j)).hasStrictFDerivAt)
  have hsurj : Function.Surjective D := by
    intro y
    obtain ⟨z, hz⟩ := hspan y
    refine ⟨z, funext fun j => ?_⟩
    rw [hz j]
    simp only [D, ContinuousLinearMap.pi_apply, _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul, pr,
      ContinuousLinearMap.proj_apply]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hN : Set.range φ ∈ 𝓝 (φ base) := by
    rw [← hder.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)]
    exact Filter.range_mem_map
  exact ⟨φ base, mem_interior_iff_mem_nhds.mpr hN⟩

lemma eval_holor_sum {ds : List ℕ} {r : ℕ} (u : Fin r → Holor ℂ ds) (j : HolorIndex ds) :
    (∑ i, u i) j = ∑ i, u i j :=
  Finset.sum_apply (M := fun _ : HolorIndex ds => ℂ) j Finset.univ (fun i x => u i x)

end CriticalReduction.Dominance

namespace CriticalReduction

open Dominance
open Arxiv.«0805.3777»

/-- If the derivative of the sum of simple tensors is surjective at one
configuration, a dense open set has CP rank at most the number of summands. -/
theorem upper_of_witness {a b c r : ℕ} (h :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin c → ℂ, ∀ i j k, T i j k = ∑ t, (u t i*(y t j*z t k) +
          x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    ∃ U : Set (Holor ℂ [a,b,c]), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank ≤ r := by
  classical
  obtain ⟨x,y,z,hspan⟩ := h
  let consIdx (n : ℕ) (ds : List ℕ) : HolorIndex (n :: ds) ≃ Fin n × HolorIndex ds := {
    toFun := fun
      | ⟨i :: is, h⟩ => (⟨i, (List.forall₂_cons.mp h).1⟩, ⟨is, (List.forall₂_cons.mp h).2⟩)
      | ⟨[], h⟩ => nomatch h
    invFun := fun q => ⟨q.1.val :: q.2.val, List.Forall₂.cons q.1.isLt q.2.property⟩
    left_inv := by
      rintro ⟨l, hl⟩
      cases l with
      | nil => cases hl
      | cons i is => rfl
    right_inv := by rintro ⟨⟨i, hi⟩, ⟨is, his⟩⟩; rfl }
  let nilIdx : HolorIndex [] ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨[], .nil⟩
    left_inv := by rintro ⟨l, hl⟩; cases hl; rfl
    right_inv := by intro q; cases q; rfl }
  let point (i : Fin a) (j : Fin b) (k : Fin c) : HolorIndex [a,b,c] :=
    ⟨[i.val,j.val,k.val], .cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩
  have triple (q : HolorIndex [a,b,c]) : ∃ i j k, q = point i j k := by
    obtain ⟨⟨i,q⟩,rfl⟩ := (consIdx a [b,c]).symm.surjective q
    obtain ⟨⟨j,q⟩,rfl⟩ := (consIdx b [c]).symm.surjective q
    obtain ⟨⟨k,q⟩,rfl⟩ := (consIdx c []).symm.surjective q
    obtain ⟨⟨⟩,rfl⟩ := nilIdx.symm.surjective q
    exact ⟨i,j,k,rfl⟩
  let _ : Finite (HolorIndex [a,b,c]) := Finite.of_surjective
    (fun q : Fin a × Fin b × Fin c => point q.1 q.2.1 q.2.2) (by
      intro q
      obtain ⟨i,j,k,rfl⟩ := triple q
      exact ⟨(i,j,k),rfl⟩)
  let _ : Fintype (HolorIndex [a,b,c]) := Fintype.ofFinite _
  let P := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
  let entry {n : ℕ} (q : HolorIndex [n]) : Fin n := (consIdx n [] q).1
  let first (t : Fin r) (q : HolorIndex [a,b,c]) : P :=
    (t, Sum.inl (entry (HolorIndex.take (ds₁ := [a]) (ds₂ := [b,c]) q)))
  let second (t : Fin r) (q : HolorIndex [a,b,c]) : P :=
    (t, Sum.inr (.inl (entry (HolorIndex.take (ds₁ := [b]) (ds₂ := [c])
      (HolorIndex.drop (ds₁ := [a]) (ds₂ := [b,c]) q)))))
  let third (t : Fin r) (q : HolorIndex [a,b,c]) : P :=
    (t, Sum.inr (.inr (entry (HolorIndex.drop (ds₁ := [b]) (ds₂ := [c])
      (HolorIndex.drop (ds₁ := [a]) (ds₂ := [b,c]) q)))))
  let pack (A : Fin r → Fin a → ℂ) (B : Fin r → Fin b → ℂ) (C : Fin r → Fin c → ℂ) (q : P) : ℂ :=
    q.2.elim (A q.1) (Sum.elim (B q.1) (C q.1))
  let φ (v : P → ℂ) (q : HolorIndex [a,b,c]) :=
    ∑ t : Fin r, v (first t q) * (v (second t q) * v (third t q))
  have hopen : (interior (Set.range φ)).Nonempty := by
    apply trilinear_image_has_interior first second third (pack x y z)
    intro Y
    obtain ⟨u,v,w,hw⟩ := hspan fun i j k => Y (point i j k)
    refine ⟨pack u v w, ?_⟩
    intro q
    obtain ⟨i,j,k,rfl⟩ := triple q
    exact hw i j k
  let F (q : HolorIndex [a,b,c]) : MvPolynomial P ℂ :=
    ∑ t : Fin r, MvPolynomial.X (first t q) *
      (MvPolynomial.X (second t q) * MvPolynomial.X (third t q))
  have he : (fun v : P → ℂ => fun q => MvPolynomial.eval v (F q)) = φ := by
    funext v q
    simp [F, φ]
  have hd := dense_image_interior_of_nonempty F (by rw [he]; exact hopen)
  rw [he] at hd
  refine ⟨interior (Set.range φ),isOpen_interior,hd,?_⟩
  intro T hT
  obtain ⟨v,rfl⟩ := interior_subset hT
  let fa (t : Fin r) (i : HolorIndex [a]) := v (t, Sum.inl (entry i))
  let fb (t : Fin r) (j : HolorIndex [b]) := v (t, Sum.inr (.inl (entry j)))
  let fc (t : Fin r) (k : HolorIndex [c]) := v (t, Sum.inr (.inr (entry k)))
  have hv : (φ v : Holor ℂ [a,b,c]) = ∑ t, Holor.mul (fa t) (Holor.mul (fb t) (fc t)) := by
    funext q
    rw [eval_holor_sum]
    rfl
  rw [hv]
  exact Nat.find_min' _ (tensor_sum_rank fa fb fc)

end CriticalReduction

namespace CriticalTensor

def Spans (a b c r : ℕ) : Prop :=
  ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
    ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
      ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))

/-- A diagonal block with a regular coordinate part of length h and a base of length d. -/
def Border (a d h base extra : ℕ) : Prop :=
  ∃ X : Fin extra → Fin a → ℂ, ∃ Y Z : Fin extra → (Fin h ⊕ Fin d) → ℂ,
  ∃ x : Fin base → Fin a → ℂ, ∃ y z : Fin base → Fin d → ℂ,
    ∀ T : Fin a → (Fin h ⊕ Fin d) → (Fin h ⊕ Fin d) → ℂ,
    ∃ U : Fin extra → Fin a → ℂ, ∃ V W : Fin extra → (Fin h ⊕ Fin d) → ℂ,
    ∃ v w : Fin base → Fin h → ℂ, ∀ i j k, (j.isLeft=true ∨ k.isLeft=true) →
      T i j k =
        (∑ t, (U t i*(Y t j*Z t k) + X t i*(V t j*Z t k) + X t i*(Y t j*W t k))) +
        ∑ t, (x t i*(j.elim (v t) (fun _ => 0) * k.elim (fun _ => 0) (z t)) +
          x t i*(j.elim (fun _ => 0) (y t) * k.elim (w t) (fun _ => 0)))

/-- Two independent regular groups interact through one partial variation
of each point in the opposite group. -/
def Cross (a h extra : ℕ) : Prop :=
  ∃ x₁ x₂ : Fin extra → Fin a → ℂ, ∃ y z : Fin extra → Fin h → ℂ,
    ∀ T : Fin a → Fin h → Fin h → ℂ, ∃ v w : Fin extra → Fin h → ℂ, ∀ i j k,
      T i j k = ∑ t, (x₂ t i*(v t j*z t k) + x₁ t i*(y t j*w t k))

end CriticalTensor

namespace CriticalTensor

/-- A tangent witness on the two width-h borders of a rectangular d-by-e base. -/
def RectBorder (a d e h base extra : ℕ) : Prop :=
  ∃ X : Fin extra → Fin a → ℂ,
    ∃ Y : Fin extra → (Fin h ⊕ Fin d) → ℂ, ∃ Z : Fin extra → (Fin h ⊕ Fin e) → ℂ,
    ∃ x : Fin base → Fin a → ℂ, ∃ y : Fin base → Fin d → ℂ, ∃ z : Fin base → Fin e → ℂ,
    ∀ T : Fin a → (Fin h ⊕ Fin d) → (Fin h ⊕ Fin e) → ℂ,
    ∃ U : Fin extra → Fin a → ℂ, ∃ V : Fin extra → (Fin h ⊕ Fin d) → ℂ,
    ∃ W : Fin extra → (Fin h ⊕ Fin e) → ℂ, ∃ v w : Fin base → Fin h → ℂ,
      ∀ i j k, (j.isLeft=true ∨ k.isLeft=true) →
        T i j k =
          (∑ t, (U t i*(Y t j*Z t k) + X t i*(V t j*Z t k) + X t i*(Y t j*W t k))) +
          ∑ t, (x t i*(j.elim (v t) (fun _ => 0) * k.elim (fun _ => 0) (z t)) +
            x t i*(j.elim (fun _ => 0) (y t) * k.elim (w t) (fun _ => 0)))

end CriticalTensor

namespace CriticalTensor.RectGrowth

open MvPolynomial

/-- A single surjective specialization gives a polynomial whose nonvanishing
guarantees surjectivity. Its determinant uses a fixed right inverse at that point. -/
lemma surjectivity_polynomial {I J V : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (x₀ : V → ℂ)
    (h₀ : Function.Surjective (M.map (eval x₀)).mulVec) :
    ∃ Q : MvPolynomial V ℂ, Q ≠ 0 ∧ ∀ x : V → ℂ,
      eval x Q ≠ 0 → Function.Surjective (M.map (eval x)).mulVec := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h₀
  let D := M * B.map (C : ℂ →+* MvPolynomial V ℂ)
  have specialize (x : V → ℂ) : eval x D.det = (M.map (eval x) * B).det := by
    have hconst : (B.map (C : ℂ →+* MvPolynomial V ℂ)).map (eval x) = B := by
      ext i j
      simp [Matrix.map_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show D = _ from rfl, Matrix.map_mul, hconst]
  have hvalue : eval x₀ D.det = 1 := by rw [specialize, hB, Matrix.det_one]
  refine ⟨D.det, ?_, ?_⟩
  · intro he
    rw [he, map_zero] at hvalue
    exact zero_ne_one hvalue
  · intro x hx
    rw [specialize] at hx
    have hprod : Function.Surjective (M.map (eval x) * B).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
    intro y
    obtain ⟨z, hz⟩ := hprod y
    refine ⟨B.mulVec z, ?_⟩
    rw [Matrix.mulVec_mulVec]
    exact hz

lemma avoid_two {V : Type} {P Q : MvPolynomial V ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ eval x Q ≠ 0 := by
  by_contra! h
  apply (mul_ne_zero hP hQ)
  apply MvPolynomial.funext
  intro x
  rw [map_mul, map_zero]
  by_cases hx : eval x P = 0
  · exact mul_eq_zero.mpr (Or.inl hx)
  · exact mul_eq_zero.mpr (Or.inr (h x hx))

/-- Separate specializations can verify blocks depending on the same parameters:
the product of their certificate polynomials is nonzero over the complex numbers. -/
lemma simultaneous_surjectivity {K V : Type} [Fintype K] {I J : K → Type}
    [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)] [∀ k, Fintype (J k)]
    (M : ∀ k, Matrix (I k) (J k) (MvPolynomial V ℂ))
    (h : ∀ k, ∃ x : V → ℂ, Function.Surjective ((M k).map (eval x)).mulVec)
    (P : MvPolynomial V ℂ) (hP : P ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ ∀ k, Function.Surjective ((M k).map (eval x)).mulVec := by
  classical
  choose z hz using h
  choose Q hQ hgood using fun k => surjectivity_polynomial (M k) (z k) (hz k)
  have hprod : (∏ k, Q k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hQ k
  obtain ⟨x, hx, hrest⟩ := avoid_two hP hprod
  have hvals : (∏ k, eval x (Q k)) ≠ 0 := by simpa only [map_prod] using hrest
  exact ⟨x, hx, fun k => hgood k x (Finset.prod_ne_zero_iff.mp hvals k (Finset.mem_univ k))⟩

/-- A priority for each sector is enough. Distinct sectors at the same priority
are disjoint on their diagonal rows and columns. -/
lemma graded_surjective {R C S : Type} [Fintype R] [Fintype C] [Fintype S] [DecidableEq S]
    (f : R → S) (g : C → S) (priority : S → Fin 3) (A : Matrix R C ℂ)
    (zero_above : ∀ i j, f i ≠ g j → priority (f i) ≤ priority (g j) → A i j=0)
    (local_maps : ∀ s : S, Function.Surjective
      (A.submatrix (fun i : {i // f i=s} => i.val) (fun j : {j // g j=s} => j.val)).mulVec) :
    Function.Surjective A.mulVec := by
  classical
  have hpre (j : R) : ∃ v : {k // g k=f j} → ℂ, ∀ i : {i // f i=f j},
      (∑ k, A i.val k.val * v k) = if i.val=j then 1 else 0 := by
    obtain ⟨v,hv⟩ := local_maps (f j) fun i => if i.val=j then 1 else 0
    exact ⟨v,fun i => congrFun hv i⟩
  choose v hv using hpre
  let B : Matrix C R ℂ := fun k j => if h : g k=f j then v j ⟨k,h⟩ else 0
  let L := A*B
  have entries (i j : R) : L i j = ∑ k : {k // g k=f j}, A i k.val*v j k := by
    change (∑ k : C, A i k*(if h : g k=f j then v j ⟨k,h⟩ else 0)) = _
    let F (k : C) := A i k * (if h : g k=f j then v j ⟨k,h⟩ else 0)
    have e := (Equiv.sumCompl (fun k : C => g k=f j)).sum_comp F
    rw [Fintype.sum_sum_type] at e
    have hp (q : {k // g k=f j}) : g q.val=f j := q.property
    have hn (q : {k // g k≠f j}) : g q.val≠f j := q.property
    simpa [F,hp,hn] using e.symm
  have off (i j : R) (h : f i ≠ f j) (hle : priority (f i) ≤ priority (f j)) : L i j=0 := by
    rw [entries]
    apply Finset.sum_eq_zero
    intro k _
    rw [zero_above i k.val (by simpa only [k.property] using h)
      (by simpa only [k.property] using hle),zero_mul]
  have triangular : L.BlockTriangular (fun i => OrderDual.toDual (priority (f i))) := by
    intro i j h
    change priority (f i) < priority (f j) at h
    exact off i j (fun he => (ne_of_lt h) (congrArg priority he)) (le_of_lt h)
  have diag (s : (Fin 3)ᵒᵈ) : L.toSquareBlock (fun i => OrderDual.toDual (priority (f i))) s = 1 := by
    ext i j
    obtain ⟨i,hi⟩ := i
    obtain ⟨j,hj⟩ := j
    have hlev : priority (f i)=priority (f j) := hi.trans hj.symm
    change L i j = _
    by_cases hij : f i=f j
    · rw [entries,hv j ⟨i,hij⟩,Matrix.one_apply]
      simp only [Subtype.mk.injEq]
    · rw [off i j hij (le_of_eq hlev),Matrix.one_apply]
      simp [show i ≠ j from fun h => hij (congrArg f h)]
  have detL : L.det=1 := by rw [triangular.det_fintype]; simp [diag]
  have hL : Function.Surjective L.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (by rw [detL]; exact isUnit_one))
  intro y
  obtain ⟨z,hz⟩ := hL y
  refine ⟨B.mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec]
  exact hz

/-- Transfer the row equations of a finite template to a global sector. Every
row needed by the sector has a local representative. Coincident selected
columns can be combined by summing their coefficients. -/
lemma cover_matrix {R C I J : Type} [Fintype C] [DecidableEq C] [Fintype J]
    (A : Matrix R C ℂ) (L : Matrix I J ℂ) (rmap : I → R) (cmap : J → C)
    (hR : Function.Surjective rmap) (hM : ∀ i j, A (rmap i) (cmap j)=L i j)
    (hs : Function.Surjective L.mulVec) : Function.Surjective A.mulVec := by
  classical
  let E : Matrix C J ℂ := fun k j => if k=cmap j then 1 else 0
  have hcols (i j) : (A*E) (rmap i) j=L i j := by
    rw [Matrix.mul_apply]
    simpa [E,mul_ite,Finset.sum_ite_eq'] using hM i j
  intro y
  obtain ⟨z,hz⟩ := hs (fun i => y (rmap i))
  refine ⟨E.mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec]
  funext r
  obtain ⟨i,rfl⟩ := hR r
  change (∑ j, (A*E) (rmap i) j*z j) = _
  simpa only [hcols,Matrix.mulVec,dotProduct] using congrFun hz i

end CriticalTensor.RectGrowth

namespace CriticalTensor.RectGrowth

open MvPolynomial

structure Dimensions where
  a : ℕ
  d : ℕ
  e : ℕ
  h : ℕ
  base : ℕ
  extra : ℕ

variable (p : Dimensions)

abbrev Pt (G : Type) := Fin p.base ⊕ (G × Fin p.extra)
abbrev Axis (n : ℕ) (G : Type) := Fin n ⊕ (G × Fin p.h)
abbrev LocalAxis (n : ℕ) := Fin p.h ⊕ Fin n
abbrev Dir (I J : Type) := Fin p.a ⊕ (I ⊕ J)
abbrev V (G : Type) := (Fin p.base × Dir p (Fin p.d) (Fin p.e)) ⊕ (G × Fin p.extra × Dir p (LocalAxis p p.d) (LocalAxis p p.e))
abbrev RR (G : Type) := Fin p.a × Axis p p.d G × Axis p p.e G
abbrev CC (G : Type) := Pt p G × Dir p (Axis p p.d G) (Axis p p.e G)
abbrev Pair (G : Type) := {z : G × G // z.1 ≠ z.2}
abbrev Sector (G : Type) := Unit ⊕ (G ⊕ Pair G)
abbrev Arm := (Fin p.h × Fin p.e) ⊕ ((Fin p.d × Fin p.h) ⊕ (Fin p.h × Fin p.h))

def arms : Arm p → LocalAxis p p.d × LocalAxis p p.e
  | .inl (j,k) => (.inl j,.inr k)
  | .inr (.inl (j,k)) => (.inr j,.inl k)
  | .inr (.inr (j,k)) => (.inl j,.inl k)

def loc {G : Type} {n : ℕ} (g : G) : LocalAxis p n → Axis p n G
  | .inl u => .inr (g,u)
  | .inr j => .inl j

def Row {G : Type} : Sector G → Type
  | .inl _ => Fin p.a × Fin p.d × Fin p.e
  | .inr (.inl _) => Fin p.a × Arm p
  | .inr (.inr _) => Fin p.a × Fin p.h × Fin p.h

def Col {G : Type} : Sector G → Type
  | .inl _ => Fin p.base × Dir p (Fin p.d) (Fin p.e)
  | .inr (.inl _) => (Fin p.extra × Dir p (LocalAxis p p.d) (LocalAxis p p.e)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h))
  | .inr (.inr _) => Fin p.extra × (Fin p.h ⊕ Fin p.h)

instance {G : Type} (s : Sector G) : Fintype (Row p s) := by rcases s with u|g|z <;> dsimp [Row] <;> infer_instance
instance {G : Type} (s : Sector G) : DecidableEq (Row p s) := by rcases s with u|g|z <;> dsimp [Row] <;> infer_instance
instance {G : Type} (s : Sector G) : Fintype (Col p s) := by rcases s with u|g|z <;> dsimp [Col] <;> infer_instance
instance {G : Type} (s : Sector G) : DecidableEq (Col p s) := by rcases s with u|g|z <;> dsimp [Col] <;> infer_instance

def row {G : Type} : (s : Sector G) → Row p s → RR p G
  | .inl _,(i,j,k) => (i,.inl j,.inl k)
  | .inr (.inl g),(i,z) => (i,loc p g (arms p z).1,loc p g (arms p z).2)
  | .inr (.inr q),(i,j,k) => (i,.inr (q.val.1,j),.inr (q.val.2,k))

def col {G : Type} : (s : Sector G) → Col p s → CC p G
  | .inl _,(t,h) => (.inl t,h.map id (Sum.map Sum.inl Sum.inl))
  | .inr (.inl g),.inl (t,h) => (.inr (g,t),h.map id (Sum.map (loc p g) (loc p g)))
  | .inr (.inl g),.inr (t,.inl h) => (.inl t,.inr (.inl (.inr (g,h))))
  | .inr (.inl g),.inr (t,.inr h) => (.inl t,.inr (.inr (.inr (g,h))))
  | .inr (.inr q),(t,.inl h) => (.inr (q.val.2,t),.inr (.inl (.inr (q.val.1,h))))
  | .inr (.inr q),(t,.inr h) => (.inr (q.val.1,t),.inr (.inr (.inr (q.val.2,h))))

def lev {G : Type} : Sector G → Fin 3
  | .inl _ => 2
  | .inr (.inl _) => 1
  | .inr (.inr _) => 0

section
variable {G K : Type} [DecidableEq G] [CommSemiring K]

def A (x : V p G → K) : Pt p G → Fin p.a → K
  | .inl t,i => x (.inl (t,.inl i))
  | .inr (g,t),i => x (.inr (g,t,.inl i))

def tail {n : ℕ} (b : Fin p.base → Fin n → K) (B : G → Fin p.extra → LocalAxis p n → K) : Pt p G → Axis p n G → K
  | .inl t,.inl j => b t j
  | .inl _,.inr _ => 0
  | .inr (g,t),.inl j => B g t (.inr j)
  | .inr (g,t),.inr (h,i) => if h=g then B g t (.inl i) else 0

def B (x : V p G → K) := tail p (n:=p.d) (fun t j => x (.inl (t,.inr (.inl j)))) (fun g t j => x (.inr (g,t,.inr (.inl j))))
def Cc (x : V p G → K) := tail p (n:=p.e) (fun t k => x (.inl (t,.inr (.inr k)))) (fun g t k => x (.inr (g,t,.inr (.inr k))))

def tangent (x : V p G → K) (r : RR p G) : CC p G → K
  | (t,.inl h) => if h=r.1 then B p x t r.2.1 * Cc p x t r.2.2 else 0
  | (t,.inr (.inl h)) => if h=r.2.1 then A p x t r.1 * Cc p x t r.2.2 else 0
  | (t,.inr (.inr h)) => if h=r.2.2 then A p x t r.1 * B p x t r.2.1 else 0

def full (x : V p G → K) : Matrix (Σ s : Sector G, Row p s) (Σ s : Sector G, Col p s) K :=
  fun r c => tangent p x (row p r.1 r.2) (col p c.1 c.2)

def block (x : V p G → K) (s : Sector G) : Matrix (Row p s) (Col p s) K :=
  fun r c => tangent p x (row p s r) (col p s c)

lemma tail_loc {n : ℕ} (b : Fin p.base → Fin n → K) (H : G → Fin p.extra → LocalAxis p n → K)
    (g : G) (t : Fin p.extra) (j : LocalAxis p n) : tail p b H (.inr (g,t)) (loc p g j) = H g t j := by
  cases j <;> simp [tail,loc]

omit [DecidableEq G] in
lemma loc_eq {n : ℕ} (g : G) (j k : LocalAxis p n) : loc p g j=loc p g k ↔ j=k := by cases j <;> cases k <;> simp [loc]

private lemma tail_map {L : Type} [CommSemiring L] {n : ℕ} (φ : K →+* L) (b : Fin p.base → Fin n → K)
    (H : G → Fin p.extra → LocalAxis p n → K) (t : Pt p G) (j : Axis p n G) :
    φ (tail p b H t j) = tail p (fun t j => φ (b t j)) (fun g t j => φ (H g t j)) t j := by
  rcases t with t|⟨g,t⟩ <;> rcases j with j|⟨h,j⟩ <;> simp only [tail,map_zero]
  by_cases he : h=g <;> simp [he]

lemma block_eval (x : V p G → ℂ) (s : Sector G) :
    (block p (MvPolynomial.X : V p G → MvPolynomial (V p G) ℂ) s).map (eval x) = block p x s := by
  ext r j
  change eval x (tangent p MvPolynomial.X (row p s r) (col p s j)) = tangent p x (row p s r) (col p s j)
  generalize hc : col p s j = z
  rcases z with ⟨t,h|h|h⟩ <;> rcases t with t|⟨g,t⟩ <;>
    simp only [tangent,A,B,Cc,apply_ite,tail_map,map_mul,map_zero,eval_X]
  all_goals split <;> simp_all

end

lemma row_surj {G : Type} [DecidableEq G] : Function.Surjective (fun z : Σ s : Sector G, Row p s => row p z.1 z.2) := by
  rintro ⟨i,j|⟨g,j⟩,k|⟨l,k⟩⟩
  · exact ⟨⟨.inl (),i,j,k⟩,rfl⟩
  · exact ⟨⟨.inr (.inl l),i,.inr (.inl (j,k))⟩,rfl⟩
  · exact ⟨⟨.inr (.inl g),i,.inl (j,k)⟩,rfl⟩
  · by_cases h : g=l
    · subst l
      exact ⟨⟨.inr (.inl g),i,.inr (.inr (j,k))⟩,rfl⟩
    · exact ⟨⟨.inr (.inr ⟨(g,l),h⟩),i,j,k⟩,rfl⟩

end CriticalTensor.RectGrowth

namespace CriticalTensor.RectGrowth

variable (p : Dimensions) {G : Type} [DecidableEq G]

def param (a : Fin p.base → Fin p.a → ℂ) (b : Fin p.base → Fin p.d → ℂ) (c : Fin p.base → Fin p.e → ℂ)
    (A : G → Fin p.extra → Fin p.a → ℂ) (B : G → Fin p.extra → LocalAxis p p.d → ℂ)
    (C : G → Fin p.extra → LocalAxis p p.e → ℂ) : V p G → ℂ
  | .inl (t,.inl i) => a t i
  | .inl (t,.inr (.inl j)) => b t j
  | .inl (t,.inr (.inr k)) => c t k
  | .inr (g,t,.inl i) => A g t i
  | .inr (g,t,.inr (.inl j)) => B g t j
  | .inr (g,t,.inr (.inr k)) => C g t k

lemma base_rank (hb : Spans p.a p.d p.e p.base) :
    ∃ x : V p G → ℂ, Function.Surjective (block p x (.inl ())).mulVec := by
  classical
  obtain ⟨a,b,c,hb⟩ := hb
  let x : V p G → ℂ := param p a b c 0 0 0
  refine ⟨x,?_⟩
  intro y
  obtain ⟨u,v,w,hu⟩ := hb fun i j k => y (i,j,k)
  let z : Fin p.base × Dir p (Fin p.d) (Fin p.e) → ℂ := fun (t,h) => h.elim (u t) (Sum.elim (v t) (w t))
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,j,k⟩ := r
  change (∑ s : Fin p.base × Dir p (Fin p.d) (Fin p.e), tangent p x (i,.inl j,.inl k) (col p (.inl ()) s) * z s) = y (i,j,k)
  rw [hu,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [tangent,col,x,param,A,B,Cc,tail,z,ite_mul,Finset.sum_ite_eq']
  ring

def target (y : Fin p.a × Arm p → ℂ) (i : Fin p.a) : LocalAxis p p.d → LocalAxis p p.e → ℂ
  | .inl j,.inl k => y (i,.inr (.inr (j,k)))
  | .inl j,.inr k => y (i,.inl (j,k))
  | .inr j,.inl k => y (i,.inr (.inl (j,k)))
  | .inr _,.inr _ => 0

lemma target_arms (y : Fin p.a × Arm p → ℂ) (i : Fin p.a) (r : Arm p) :
    target p y i (arms p r).1 (arms p r).2=y (i,r) := by
  rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;> rfl

lemma arms_hit (r : Arm p) : (arms p r).1.isLeft=true ∨ (arms p r).2.isLeft=true := by
  rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;> simp [arms]

lemma border_rank (g : G) (hr : RectBorder p.a p.d p.e p.h p.base p.extra) :
    ∃ x : V p G → ℂ, Function.Surjective (block p x (.inr (.inl g))).mulVec := by
  classical
  obtain ⟨aa,bb,cc,a,b,c,hr⟩ := hr
  let x : V p G → ℂ := param p a b c (fun _ => aa) (fun _ => bb) (fun _ => cc)
  refine ⟨x,?_⟩
  intro y
  obtain ⟨u,v,w,vb,wb,hu⟩ := hr (target p y)
  let z : (Fin p.extra × Dir p (LocalAxis p p.d) (LocalAxis p p.e)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h)) → ℂ
    | .inl (t,h) => h.elim (u t) (Sum.elim (v t) (w t))
    | .inr (t,h) => h.elim (vb t) (wb t)
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,r⟩ := r
  change (∑ s : (Fin p.extra × Dir p (LocalAxis p p.d) (LocalAxis p p.e)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h)),
    tangent p x (i,loc p g (arms p r).1,loc p g (arms p r).2) (col p (.inr (.inl g)) s) * z s) = y (i,r)
  rw [← target_arms p y i r,hu i _ _ (arms_hit p r),Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp [tangent,col,x,param,A,B,Cc,z,tail_loc,loc_eq,ite_mul,Finset.sum_ite_eq']
    ring
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type]
    rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;>
      simp [tangent,col,x,param,A,B,Cc,tail,z,arms,loc,ite_mul,Finset.sum_ite_eq'] <;> ring

lemma cross_rank (q : Pair G) (hc : Cross p.a p.h p.extra) :
    ∃ x : V p G → ℂ, Function.Surjective (block p x (.inr (.inr q))).mulVec := by
  classical
  obtain ⟨x₁,x₂,b,c,hc⟩ := hc
  let x : V p G → ℂ := param p 0 0 0 (fun g => if g=q.val.1 then x₁ else x₂)
    (fun _ t => Sum.elim (b t) 0) (fun _ t => Sum.elim (c t) 0)
  refine ⟨x,?_⟩
  intro y
  obtain ⟨v,w,hw⟩ := hc fun i j k => y (i,j,k)
  let z : Fin p.extra × (Fin p.h ⊕ Fin p.h) → ℂ := fun (t,h) => h.elim (v t) (w t)
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,j,k⟩ := r
  change (∑ s : Fin p.extra × (Fin p.h ⊕ Fin p.h),
    tangent p x (i,.inr (q.val.1,j),.inr (q.val.2,k)) (col p (.inr (.inr q)) s)*z s)=y (i,j,k)
  rw [hw,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type]
  simp [tangent,col,x,param,A,B,Cc,tail,z,ite_mul,Finset.sum_ite_eq',q.property.symm]
  ring

end CriticalTensor.RectGrowth

namespace CriticalTensor.RectGrowth

variable (p : Dimensions) {G : Type} [DecidableEq G] (x : V p G → ℂ)

private lemma arm_base (g : G) (r : Row p (.inr (.inl g))) (z : Col p (G:=G) (.inl ())) :
    tangent p x (row p (.inr (.inl g)) r) (col p (.inl ()) z)=0 := by
  rcases r with ⟨i,⟨j,k⟩|⟨j,k⟩|⟨j,k⟩⟩ <;> rcases z with ⟨t,h|h|h⟩ <;>
    simp [row,col,tangent,arms,loc,B,Cc,tail]

private lemma arm_other (g h : G) (gh : g ≠ h) (r : Row p (.inr (.inl g))) (z : Col p (.inr (.inl h))) :
    tangent p x (row p (.inr (.inl g)) r) (col p (.inr (.inl h)) z)=0 := by
  rcases r with ⟨i,⟨j,k⟩|⟨j,k⟩|⟨j,k⟩⟩ <;> rcases z with ⟨t,u|(u|u)|(u|u)⟩|⟨t,u|u⟩ <;>
    simp [row,col,tangent,arms,loc,B,Cc,tail,gh,gh.symm]

private lemma pair_base (q : Pair G) (r : Row p (.inr (.inr q))) (z : Col p (G:=G) (.inl ())) :
    tangent p x (row p (.inr (.inr q)) r) (col p (.inl ()) z)=0 := by
  rcases r with ⟨i,j,k⟩
  rcases z with ⟨t,h|h|h⟩ <;> simp [row,col,tangent,B,Cc,tail]

private lemma pair_arm (q : Pair G) (h : G) (r : Row p (.inr (.inr q))) (z : Col p (.inr (.inl h))) :
    tangent p x (row p (.inr (.inr q)) r) (col p (.inr (.inl h)) z)=0 := by
  rcases q with ⟨⟨g,l⟩,hg⟩
  change g≠l at hg
  rcases r with ⟨i,j,k⟩
  rcases z with ⟨t,u|(u|u)|(u|u)⟩|⟨t,u|u⟩ <;>
    by_cases he : g=h <;> by_cases hf : l=h <;>
    simp_all [row,col,tangent,loc,B,Cc,tail]
  all_goals grind

private lemma pair_other (q q' : Pair G) (hpq : q≠q') (r : Row p (.inr (.inr q))) (z : Col p (.inr (.inr q'))) :
    tangent p x (row p (.inr (.inr q)) r) (col p (.inr (.inr q')) z)=0 := by
  rcases q with ⟨⟨a,b⟩,hab⟩
  rcases q' with ⟨⟨c,d⟩,hcd⟩
  have h : a=c → b≠d := by rintro rfl rfl; exact (hpq rfl).elim
  rcases r with ⟨i,j,k⟩
  rcases z with ⟨t,v|v⟩ <;> by_cases hac : a=c <;> by_cases hbd : b=d <;>
    simp_all [row,col,tangent,B,Cc,tail,eq_comm]

lemma off (s t : Sector G) (h : s≠t) (hl : lev s≤lev t) (r : Row p s) (z : Col p t) :
    tangent p x (row p s r) (col p t z)=0 := by
  rcases s with ⟨⟩|g|q <;> rcases t with ⟨⟩|h'|q'
  · exact (h rfl).elim
  · exact (by decide : ¬((2:Fin 3)≤1)) hl |>.elim
  · exact (by decide : ¬((2:Fin 3)≤0)) hl |>.elim
  · exact arm_base p x g r z
  · exact arm_other p x g h' (fun e => h (e ▸ rfl)) r z
  · exact (by decide : ¬((1:Fin 3)≤0)) hl |>.elim
  · exact pair_base p x q r z
  · exact pair_arm p x q h' r z
  · exact pair_other p x q q' (fun e => h (e ▸ rfl)) r z

end CriticalTensor.RectGrowth

namespace CriticalTensor.RectGrowth

open MvPolynomial

variable (p : Dimensions) {G : Type} [Fintype G] [DecidableEq G]

def actual (x : V p G → ℂ) : Matrix (RR p G) (CC p G) ℂ := tangent p x

lemma common (hb : Spans p.a p.d p.e p.base) (hr : RectBorder p.a p.d p.e p.h p.base p.extra)
    (hc : Cross p.a p.h p.extra) : ∃ x : V p G → ℂ, Function.Surjective (actual p x).mulVec := by
  classical
  have each (s : Sector G) : ∃ x : V p G → ℂ, Function.Surjective (block p x s).mulVec := by
    rcases s with ⟨⟩|g|q
    · exact base_rank p hb
    · exact border_rank p g hr
    · exact cross_rank p q hc
  let M (s : Sector G) := block p (MvPolynomial.X : V p G → MvPolynomial (V p G) ℂ) s
  have openSet (s : Sector G) : ∃ x : V p G → ℂ, Function.Surjective ((M s).map (eval x)).mulVec := by
    obtain ⟨x,h⟩ := each s
    exact ⟨x,by simpa only [M,block_eval] using h⟩
  obtain ⟨x,_,hx⟩ := simultaneous_surjectivity M openSet 1 one_ne_zero
  have hs (s : Sector G) : Function.Surjective (block p x s).mulVec := by simpa only [M,block_eval] using hx s
  have hfull : Function.Surjective (full p x).mulVec := by
    apply graded_surjective (fun r => r.1) (fun j => j.1) lev (full p x)
    · rintro ⟨s,i⟩ ⟨t,j⟩ h ht
      exact off p x s t h ht i j
    · intro s
      apply cover_matrix _ (block p x s) (fun i => ⟨⟨s,i⟩,rfl⟩) (fun j => ⟨⟨s,j⟩,rfl⟩)
      · rintro ⟨⟨t,i⟩,ht⟩
        change t=s at ht
        subst t
        exact ⟨i,rfl⟩
      · intro i j; rfl
      · exact hs s
  exact ⟨x,cover_matrix (actual p x) (full p x) (fun r => row p r.1 r.2) (fun j => col p j.1 j.2)
    (row_surj p) (fun _ _ => rfl) hfull⟩

lemma action (x : V p G → ℂ) (z : CC p G → ℂ) (i : Fin p.a) (j : Axis p p.d G) (k : Axis p p.e G) :
    (actual p x).mulVec z (i,j,k) = ∑ t : Pt p G,
      (z (t,.inl i)*(B p x t j*Cc p x t k) + A p x t i*(z (t,.inr (.inl j))*Cc p x t k) +
      A p x t i*(B p x t j*z (t,.inr (.inr k)))) := by
  classical
  change (∑ w : CC p G, tangent p x (i,j,k) w*z w)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [tangent,ite_mul,Finset.sum_ite_eq']
  ring

end CriticalTensor.RectGrowth

namespace CriticalTensor

open RectGrowth

/-- A base block, its border with one regular block, and an ordered pair of regular
blocks suffice to extend both axes by the same number of regular blocks. -/
lemma grow_rect (a d e h base extra t : ℕ) (hb : Spans a d e base)
    (hr : RectBorder a d e h base extra) (hc : Cross a h extra) :
    Spans a (d+h*t) (e+h*t) (base+extra*t) := by
  classical
  let p : Dimensions := ⟨a,d,e,h,base,extra⟩
  let G := Fin t
  let left : Fin (d+h*t) ≃ Axis p p.d G := Fintype.equivOfCardEq (by simp [G,p,Axis,Nat.mul_comm])
  let right : Fin (e+h*t) ≃ Axis p p.e G := Fintype.equivOfCardEq (by simp [G,p,Axis,Nat.mul_comm])
  let f : Fin (base+extra*t) ≃ Pt p G := Fintype.equivOfCardEq (by simp [G,p,Pt,Nat.mul_comm])
  obtain ⟨x,hx⟩ := common p (G:=G) hb hr hc
  refine ⟨fun t i => A p x (f t) i,fun t j => B p x (f t) (left j),fun t k => Cc p x (f t) (right k),?_⟩
  intro T
  obtain ⟨z,hz⟩ := hx fun r => T r.1 (left.symm r.2.1) (right.symm r.2.2)
  refine ⟨fun t i => z (f t,.inl i),fun t j => z (f t,.inr (.inl (left j))),
    fun t k => z (f t,.inr (.inr (right k))),?_⟩
  intro i j k
  have hw := (congrFun hz (i,left j,right k)).symm
  simp only [Equiv.symm_apply_apply] at hw
  rw [action] at hw
  exact hw.trans (f.sum_comp (fun t => z (t,Sum.inl i)*(B p x t (left j)*Cc p x t (right k)) +
    A p x t i*(z (t,Sum.inr (Sum.inl (left j)))*Cc p x t (right k)) +
    A p x t i*(B p x t (left j)*z (t,Sum.inr (Sum.inr (right k)))))).symm

end CriticalTensor

namespace CriticalTensor

/-- Independent crossed blocks on complementary first-axis subspaces may be combined. -/
lemma cross_add {a b h n m : ℕ} (hl : Cross a h n) (hr : Cross b h m) : Cross (a+b) h (n+m) := by
  classical
  obtain ⟨xl,ul,yl,zl,hl⟩ := hl
  obtain ⟨xr,ur,yr,zr,hr⟩ := hr
  let e : Fin a ⊕ Fin b ≃ Fin (a+b) := finSumFinEquiv
  let p : Fin n ⊕ Fin m ≃ Fin (n+m) := finSumFinEquiv
  let first (f : Fin n → Fin a → ℂ) (g : Fin m → Fin b → ℂ) (t : Fin (n+m)) (i : Fin (a+b)) : ℂ :=
    (p.symm t).elim (fun s => (e.symm i).elim (f s) 0) (fun s => (e.symm i).elim 0 (g s))
  let second (f : Fin n → Fin h → ℂ) (g : Fin m → Fin h → ℂ) (t : Fin (n+m)) := (p.symm t).elim f g
  refine ⟨first xl xr,first ul ur,second yl yr,second zl zr,?_⟩
  intro T
  obtain ⟨v₁,w₁,h₁⟩ := hl (fun i => T (e (.inl i)))
  obtain ⟨v₂,w₂,h₂⟩ := hr (fun i => T (e (.inr i)))
  refine ⟨second v₁ v₂,second w₁ w₂,?_⟩
  intro i j k
  obtain ⟨s,rfl⟩ := e.surjective i
  let term (t : Fin (n+m)) := first ul ur t (e s)*(second v₁ v₂ t j*second zl zr t k) +
    first xl xr t (e s)*(second yl yr t j*second w₁ w₂ t k)
  change T (e s) j k = ∑ t,term t
  rw [← p.sum_comp term,Fintype.sum_sum_type]
  cases s with
  | inl i => simpa [term,first,second] using h₁ i j k
  | inr i => simpa [term,first,second] using h₂ i j k

private lemma cross_small_two : Cross 2 2 2 := by
  let q (t j : Fin 2) : ℂ := if t=j then 1 else 0
  refine ⟨fun _ i => if i=0 then 1 else 0,fun _ i => if i=1 then 1 else 0,q,q,?_⟩
  intro T
  refine ⟨fun t j => T 1 j t,fun t k => T 0 t k,?_⟩
  intro i j k
  fin_cases i <;> simp [q,ite_mul,mul_ite,Finset.sum_ite_eq']

/-- The two crossed groups on three first coordinates give a unimodular twelve-by-twelve matrix. -/
private lemma cross_small_three : Cross 3 2 3 := by
  let x₁ : Fin 3 → Fin 3 → ℂ := ![![1,0,0],![0,1,0],![0,0,1]]
  let x₂ : Fin 3 → Fin 3 → ℂ := ![![1,0,1],![0,1,1],![1,1,1]]
  let b : Fin 3 → Fin 2 → ℂ := ![![1,0],![0,1],![1,1]]
  refine ⟨x₁,x₂,b,b,?_⟩
  intro T
  let v : Fin 3 → Fin 2 → ℂ := ![
    ![T 0 1 0 - T 1 0 0 + T 2 0 0 - T 2 1 0, T 0 1 0 - T 0 1 1],
    ![-T 1 0 0 + T 1 0 1, -T 0 1 1 + T 1 0 1 - T 2 0 1 + T 2 1 1],
    ![T 1 0 0, T 0 1 1]]
  let w : Fin 3 → Fin 2 → ℂ := ![
    ![T 0 0 0 - T 0 1 0 - T 2 0 0 + T 2 1 0, T 0 0 1 - T 1 0 0],
    ![-T 0 1 1 + T 1 1 0, -T 1 0 1 + T 1 1 1 + T 2 0 1 - T 2 1 1],
    ![-T 0 1 0 + T 2 1 0, -T 1 0 1 + T 2 0 1]]
  refine ⟨v,w,?_⟩
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [Fin.sum_univ_three,Matrix.cons_val_two,x₁,x₂,b,v,w] <;> ring_nf <;> rfl

/-- At width two, two groups with one point per first coordinate span all crossed rows. -/
lemma cross_width_two (a : ℕ) (ha : 2 ≤ a) : Cross a 2 a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases h₂ : a=2
    · simpa [h₂] using cross_small_two
    by_cases h₃ : a=3
    · simpa [h₃] using cross_small_three
    have hsmall : Cross (a-2) 2 (a-2) := ih (a-2) (by omega) (by omega)
    simpa only [show a-2+2=a by omega] using cross_add hsmall cross_small_two

end CriticalTensor

namespace CriticalTensor.ConsecutiveBorder.Binary

def intBit (b : Bool) : ℤ := if b then 1 else 0
def fieldBit (b : Bool) : ZMod 2 := if b then 1 else 0

lemma cast_intBit (b : Bool) : ((intBit b : ℤ) : ZMod 2) = fieldBit b := by cases b <;> rfl

lemma fieldBit_xor (a b : Bool) : fieldBit (a ^^ b) = fieldBit a + fieldBit b := by
  cases a <;> cases b <;> decide

/-- XOR of the columns whose index occurs in the mask. -/
def xorColumns (cols : ℕ → ℕ) (mask : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => xorColumns cols mask m ^^^ (if mask.testBit m then cols m else 0)

lemma xorColumns_entry (cols : ℕ → ℕ) (mask row m : ℕ) :
    fieldBit ((xorColumns cols mask m).testBit row) =
      ∑ j ∈ Finset.range m, fieldBit ((cols j).testBit row) * fieldBit (mask.testBit j) := by
  induction m with
  | zero => simp [xorColumns, fieldBit]
  | succ m ih =>
    rw [xorColumns, Nat.testBit_xor, fieldBit_xor, ih, Finset.sum_range_succ]
    cases mask.testBit m <;> simp [fieldBit]

lemma complex_surjectivity {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (B : Matrix κ ι ℤ)
    (hab : A.map (Int.castRingHom (ZMod 2)) * B.map (Int.castRingHom (ZMod 2)) = 1) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let C := A * B
  have h2 : ((C.det : ℤ) : ZMod 2) = 1 := by
    change (Int.castRingHom (ZMod 2)) C.det = 1
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show C = A * B from rfl, Matrix.map_mul, hab,
      Matrix.det_one]
  have hne : C.det ≠ 0 := by
    intro he
    rw [he, Int.cast_zero] at h2
    exact zero_ne_one h2
  have hu : IsUnit (C.map (Int.castRingHom ℂ)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    change (C.det : ℂ) ≠ 0
    exact_mod_cast hne
  have hsurj : Function.Surjective (C.map (Int.castRingHom ℂ)).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨(B.map (Int.castRingHom ℂ)).mulVec x, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul]
  exact hx

lemma surjective_of_certificate {d m : ℕ} (A : Matrix (Fin d) (Fin m) ℤ) (cols masks : ℕ → ℕ)
    (hcols : ∀ i j, A i j = intBit ((cols j.val).testBit i.val))
    (hcheck : ∀ i : Fin d, xorColumns cols (masks i.val) m = 2 ^ i.val) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let B : Matrix (Fin m) (Fin d) ℤ := fun j i => intBit ((masks i.val).testBit j.val)
  apply complex_surjectivity A B
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  calc
    _ = ∑ k : Fin m, fieldBit ((cols k.val).testBit i.val) * fieldBit ((masks j.val).testBit k.val) := by
      apply Finset.sum_congr rfl
      intro k _
      change ((A i k : ℤ) : ZMod 2) * ((intBit ((masks j.val).testBit k.val) : ℤ) : ZMod 2) = _
      rw [hcols, cast_intBit, cast_intBit]
    _ = ∑ k ∈ Finset.range m, fieldBit ((cols k).testBit i.val) * fieldBit ((masks j.val).testBit k) := by
      exact Fin.sum_univ_eq_sum_range (fun k => fieldBit ((cols k).testBit i.val) *
        fieldBit ((masks j.val).testBit k)) m
    _ = fieldBit ((xorColumns cols (masks j.val) m).testBit i.val) := (xorColumns_entry _ _ _ _).symm
    _ = _ := by
      rw [hcheck j, Nat.testBit_two_pow]
      by_cases h : i = j
      · subst j; simp [fieldBit]
      · have hji : j.val ≠ i.val := fun hv => h (Fin.ext hv.symm)
        simp [h, hji, fieldBit]

end CriticalTensor.ConsecutiveBorder.Binary

namespace CriticalTensor.ConsecutiveBorder

abbrev Side (d : ℕ) := Fin 2 ⊕ Fin d
abbrev Rows (a d e : ℕ) := (Fin 2 × Side e × Fin a) ⊕ (Fin d × Fin 2 × Fin a)
abbrev Cols (a d e r : ℕ) := (Fin a × (Side d ⊕ (Side e ⊕ Fin a))) ⊕ (Fin r × (Fin 2 ⊕ Fin 2))

def coords {a d e : ℕ} : Rows a d e → Side d × Side e × Fin a
  | .inl (j,k,i) => (.inl j,k,i)
  | .inr (j,k,i) => (.inr j,.inl k,i)

def matrix {a d e r : ℕ} {K : Type} [CommSemiring K]
    (X : Fin a → Fin a → K) (Y : Fin a → Side d → K) (Z : Fin a → Side e → K)
    (x : Fin r → Fin a → K) (y : Fin r → Fin d → K) (z : Fin r → Fin e → K) :
    Matrix (Rows a d e) (Cols a d e r) K := fun row col =>
  let (j,k,i) := coords row
  match col with
  | .inl (t,.inl h) => if h=j then X t i * Z t k else 0
  | .inl (t,.inr (.inl h)) => if h=k then X t i * Y t j else 0
  | .inl (t,.inr (.inr h)) => if h=i then Y t j * Z t k else 0
  | .inr (t,.inl h) => if Sum.inl h=j then x t i * k.elim (fun _ => 0) (z t) else 0
  | .inr (t,.inr h) => if Sum.inl h=k then x t i * j.elim (fun _ => 0) (y t) else 0

lemma cast_matrix {a d e r : ℕ} (X : Fin a → Fin a → ℤ) (Y : Fin a → Side d → ℤ)
    (Z : Fin a → Side e → ℤ) (x : Fin r → Fin a → ℤ) (y : Fin r → Fin d → ℤ) (z : Fin r → Fin e → ℤ) :
    (matrix X Y Z x y z).map (Int.castRingHom ℂ) = matrix (fun t i => (X t i : ℂ)) (fun t j => (Y t j : ℂ))
      (fun t k => (Z t k : ℂ)) (fun t i => (x t i : ℂ)) (fun t j => (y t j : ℂ)) (fun t k => (z t k : ℂ)) := by
  have ec (P : Prop) [Decidable P] (v : ℤ) (w : ℂ) (hv : (v : ℂ)=w) :
      ((if P then v else 0 : ℤ) : ℂ) = (if P then w else 0) := by by_cases hp : P <;> simp [hp,hv]
  ext row col
  change ((matrix X Y Z x y z row col : ℤ) : ℂ) = _
  rcases row with ⟨j,k|k,i⟩|⟨j,k,i⟩ <;> rcases col with ⟨t,v|v|v⟩|⟨t,v|v⟩ <;>
    simp only [matrix,coords,Sum.elim_inl,Sum.elim_inr]
  all_goals apply ec
  all_goals simp

def prodFin {I J : Type} {n k : ℕ} (ei : I ≃ Fin n) (ej : J ≃ Fin k) : I × J ≃ Fin (n*k) :=
  (ei.prodCongr ej).trans finProdFinEquiv

def sumFin {I J : Type} {n k : ℕ} (ei : I ≃ Fin n) (ej : J ≃ Fin k) : I ⊕ J ≃ Fin (n+k) :=
  (Equiv.sumCongr ei ej).trans finSumFinEquiv

def rows (a d e : ℕ) : Rows a d e ≃ Fin (2*((2+e)*a)+d*(2*a)) :=
  sumFin (prodFin (Equiv.refl _) (prodFin finSumFinEquiv (Equiv.refl _))) (prodFin (Equiv.refl _) finProdFinEquiv)

def cols (a d e r : ℕ) : Cols a d e r ≃ Fin (a*((2+d)+((2+e)+a))+r*(2+2)) :=
  sumFin (prodFin (Equiv.refl _) (sumFin finSumFinEquiv (sumFin finSumFinEquiv (Equiv.refl _))))
    (prodFin (Equiv.refl _) finSumFinEquiv)

def flags {n m : ℕ} (a : Array ℕ) (t : Fin n) (u : Fin m) : ℤ := Binary.intBit ((a[t.val]?.getD 0).testBit u.val)

end CriticalTensor.ConsecutiveBorder

namespace CriticalTensor.ConsecutiveBorder

open Binary

lemma rank_of_binary {I J : Type} [Fintype J] [DecidableEq J] {n k : ℕ} (M : Matrix I J ℤ)
    (er : I ≃ Fin n) (ec : J ≃ Fin k) (cols masks : ℕ → ℕ)
    (he : ∀ (i : Fin n) (j : Fin k), M (er.symm i) (ec.symm j) = intBit ((cols j.val).testBit i.val))
    (hc : ∀ i : Fin n, xorColumns cols (masks i.val) k=2^i.val) :
    Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  let N := M.submatrix er.symm ec.symm
  have hs := surjective_of_certificate N cols masks he hc
  have hm : M.map (Int.castRingHom ℂ) = (N.map (Int.castRingHom ℂ)).submatrix er ec := by
    ext i j
    simp [N,Matrix.submatrix,Matrix.map_apply]
  rw [hm]
  intro T
  obtain ⟨v,hv⟩ := hs (T ∘ er.symm)
  refine ⟨v ∘ ec,?_⟩
  rw [Matrix.submatrix_mulVec_equiv]
  have hec : (v ∘ ec) ∘ ec.symm=v := by ext; simp
  rw [hec,hv]
  ext
  simp

def window (f : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => window f start n && f (start+n)

def Before (f : ℕ → Bool) (b : ℕ) := ∀ i < b, f i = true

lemma before_zero (f : ℕ → Bool) : Before f 0 := fun _ h => by omega

lemma extend {f : ℕ → Bool} {b n : ℕ} (earlier : Before f b) (h : window f b n = true) :
    Before f (b+n) := by
  induction n with
  | zero => simpa using earlier
  | succ n ih =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
    intro i hi
    by_cases h' : i < b+n
    · exact ih h₁ i h'
    · have he : i=b+n := by omega
      exact he ▸ h₂

structure RowWindow (f : ℕ → Bool) (n : ℕ) : Type where
  verified : Before f n

def start (f : ℕ → Bool) : RowWindow f 0 := ⟨before_zero f⟩

def nextWindow {f : ℕ → Bool} {b : ℕ} (prev : RowWindow f b) (n : ℕ)
    (h : window f b n = true) : RowWindow f (b+n) := ⟨extend prev.verified h⟩

def directCheck {I J : Type} {n k : ℕ} [NeZero n] (M : Matrix I J ℤ) (er : I ≃ Fin n)
    (ec : J ≃ Fin k) (a b : ℕ → ℕ) (i : ℕ) : Bool :=
  (List.finRange k).all (fun j => M (er.symm (Fin.ofNat n i)) (ec.symm j) == intBit ((a j.val).testBit i)) &&
    (xorColumns a (b i) k == 2^i)

lemma checked {I J : Type} [Fintype J] [DecidableEq J] {n k : ℕ} [NeZero n]
    (M : Matrix I J ℤ) (er : I ≃ Fin n) (ec : J ≃ Fin k) (a b : ℕ → ℕ)
    (h : Before (directCheck M er ec a b) n) : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  apply rank_of_binary M er ec a b
  · intro i j
    have hv := (Bool.and_eq_true_iff.mp (h i.val i.isLt)).1
    have hj := List.all_eq_true.mp hv j (List.mem_finRange _)
    have he : Fin.ofNat n i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    simpa only [beq_iff_eq,he] using hj
  · intro i
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (h i.val i.isLt)).2

end CriticalTensor.ConsecutiveBorder


namespace CriticalTensor.ConsecutiveBorder

/-- Each stored word contains eight fixed-width natural numbers. -/
def packedEntry (t : Array ℕ) (width i : ℕ) : ℕ := (t[i/8]?.getD 0 >>> (width*(i%8))) % 2^width

end CriticalTensor.ConsecutiveBorder

namespace CriticalTensor.BinaryLifting

open CriticalTensor.ConsecutiveBorder.Binary

lemma lift_surj {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] (A : Matrix I K ℤ)
    (h : Function.Surjective (A.map (Int.castRingHom (ZMod 2))).mulVec) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  obtain ⟨b,hb⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
  let B : Matrix K I ℤ := fun j i => (b j i).val
  have he : B.map (Int.castRingHom (ZMod 2)) = b := by
    ext i j
    change (((b i j).val : ℤ) : ZMod 2) = b i j
    simp
  apply complex_surjectivity A B
  rwa [he]

end CriticalTensor.BinaryLifting

namespace CriticalTensor.RectGrid

open MvPolynomial

abbrev Slot (G J : Type) (s : ℕ) := G × J × Fin s
abbrev Parameters (G J W : Type) (s d eLen : ℕ) := Slot G J s × (Fin d ⊕ (Fin eLen ⊕ W))
abbrev Columns (G J W : Type) (s d eLen : ℕ) :=
  (G × Fin s × Fin d) ⊕ ((J × Fin s × Fin eLen) ⊕ (Fin s × W))

variable {s d eLen : ℕ}

def LocalSpan {G J W : Type} [Fintype G] [Fintype J] (a : Slot G J s → Fin d → ℂ) (b : Slot G J s → Fin eLen → ℂ)
    (c : Slot G J s → W → ℂ) (g : G) (h : J) : Prop :=
  ∀ T : Fin d → Fin eLen → W → ℂ,
    ∃ u : G → Fin s → Fin d → ℂ, ∃ v : J → Fin s → Fin eLen → ℂ, ∃ w : Fin s → W → ℂ, ∀ i j k,
      T i j k =
        (∑ l, ∑ t, u l t i * (b (l,h,t) j * c (l,h,t) k)) +
        (∑ l, ∑ t, a (g,l,t) i * (v l t j * c (g,l,t) k)) +
        ∑ t, a (g,h,t) i * (b (g,h,t) j * w t k)

def pad {G : Type} [DecidableEq G] (g : G) (v : Fin d → ℂ) (i : G × Fin d) : ℂ :=
  if g = i.1 then v i.2 else 0

lemma assemble {G J W : Type} [Fintype G] [Fintype J] [DecidableEq G] [DecidableEq J] (a : Slot G J s → Fin d → ℂ) (b : Slot G J s → Fin eLen → ℂ)
    (c : Slot G J s → W → ℂ) (H : ∀ g h, LocalSpan a b c g h)
    (T : (G × Fin d) → (J × Fin eLen) → W → ℂ) :
    ∃ u : Slot G J s → (G × Fin d) → ℂ, ∃ v : Slot G J s → (J × Fin eLen) → ℂ, ∃ w : Slot G J s → W → ℂ, ∀ i j k,
      T i j k = ∑ z, (u z i * (pad z.2.1 (b z) j * c z k) +
        pad z.1 (a z) i * (v z j * c z k) +
        pad z.1 (a z) i * (pad z.2.1 (b z) j * w z k)) := by
  classical
  choose U V Z h using fun g h => H g h (fun i j k => T (g,i) (h,j) k)
  refine ⟨fun z i => U i.1 z.2.1 z.1 z.2.2 i.2,
    fun z j => V z.1 j.1 z.2.1 z.2.2 j.2, fun z => Z z.1 z.2.1 z.2.2, ?_⟩
  rintro ⟨g,i⟩ ⟨f,j⟩ k
  rw [h g f i j k]
  simp only [Finset.sum_add_distrib]
  congr 1
  · congr 1
    · simp [Fintype.sum_prod_type, pad, ite_mul, mul_ite, Finset.sum_ite_irrel]
    · simp [Fintype.sum_prod_type, pad, ite_mul, Finset.sum_ite_irrel]
  · simp [Fintype.sum_prod_type, pad, ite_mul, mul_ite, Finset.sum_ite_irrel]

def aval {G J W : Type} (x : Parameters G J W s d eLen → ℂ) (z : Slot G J s) (i : Fin d) := x (z, Sum.inl i)
def bval {G J W : Type} (x : Parameters G J W s d eLen → ℂ) (z : Slot G J s) (j : Fin eLen) := x (z, Sum.inr (Sum.inl j))
def cval {G J W : Type} (x : Parameters G J W s d eLen → ℂ) (z : Slot G J s) (k : W) := x (z, Sum.inr (Sum.inr k))

noncomputable def polynomialMatrix {G J W : Type} [DecidableEq W] (g : G) (h : J) :
    Matrix (Fin d × Fin eLen × W) (Columns G J W s d eLen) (MvPolynomial (Parameters G J W s d eLen) ℂ)
  | (i,j,k), Sum.inl (l,t,q) =>
      if q = i then X ((l,h,t), Sum.inr (Sum.inl j)) * X ((l,h,t), Sum.inr (Sum.inr k)) else 0
  | (i,j,k), Sum.inr (Sum.inl (l,t,q)) =>
      if q = j then X ((g,l,t), Sum.inl i) * X ((g,l,t), Sum.inr (Sum.inr k)) else 0
  | (i,j,k), Sum.inr (Sum.inr (t,q)) =>
      if q = k then X ((g,h,t), Sum.inl i) * X ((g,h,t), Sum.inr (Sum.inl j)) else 0

lemma polynomial_action {G J W : Type} [Fintype G] [Fintype J] [Fintype W] [DecidableEq W]
    (g : G) (h : J) (x : Parameters G J W s d eLen → ℂ) (y : Columns G J W s d eLen → ℂ) (i : Fin d) (j : Fin eLen) (k : W) :
    ((polynomialMatrix (s:=s) (d:=d) (eLen:=eLen) g h).map (eval x)).mulVec y (i,j,k) =
      (∑ l, ∑ t, y (Sum.inl (l,t,i)) * (bval x (l,h,t) j * cval x (l,h,t) k)) +
      (∑ l, ∑ t, aval x (g,l,t) i * (y (Sum.inr (Sum.inl (l,t,j))) * cval x (g,l,t) k)) +
      ∑ t, aval x (g,h,t) i * (bval x (g,h,t) j * y (Sum.inr (Sum.inr (t,k)))) := by
  classical
  change (∑ z : Columns G J W s d eLen, eval x (polynomialMatrix g h (i,j,k) z) * y z) = _
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, polynomialMatrix, aval, bval, cval,
    apply_ite, Finset.sum_ite_eq', mul_assoc, mul_comm, add_assoc]

lemma local_iff_surjective {G J W : Type} [Fintype G] [Fintype J] [Fintype W] [DecidableEq W]
    (g : G) (h : J) (x : Parameters G J W s d eLen → ℂ) :
    LocalSpan (aval x) (bval x) (cval x) g h ↔
      Function.Surjective ((polynomialMatrix (s:=s) (d:=d) (eLen:=eLen) g h).map (eval x)).mulVec := by
  constructor
  · intro H T
    obtain ⟨u,v,w,hT⟩ := H fun i j k => T (i,j,k)
    let y : Columns G J W s d eLen → ℂ := Sum.elim (fun z => u z.1 z.2.1 z.2.2)
      (Sum.elim (fun z => v z.1 z.2.1 z.2.2) (fun z => w z.1 z.2))
    refine ⟨y, ?_⟩
    funext z
    obtain ⟨i,j,k⟩ := z
    rw [polynomial_action]
    exact (hT i j k).symm
  · intro H T
    obtain ⟨y,hy⟩ := H fun z => T z.1 z.2.1 z.2.2
    refine ⟨fun l t i => y (Sum.inl (l,t,i)), fun l t j => y (Sum.inr (Sum.inl (l,t,j))),
      fun t k => y (Sum.inr (Sum.inr (t,k))), ?_⟩
    intro i j k
    exact (congrFun hy (i,j,k)).symm.trans (polynomial_action g h x y i j k)

lemma simultaneous_local {G J W : Type} [Fintype G] [Fintype J] [Fintype W] [DecidableEq W]
    (H : ∀ (g : G) (h : J), ∃ x : Parameters G J W s d eLen → ℂ, LocalSpan (aval x) (bval x) (cval x) g h) :
    ∃ x : Parameters G J W s d eLen → ℂ, ∀ (g : G) (h : J), LocalSpan (aval x) (bval x) (cval x) g h := by
  classical
  have h (p : G × J) : ∃ x : Parameters G J W s d eLen → ℂ,
      Function.Surjective ((polynomialMatrix p.1 p.2).map (eval x)).mulVec := by
    obtain ⟨x,hx⟩ := H p.1 p.2
    exact ⟨x, (local_iff_surjective _ _ _).mp hx⟩
  obtain ⟨x, _, hx⟩ := RectGrowth.simultaneous_surjectivity (fun p : G × J => polynomialMatrix p.1 p.2)
    h 1 one_ne_zero
  exact ⟨x, fun g h => (local_iff_surjective g h x).mpr (hx (g,h))⟩

def relabel {G J H L : Type} (e : G ≃ H) (f : J ≃ L) (z : Slot G J s) : Slot H L s := (e z.1, f z.2.1, z.2.2)

lemma relabel_local {G J H L W : Type} [Fintype G] [Fintype J] [Fintype H] [Fintype L] (e : G ≃ H) (f : J ≃ L)
    (a : Slot H L s → Fin d → ℂ) (b : Slot H L s → Fin eLen → ℂ) (c : Slot H L s → W → ℂ) (g : G) (h : J)
    (hs : LocalSpan a b c (e g) (f h)) :
    LocalSpan (fun z => a (relabel e f z)) (fun z => b (relabel e f z))
      (fun z => c (relabel e f z)) g h := by
  intro T
  obtain ⟨u,v,w,hT⟩ := hs T
  refine ⟨fun l => u (e l), fun l => v (f l), w, ?_⟩
  intro i j k
  rw [hT i j k]
  dsimp only [relabel]
  congr 1
  congr 1
  · exact (e.sum_comp (fun l => ∑ t, u l t i * (b (l,f h,t) j * c (l,f h,t) k))).symm
  · exact (f.sum_comp (fun l => ∑ t, a (e g,l,t) i * (v l t j * c (e g,l,t) k))).symm

set_option maxHeartbeats 800000 in
/-- One local witness works in every cell after relabeling the two group indices.
Their determinant conditions then hold at a single shared choice of the factors. -/
lemma spans_of_cell {g q d eLen s a : ℕ} [NeZero g] [NeZero q]
    (x₀ : Parameters (Fin g) (Fin q) (Fin a) s d eLen → ℂ)
    (h₀ : LocalSpan (aval x₀) (bval x₀) (cval x₀) 0 0) :
    CriticalTensor.Spans a (g*d) (q*eLen) (g*(q*s)) := by
  classical
  let G := Fin g
  let J := Fin q
  let W := Fin a
  have hw (i : G) (j : J) : ∃ x : Parameters G J W s d eLen → ℂ,
      LocalSpan (aval x) (bval x) (cval x) i j := by
    let e := Equiv.swap i 0
    let f := Equiv.swap j 0
    have ho : LocalSpan (aval x₀) (bval x₀) (cval x₀) (e i) (f j) := by simpa [e,f] using h₀
    exact ⟨fun z => x₀ (relabel e f z.1,z.2), relabel_local e f (aval x₀) (bval x₀) (cval x₀) i j ho⟩
  obtain ⟨x,h⟩ := simultaneous_local hw
  let A := fun z : Slot G J s => pad z.1 (aval x z)
  let B := fun z : Slot G J s => pad z.2.1 (bval x z)
  let C := cval x
  let e : (G × Fin d) ≃ Fin (g*d) := finProdFinEquiv
  let f : (J × Fin eLen) ≃ Fin (q*eLen) := finProdFinEquiv
  let er : Slot G J s ≃ Fin (g*(q*s)) := ((Equiv.refl G).prodCongr finProdFinEquiv).trans finProdFinEquiv
  refine ⟨fun t => C (er.symm t),fun t j => A (er.symm t) (e.symm j),
    fun t k => B (er.symm t) (f.symm k),?_⟩
  intro T
  obtain ⟨u,v,w,hw⟩ := assemble (aval x) (bval x) (cval x) h (fun j k i => T i (e j) (f k))
  refine ⟨fun t => w (er.symm t),fun t j => u (er.symm t) (e.symm j),
    fun t k => v (er.symm t) (f.symm k),?_⟩
  intro i j k
  have hv := hw (e.symm j) (f.symm k) i
  simp only [Equiv.apply_symm_apply] at hv
  rw [hv, ← er.sum_comp]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Equiv.symm_apply_apply,A,B,C]
  ring

end CriticalTensor.RectGrid

namespace CriticalTensor.RectGrid

open MvPolynomial CriticalTensor.ConsecutiveBorder.Binary
open CriticalTensor.ConsecutiveBorder (prodFin sumFin)

def rowOrder (d eLen a : ℕ) : Fin d × Fin eLen × Fin a ≃ Fin (d*(eLen*a)) :=
  prodFin (Equiv.refl _) finProdFinEquiv

def colOrder (g q s d eLen a : ℕ) :
    Columns (Fin g) (Fin q) (Fin a) s d eLen ≃ Fin (g*(s*d)+(q*(s*eLen)+s*a)) :=
  sumFin (prodFin (Equiv.refl _) finProdFinEquiv)
    (sumFin (prodFin (Equiv.refl _) finProdFinEquiv) finProdFinEquiv)

def factorBit {g q s d eLen a : ℕ} (masks : Array ℕ) (p : Parameters (Fin g) (Fin q) (Fin a) s d eLen) : ℤ :=
  let z := p.1
  let idx := ((z.1.val*q+z.2.1.val)*s+z.2.2.val)*3
  match p.2 with
  | .inl i => intBit ((masks[idx]?.getD 0).testBit i.val)
  | .inr (.inl j) => intBit ((masks[idx+1]?.getD 0).testBit j.val)
  | .inr (.inr k) => intBit ((masks[idx+2]?.getD 0).testBit k.val)

def integerMatrix {g q s d eLen a : ℕ} [NeZero g] [NeZero q] (masks : Array ℕ) :
    Matrix (Fin d × Fin eLen × Fin a) (Columns (Fin g) (Fin q) (Fin a) s d eLen) ℤ
  | (i,j,k), .inl (l,t,coord) =>
    if coord=i then factorBit (g:=g) (q:=q) (eLen:=eLen) (s:=s) (d:=d) (a:=a) masks ((l,0,t), Sum.inr (.inl j)) *
      factorBit (g:=g) (q:=q) (eLen:=eLen) (s:=s) (d:=d) (a:=a) masks ((l,0,t), Sum.inr (.inr k)) else 0
  | (i,j,k), .inr (.inl (l,t,coord)) =>
    if coord=j then factorBit (g:=g) (q:=q) (eLen:=eLen) (s:=s) (d:=d) (a:=a) masks ((0,l,t), .inl i) *
      factorBit (g:=g) (q:=q) (eLen:=eLen) (s:=s) (d:=d) (a:=a) masks ((0,l,t), Sum.inr (.inr k)) else 0
  | (i,j,k), .inr (.inr (t,coord)) =>
    if coord=k then factorBit (g:=g) (q:=q) (eLen:=eLen) (s:=s) (d:=d) (a:=a) masks ((0,0,t), .inl i) * factorBit (g:=g) (q:=q) (eLen:=eLen) (s:=s) (d:=d) (a:=a) masks ((0,0,t), .inr (.inl j)) else 0

lemma evaluate_integer {g q s d eLen a : ℕ} [NeZero g] [NeZero q] (masks : Array ℕ) :
    (integerMatrix (g:=g) (q:=q) (eLen:=eLen) (s:=s) (d:=d) (a:=a) masks).map (Int.castRingHom ℂ) =
      (polynomialMatrix (J:=Fin q) (W:=Fin a) (s:=s) (d:=d) (eLen:=eLen) (0:Fin g) 0).map
        (eval (fun p => (factorBit masks p : ℂ))) := by
  ext ⟨i,j,k⟩ z
  rcases z with ⟨l,t,h⟩|⟨l,t,h⟩|⟨t,h⟩ <;>
    simp [Matrix.map_apply,integerMatrix,polynomialMatrix,apply_ite] <;> split <;> simp_all

end CriticalTensor.RectGrid

namespace CriticalTensor.RectGrid

open CriticalTensor.ConsecutiveBorder.Binary

private def addMultiple (v : ℤ) (w z : ℕ) : ℕ := if v%2=0 then z else w ^^^ z

private lemma eval_addMultiple (v : ℤ) (w z j : ℕ) :
    fieldBit ((addMultiple v w z).testBit j) =
      (v : ZMod 2)*fieldBit (w.testBit j) + fieldBit (z.testBit j) := by
  have h : v%2=0 ∨ v%2=1 := by omega
  rw [← ZMod.intCast_mod v 2]
  rcases h with h|h <;> simp [addMultiple,h,Nat.testBit_xor,fieldBit_xor]

private def foldWord : (n : ℕ) → (Fin n → ℕ → ℕ) → ℕ → ℕ
  | 0, _, v => v
  | n+1, f, v => f (Fin.last n) (foldWord n (fun i => f i.castSucc) v)

private lemma eval_fold (j : ℕ) {n : ℕ} (f : Fin n → ℕ → ℕ) (v : ℕ) (g : Fin n → ZMod 2)
    (hf : ∀ i z, fieldBit ((f i z).testBit j) = g i + fieldBit (z.testBit j)) :
    fieldBit ((foldWord n f v).testBit j) = (∑ i,g i) + fieldBit (v.testBit j) := by
  induction n with
  | zero => simp [foldWord]
  | succ n ih =>
    rw [foldWord,hf,ih (fun i => f i.castSucc) (fun i => g i.castSucc)
      (fun i => hf i.castSucc),Fin.sum_univ_castSucc]
    abel

section RowProduct
variable {g q s d eLen a : ℕ} [NeZero g] [NeZero q]
private abbrev Key (g q s d eLen a : ℕ) := Columns (Fin g) (Fin q) (Fin a) s d eLen

/-- Only three column families can contribute to one row. The multiplier carries
all output columns simultaneously in the bits of one natural number. -/
def rowProduct (data : Array ℕ) (b : Key g q s d eLen a → ℕ) (r : Fin d × Fin eLen × Fin a) : ℕ :=
  let op := fun c acc => addMultiple (integerMatrix data r c) (b c) acc
  let v := foldWord g (fun l z => foldWord s (fun t => op (.inl (l,t,r.1))) z) 0
  let w := foldWord q (fun l z => foldWord s (fun t => op (.inr (.inl (l,t,r.2.1)))) z) v
  foldWord s (fun t => op (.inr (.inr (t,r.2.2)))) w

private lemma eval_product (data : Array ℕ) (b : Key g q s d eLen a → ℕ) (r : Fin d × Fin eLen × Fin a) (j : ℕ) :
    fieldBit ((rowProduct data b r).testBit j) =
      ∑ k, ((integerMatrix data r k : ℤ) : ZMod 2) * fieldBit ((b k).testBit j) := by
  obtain ⟨u,v,w⟩ := r
  let f : Key g q s d eLen a → ZMod 2 := fun k => ((integerMatrix data (u,v,w) k : ℤ) : ZMod 2)*fieldBit ((b k).testBit j)
  let op := fun (k : Key g q s d eLen a) (z : ℕ) => addMultiple (integerMatrix data (u,v,w) k) (b k) z
  have step (k : Key g q s d eLen a) (z : ℕ) : fieldBit ((op k z).testBit j) = f k + fieldBit (z.testBit j) := eval_addMultiple _ _ _ _
  have twice {n : ℕ} (c : Fin n → Fin s → Key g q s d eLen a) (z : ℕ) :
      fieldBit ((foldWord n (fun l y => foldWord s (fun t => op (c l t)) y) z).testBit j) =
        (∑ l, ∑ t, f (c l t)) + fieldBit (z.testBit j) := by
    apply eval_fold
    intro l y
    exact eval_fold j _ y _ (fun t => step _)
  change fieldBit ((foldWord s (fun t => op (.inr (.inr (t,w))))
    (foldWord q (fun l z => foldWord s (fun t => op (.inr (.inl (l,t,v)))) z)
      (foldWord g (fun l z => foldWord s (fun t => op (.inl (l,t,u))) z) 0))).testBit j) = ∑ k, f k
  rw [eval_fold (g:=fun t => f (.inr (.inr (t,w)))) (hf:=fun t => step _)]
  rw [twice (fun l t => .inr (.inl (l,t,v))), twice (fun l t => .inl (l,t,u))]
  have right :
      (∑ k, f k) = (∑ l,∑ t, f (.inl (l,t,u))) +
        ((∑ l,∑ t, f (.inr (.inl (l,t,v)))) + ∑ t,f (.inr (.inr (t,w)))) := by
    simp [f,Fintype.sum_sum_type,Fintype.sum_prod_type,integerMatrix,apply_ite,ite_mul]
  rw [right]
  simp only [Nat.zero_testBit,fieldBit,Bool.false_eq_true,if_false,add_zero]
  abel

end RowProduct

open CriticalTensor.BinaryLifting (lift_surj)

def fit (w i : ℕ) : Bool := w.testBit i && (w >>> (i+1) == 0)

private lemma off_bit {w i j : ℕ} (h : fit w i = true) (hj : i<j) : w.testBit j = false := by
  have he := congrArg (fun z : ℕ => z.testBit (j-(i+1))) (beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2)
  simp only [Nat.testBit_shiftRight,Nat.zero_testBit] at he
  rwa [show i+1+(j-(i+1))=j by omega] at he

lemma from_rows {g q s d eLen a : ℕ} [NeZero g] [NeZero q] (data : Array ℕ) (b : Columns (Fin g) (Fin q) (Fin a) s d eLen → ℕ)
    (h : ∀ i : Fin (d*(eLen*a)), fit (rowProduct data b ((rowOrder d eLen a).symm i)) i.val = true) :
    CriticalTensor.Spans a (g*d) (q*eLen) (g*(q*s)) := by
  let e := rowOrder d eLen a
  let K := Columns (Fin g) (Fin q) (Fin a) s d eLen
  let M : Matrix (Fin (d*(eLen*a))) K ℤ := fun i j => integerMatrix data (e.symm i) j
  let N := M.map (Int.castRingHom (ZMod 2))
  let T : Matrix K (Fin (d*(eLen*a))) (ZMod 2) := fun j i => fieldBit ((b j).testBit i.val)
  let L := N*T
  have hL (i j : Fin (d*(eLen*a))) : L i j = fieldBit ((rowProduct data b (e.symm i)).testBit j.val) :=
    (eval_product data b (e.symm i) j.val).symm
  have ht : L.IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    have bit : (rowProduct data b (e.symm i)).testBit j.val = false := off_bit (h i) hij
    rw [hL,bit]
    rfl
  have hd : L.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular L ht]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [hL]
    have bit : (rowProduct data b (e.symm i)).testBit i.val = true := (Bool.and_eq_true_iff.mp (h i)).1
    rw [bit]
    exact one_ne_zero
  have hsurj : Function.Surjective L.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  have hn : Function.Surjective N.mulVec := by
    intro y
    obtain ⟨z,hz⟩ := hsurj y
    exact ⟨T.mulVec z,(Matrix.mulVec_mulVec _ _ _).trans hz⟩
  have hs := lift_surj M hn
  apply spans_of_cell (fun p => (factorBit data p : ℂ))
  apply (local_iff_surjective _ _ _).mpr
  rw [← evaluate_integer]
  intro y
  obtain ⟨z,hz⟩ := hs (y ∘ e.symm)
  refine ⟨z,?_⟩
  funext i
  have h' := congrFun hz (e i)
  change (∑ k, ((M (e i) k : ℤ) : ℂ)*z k) = y (e.symm (e i)) at h'
  change (∑ k, ((integerMatrix data i k : ℤ) : ℂ)*z k)=y i
  simpa only [M,Equiv.symm_apply_apply] using h'

end CriticalTensor.RectGrid

namespace CriticalTensor.RectGrid

open CriticalTensor.ConsecutiveBorder.Binary

/-- Natural-index folds keep numeric execution independent of the finite index casts. -/
private def sweep (f : ℕ → ℕ → ℕ) (z : ℕ) : ℕ → ℕ
  | 0 => z
  | t+1 => f t (sweep f z t)

private lemma fold_index (f : ℕ → ℕ → ℕ) (z n : ℕ) :
    foldWord n (fun t => f t.val) z = sweep f z n := by
  induction n with
  | zero => rfl
  | succ n h => exact congrArg (f n) h

private def productBit (data : Array ℕ) (t u i v j : ℕ) : Bool :=
  (data[t+u]?.getD 0).testBit i && (data[t+v]?.getD 0).testBit j

private def addBit (h : Bool) (w z : ℕ) := if h then w ^^^ z else z

private lemma add_bits (a b : Bool) (w z : ℕ) :
    addMultiple (intBit a * intBit b) w z = addBit (a && b) w z := by
  cases a <;> cases b <;> simp [intBit,addMultiple,addBit]

def fastProduct (g q s d eLen a : ℕ) (data : Array ℕ) (b : ℕ → ℕ) (i j k : ℕ) : ℕ :=
  let u := sweep (fun l z => sweep (fun t =>
    addBit (productBit data ((l*q*s+t)*3) 1 j 2 k) (b ((l*s+t)*d+i))) z s) 0 g
  let v := sweep (fun l z => sweep (fun t =>
    addBit (productBit data ((l*s+t)*3) 0 i 2 k) (b (g*(s*d)+(l*s+t)*eLen+j))) z s) u q
  sweep (fun t => addBit (productBit data (t*3) 0 i 1 j) (b (g*(s*d)+(q*(s*eLen)+t*a+k)))) v s

private lemma col1 {g q s d eLen a : ℕ} (l : Fin g) (t : Fin s) (h : Fin d) :
    (colOrder g q s d eLen a (.inl (l,t,h))).val = (l.val*s+t.val)*d+h.val := by
  change h.val + d*t.val + s*d*l.val = _
  ring

private lemma col2 {g q s d eLen a : ℕ} (l : Fin q) (t : Fin s) (h : Fin eLen) :
    (colOrder g q s d eLen a (.inr (.inl (l,t,h)))).val = g*(s*d)+(l.val*s+t.val)*eLen+h.val := by
  change g*(s*d)+(h.val+eLen*t.val+s*eLen*l.val) = _
  ring

private lemma col3 {g q s d eLen a : ℕ} (t : Fin s) (h : Fin a) :
    (colOrder g q s d eLen a (.inr (.inr (t,h)))).val = g*(s*d)+(q*(s*eLen)+t.val*a+h.val) := by
  change g*(s*d)+(q*(s*eLen)+(h.val+a*t.val)) = _
  ring

lemma fast_correct {g q s d eLen a : ℕ} [NeZero g] [NeZero q] (data : Array ℕ) (b : ℕ → ℕ)
    (i : Fin d) (j : Fin eLen) (k : Fin a) :
    rowProduct data (fun c => b (colOrder g q s d eLen a c).val) (i,j,k) = fastProduct g q s d eLen a data b i.val j.val k.val := by
  have h₁ (l : Fin g) (t : Fin s) (z : ℕ) :
      addMultiple (integerMatrix (g:=g) (q:=q) (eLen:=eLen) data (i,j,k) (.inl (l,t,i))) (b (colOrder g q s d eLen a (.inl (l,t,i))).val) z =
        addBit (productBit data ((l.val*q*s+t.val)*3) 1 j.val 2 k.val) (b ((l.val*s+t.val)*d+i.val)) z := by
    rw [col1]
    simp [integerMatrix,factorBit,productBit,add_bits]
  have h₂ (l : Fin q) (t : Fin s) (z : ℕ) :
      addMultiple (integerMatrix (g:=g) (q:=q) (eLen:=eLen) data (i,j,k) (.inr (.inl (l,t,j)))) (b (colOrder g q s d eLen a (.inr (.inl (l,t,j)))).val) z =
        addBit (productBit data ((l.val*s+t.val)*3) 0 i.val 2 k.val) (b (g*(s*d)+(l.val*s+t.val)*eLen+j.val)) z := by
    rw [col2]
    simp [integerMatrix,factorBit,productBit,add_bits]
  have h₃ (t : Fin s) (z : ℕ) :
      addMultiple (integerMatrix (g:=g) (q:=q) (eLen:=eLen) data (i,j,k) (.inr (.inr (t,k)))) (b (colOrder g q s d eLen a (.inr (.inr (t,k)))).val) z =
        addBit (productBit data (t.val*3) 0 i.val 1 j.val) (b (g*(s*d)+(q*(s*eLen)+t.val*a+k.val))) z := by
    rw [col3]
    simp [integerMatrix,factorBit,productBit,add_bits]
  unfold rowProduct fastProduct
  have op₁ (l : Fin g) (t : Fin s) : addMultiple (integerMatrix (g:=g) (q:=q) (eLen:=eLen) data (i,j,k) (.inl (l,t,i))) (b (colOrder g q s d eLen a (.inl (l,t,i))).val) =
      addBit (productBit data ((l.val*q*s+t.val)*3) 1 j.val 2 k.val) (b ((l.val*s+t.val)*d+i.val)) := funext (h₁ l t)
  have op₂ (l : Fin q) (t : Fin s) : addMultiple (integerMatrix (g:=g) (q:=q) (eLen:=eLen) data (i,j,k) (.inr (.inl (l,t,j)))) (b (colOrder g q s d eLen a (.inr (.inl (l,t,j)))).val) =
      addBit (productBit data ((l.val*s+t.val)*3) 0 i.val 2 k.val) (b (g*(s*d)+(l.val*s+t.val)*eLen+j.val)) := funext (h₂ l t)
  have op₃ (t : Fin s) : addMultiple (integerMatrix (g:=g) (q:=q) (eLen:=eLen) data (i,j,k) (.inr (.inr (t,k)))) (b (colOrder g q s d eLen a (.inr (.inr (t,k)))).val) =
      addBit (productBit data (t.val*3) 0 i.val 1 j.val) (b (g*(s*d)+(q*(s*eLen)+t.val*a+k.val))) := funext (h₃ t)
  simp only [op₁,op₂,op₃,← fold_index]

lemma from_bits {g q s d eLen a : ℕ} [NeZero g] [NeZero q] (data : Array ℕ) (b : ℕ → ℕ)
    (h : ∀ i : Fin (d*(eLen*a)), let p := (rowOrder d eLen a).symm i
      fit (fastProduct g q s d eLen a data b p.1.val p.2.1.val p.2.2.val) i.val = true) :
    CriticalTensor.Spans a (g*d) (q*eLen) (g*(q*s)) := by
  apply from_rows data (fun c => b (colOrder g q s d eLen a c).val)
  intro i
  have he := fast_correct (g:=g) (q:=q) (eLen:=eLen) (s:=s) (a:=a) data b ((rowOrder d eLen a).symm i).1 ((rowOrder d eLen a).symm i).2.1 ((rowOrder d eLen a).symm i).2.2
  exact (congrArg (fun w => fit w i.val) he).trans (h i)

end CriticalTensor.RectGrid

namespace CriticalTensor.RectGrid

/-- Decode consecutive 16-bit blocks. Zero and one- or two-bit blocks
are represented by flags and positions. Other blocks store all sixteen bits. -/
def unpack16 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, v =>
    if v=0 then 0
    else if v%2=0 then (unpack16 n (v >>> 1)) <<< 16
    else if v%4=1 then (1 <<< ((v >>> 2)%16)) ||| ((unpack16 n (v >>> 6)) <<< 16)
    else if v%8=3 then (1 <<< ((v >>> 3)%16)) ||| (1 <<< ((v >>> 7)%16)) |||
      ((unpack16 n (v >>> 11)) <<< 16)
    else ((v >>> 3)%65536) ||| ((unpack16 n (v >>> 19)) <<< 16)

end CriticalTensor.RectGrid

namespace CriticalTensor.RectGrid.Twenty

open CriticalTensor.ConsecutiveBorder (RowWindow start nextWindow)

private def factors : Array ℕ := #[0x1, 0x1, 0x1, 0x2, 0x2, 0x2, 0x1a, 0x7, 0x14, 0x15, 0x2, 0x3d, 0x16, 0x1, 0x1e, 0x5, 0x5, 0x2e, 0x9, 0x2, 0x35, 0x3, 0x5, 0x35, 0x19, 0x7, 0x1a, 0x5, 0x4, 0x5, 0x19, 0x1, 0x2b, 0xe, 0x2, 0x15, 0x17, 0x2, 0x2a, 0xa, 0x1, 0x17, 0x8, 0x4, 0x3b, 0x13, 0x3, 0x33, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x8, 0x7, 0x39, 0x2, 0x7, 0x1f, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x7, 0x4, 0x18, 0x12, 0x5, 0x12, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]
private def t0 : Array ℕ := #[0x2467c110920f7c400900401, 0x20124c00e84010000940000, 0x21840000002d000000000, 0x2033c4007c0000000000000, 0x20209000000000000000000, 0x2433cd18000f40000000680, 0x24630520020900402000000, 0x3394cd00000280000000000]
private def t1 : Array ℕ := #[0x13018d2a000000000000000, 0x20680000000000000000000, 0x3703c008030000900018000, 0x273181c0020000140000000, 0x303c008026000000000000, 0x27318880000000000000000, 0x16000000000000000000000, 0x2433cd18000f40000000c00]
private def t2 : Array ℕ := #[0x27218400020000400000000, 0x10224000000000000000000, 0x30200000000000000000000, 0x20000000000000000000000, 0x37800000000000000000800, 0x27458800000000000000000, 0x14368d00000000000000000, 0x27870000000000000000000]
private def t3 : Array ℕ := #[0x37c00000000000000000000, 0x3303cd08000000000000000, 0x30640c00000000000000000, 0x10564000004000000000000, 0x27100000000000000000000, 0x37760000000000000000000, 0x3703c008030000900030000, 0x1005c0000000200000000]
private def t4 : Array ℕ := #[0x37224000008000000000000, 0x34100a00000000000000000, 0x8000000000000000000000, 0x3083c00803000090003a000, 0x640c00020000400400000, 0x1314cd0000000a000000000, 0xa68400c00000000000000, 0xc0a000000000000000000]
private def t5 : Array ℕ := #[0x0, 0xe30008004440000000f40, 0x17740d0003000090003d000, 0x17018400e80000000680000, 0x0, 0x34000dc8033000580000000, 0x20024000ea0030400800000, 0x970014000000000000000]
private def t6 : Array ℕ := #[0x270009c0000000000000000, 0x17000000000000000000000, 0x37800000000000000000000, 0x30000000000000000000000, 0x740000004020000000000, 0x740000004a00000000000, 0x27740000020000000000000, 0x4414900004008000000000]
private def t7 : Array ℕ := #[0x460cd00004b00000000a00, 0x30414d08000000000020000, 0x318400100000000000000, 0x970031000000000000000, 0x270004c0010000000000000, 0x17318800024020400900000, 0x39000740000000000, 0x170009c0020000900000000]
private def t8 : Array ℕ := #[0x17018400a00000000000000, 0x17a70018000800000000000, 0x34000000000000000000000, 0x1341490000401c000000000, 0x740000004c40000000b00, 0x3428d00030000900024000, 0x17968400800000000000000, 0x17300010000000000000000]
private def t9 : Array ℕ := #[0x27b68000000000000000000, 0x10224000000030000000000, 0x23b68d00000c00000000000, 0x34218008013000800000000, 0x17558400004020000200000, 0x37f40000004300000000000, 0x17740000000000000000000, 0x17018400e80000000000000]
private def t10 : Array ℕ := #[0x4a68d20000000000000000, 0x13318c08013000000000000, 0x0, 0x34300d18230f6890023ac02, 0x2403c108124034400900004, 0x8200028000200808, 0x7324818b14f60d0093a410, 0x17318818924f48400b00420]
private def t11 : Array ℕ := #[0x17100019020b40401000000, 0x0, 0x17970c0d004140004000000, 0x20a18400000900008000000, 0x17f3000d024140410000000, 0x37900c39024440420000000]
private def tabs := #[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]
private def mult (j : ℕ) := ((tabs[j/8]?.getD #[])[j%8]?).getD 0

private def checkAt (i : ℕ) : Bool :=
  let p := (rowOrder 5 3 6).symm (Fin.ofNat 90 i)
  fit (fastProduct 4 7 2 5 3 6 factors mult p.1.val p.2.1.val p.2.2.val) i
private def r5 : RowWindow checkAt 5 := nextWindow (start checkAt) 5 (by decide +kernel)
private def r10 : RowWindow checkAt 10 := nextWindow r5 5 (by decide +kernel)
private def r15 : RowWindow checkAt 15 := nextWindow r10 5 (by decide +kernel)
private def r20 : RowWindow checkAt 20 := nextWindow r15 5 (by decide +kernel)
private def r25 : RowWindow checkAt 25 := nextWindow r20 5 (by decide +kernel)
private def r30 : RowWindow checkAt 30 := nextWindow r25 5 (by decide +kernel)
private def r35 : RowWindow checkAt 35 := nextWindow r30 5 (by decide +kernel)
private def r40 : RowWindow checkAt 40 := nextWindow r35 5 (by decide +kernel)
private def r45 : RowWindow checkAt 45 := nextWindow r40 5 (by decide +kernel)
private def r50 : RowWindow checkAt 50 := nextWindow r45 5 (by decide +kernel)
private def r55 : RowWindow checkAt 55 := nextWindow r50 5 (by decide +kernel)
private def r60 : RowWindow checkAt 60 := nextWindow r55 5 (by decide +kernel)
private def r65 : RowWindow checkAt 65 := nextWindow r60 5 (by decide +kernel)
private def r70 : RowWindow checkAt 70 := nextWindow r65 5 (by decide +kernel)
private def r75 : RowWindow checkAt 75 := nextWindow r70 5 (by decide +kernel)
private def r80 : RowWindow checkAt 80 := nextWindow r75 5 (by decide +kernel)
private def r85 : RowWindow checkAt 85 := nextWindow r80 5 (by decide +kernel)
private def r90 : RowWindow checkAt 90 := nextWindow r85 5 (by decide +kernel)

theorem spans : CriticalTensor.Spans 6 20 21 56 := by
  apply from_bits (g:=4) (q:=7) (s:=2) (d:=5) (eLen:=3) (a:=6) factors mult
  intro i
  have ok := r90.verified i.val i.isLt
  have hi : Fin.ofNat 90 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [checkAt,hi] using ok

end CriticalTensor.RectGrid.Twenty

namespace CriticalTensor.ConsecutiveSixBase

open CriticalTensor.RectGrid
open CriticalTensor.ConsecutiveBorder (RowWindow start nextWindow)

namespace Six

private def points : Array ℕ := #[
    0x1, 0x1, 0x1, 0x2, 0x2, 0x2, 0x4, 0x4, 0x4,
    0x8, 0x8, 0x8, 0x10, 0x10, 0x10, 0x20, 0x20, 0x20,
    0x23, 0x40, 0x24, 0x11, 0x9, 0x14, 0xf, 0x71, 0x1e,
    0x3d, 0x6e, 0x26, 0x14, 0x12, 0x3, 0xc, 0x56, 0x39,
    0x1b, 0x65, 0x11, 0x13, 0x5f, 0x21, 0x29, 0x4e, 0x9]
private def unpack := unpack16 16

private def t0 : Array ℕ := #[
    unpack 0x6c0e42c1e4083d1c078480e0a0c0732b0700bb001381, unpack 0x2c0e52c9fcdeae836eccac158801c, unpack 0x966024dcdd966a56902b0e0, unpack 0x2999ca07f57aba0dbb327c80,
    unpack 0x53bb672015c0b03d2b8400, (0x9410019 <<< 210), unpack 0x190384837fc7281051d592ebb, unpack 0x2c0e328df05fcbf36c6dc30399580169ec58,
    unpack 0x53b3106f86c8503d9b000c5ff5da0, unpack 0x640e120dff1ca04a203a090700, (0x72c9001444810415 <<< 175), (0x26008336f <<< 217),
    unpack 0xa667281fcdbb1101c12880e0d1c02f29220f9, unpack 0x5333940fe6dd8880e0944070143c038, unpack 0x4b6ae4023d04073adb2240, unpack 0x26071846f86c3100]
private def t1 : Array ℕ := #[
    unpack 0x14ec819b9b4301fd9800, (0x2403063 <<< 224), unpack 0x293016f6cbb5ba9682a, unpack 0x152c6093bdd9a969e8,
    unpack 0x4c0e1245ff1819940, 0, (0x3601882400541001 <<< 189), (0x1 <<< 231),
    unpack 0xe90a27c68a0380127b8607000b0e62, unpack 0x3a1249f1a280e0049ee181c190, unpack 0x94a403f8b81c0e0080, unpack 0x4a5085fdd62203b1bda600,
    0, (0x1 <<< 238), unpack 0x6c0e4289f1f76e836eccac1d00e34, unpack 0x26073140fe6ff5ba0dbb32b350]
private def t2 : Array ℕ := #[
    unpack 0xd01ec9c80472280e0e80, unpack 0x2598cb07c765c44071400, (0x480728820011 <<< 203), (0x5 <<< 245),
    unpack 0x21d988173166601dd637a812cc, unpack 0x8663205cc5c880775a8000de0, unpack 0x5270c1c402bc372f4df5bf97a80, unpack 0x16071846f86e5dfdb4400,
    (0x110021980023 <<< 206), 0, unpack 0x4a3045cc5d0c079a00faf25a04646, unpack 0x3a7089c55cbd45a73b8c,
    unpack 0x26072026e0334c20, unpack 0x25dfdb0100, 0, unpack 0x209a2000]
private def t3 : Array ℕ := #[
    0, 0, (0x5000248001 <<< 211), unpack 0xc8c807340e03fdb1e80,
    unpack 0xf969400, (0x1 <<< 232), unpack 0x1303db3f60603fdb6a00, unpack 0x5222c9fcd81c07fb6d4168,
    0, unpack 0x14ec4503f9bf965a00, unpack 0x36071924e6c3e800, (0x80045121 <<< 218),
    unpack 0x53b1140fe6e50207564a, unpack 0x152c6403e3f2fed8024f50c0e656005a70, unpack 0x190384b27f370efed83b6ed9771d20, unpack 0xa762281fcdca04a203a488700]
private def t4 : Array ℕ := #[
    unpack 0x1b039c827c37281057e400, (0x649 <<< 216), (0x1 <<< 247), (0x401 <<< 237),
    0, unpack 0xd81c809b8a0701fe590607e7d00, (0x16018824005 <<< 209), 0,
    unpack 0x4bb2166fe6e0a03fdb2480701c00e24, 0, unpack 0x1b0390117c170381c19a40, unpack 0x3026e8380ff6c1c4900,
    (0x2201083080500c0015 <<< 181), unpack 0x4b2000, (0x143 <<< 229), 0]
private def t5 : Array ℕ := #[
    (0xc801 <<< 235), unpack 0x152c2093a0a03c44070d00, (0x3601012400500c005 <<< 185), (0x9 <<< 234),
    (0xc00704c1 <<< 219), unpack 0x54b1824ef402598, (0x4c009229 <<< 220), (0x1b00551b60028802220001210201 <<< 142),
    unpack 0xd81cc413c0057f5c5800, 0, 0, unpack 0x34071c42fc2e8a03f9b052403834028b9287207,
    unpack 0x25d96807c008e4501fed9240380e0079497e3, unpack 0x680e58e5f6003ec3ba603112, unpack 0x4bbd572011fdfb6c6d430399580065c2b00e, unpack 0xa967201cd2280ff6c9201c05403885f2]
private def t6 : Array ℕ := #[
    unpack 0x9765a01f002391407fb64900e055c02e44, unpack 0x253104fe6fe58101b6c, 0, unpack 0x581c2183a503a82dd8,
    unpack 0x12cce183a5d81169a8, unpack 0x976ac8047f7edb1b50c0e656004c70, unpack 0xc84b27f37e9a85cb0, unpack 0x12903077eb0024fd43d0,
    unpack 0xe00ba106690340e0, unpack 0x748593a0a038440f75b645620, 0, unpack 0xd81ce58be34401fed9240381a01c0,
    unpack 0x976524dfd2180f0103d0b2e40, unpack 0x642593f9b8180ff6c9201c880, unpack 0x16072864fe2e8203dcbd50481f6980, unpack 0x1303e43560e03fdb0500]
private def t7 : Array ℕ := #[
    unpack 0x13039e217e48e03c9b2048eee040700, (0x201603280551804140102400401 <<< 141), (0x1803aedb001440111000090811 <<< 147), unpack 0x251026e2fa1501f5e9600,
    unpack 0x581c6093a0e03fdb7a00, (0x3001232200151004140105 <<< 165), (0x803064000a024080a03 <<< 172), unpack 0xecc248bfe3942233800,
    unpack 0x2c0e52cdd30e2c03800, (0x1300c08040088403 <<< 190), (0x68018468008215 <<< 196), unpack 0xb03db3f69000,
    (0x6802100000b <<< 208), (0x480801 <<< 215), (0x14016835 <<< 221), (0x1803ad <<< 227)]
private def t8 : Array ℕ := #[
    (0x14017 <<< 233), (0x1 <<< 239), 0, (0x1 <<< 251),
    unpack 0x104c5f8772f5169c8, unpack 0x29d8cb3717e58444705e403fc300, unpack 0x129cb274c3741b7602d4b0a, unpack 0x190860f0015e61fcbd400,
    unpack 0x1164e8402a30, unpack 0x642593f9b8280ff6da85d30, (0x1 <<< 248), unpack 0xa66420ddefdba400,
    unpack 0x14ec018b8b0601c222383d8fe18a3421, unpack 0x12ec059bfe3977f6d70c07003d2482, (0x2802066100021809 <<< 188), unpack 0x860e0074652]
private def t9 : Array ℕ := #[
    unpack 0xc84b27f370501fed9240385204, unpack 0x12ec059bfe3977f6d70c120, unpack 0x12841277a00d4, unpack 0x976704dc596cd800,
    (0x4803 <<< 236), unpack 0xa474d4b40, unpack 0xa77a80150, unpack 0x2a5841277a02d0,
    unpack 0x640e2249cda200e6400, unpack 0x426fa04a0, unpack 0x130388307100af2d9b0280, 0,
    unpack 0x57d74d4c80, unpack 0x2183801d0, (0xd001248200145 <<< 199), unpack 0x767b6d4401cc6c00]
private def t10 : Array ℕ := #[
    unpack 0xb038c12701c07fb609560, unpack 0x1d3944f2011e0903f9b6a657f8c0, unpack 0x12eca513e3fac20c3800, unpack 0x251944f8d040735321181c0,
    0, unpack 0xc81c2593f9b8180ff6da8c980, unpack 0x25980a27c68403fdb3076db080, unpack 0x1db866fa03a0,
    unpack 0x67458ba844477400, unpack 0x981cc11be1ba080ff6dd6600700, unpack 0x9420939d35336ec0, unpack 0x54b3806f2011f65bae8f40,
    unpack 0x9760249cdf414d80, 0, unpack 0x3b32806f82c0d03fdb0712d39e4, unpack 0x6c0e404dc402b81c078280fabe18a3429]
private def t11 : Array ℕ := #[
    unpack 0x14cc218b8b2efe5e83c4148, unpack 0x26072026e97ed83b8c010, unpack 0x6c0e2285c4381fe59024760c0e00, unpack 0xa6d5e0b01c0e0310,
    unpack 0x126c1207f964109c00, unpack 0xd01e158a0701e0a03ea2d39f4, unpack 0x981ce18bfe38380f1101c15900ff0c502d, unpack 0x1b0384127f37f2c094407016a58,
    unpack 0x14cc64138aedcbd75010788, unpack 0x640e62c9d08000b0e6a, unpack 0x152ca593f9ba380ff6c1b766566430, (0x240284280021 <<< 204),
    unpack 0x10aa000, unpack 0x2a584127b172d9b0025, unpack 0x54b0826f6fa003d, (0x600083 <<< 228)]
private def t12 : Array ℕ := #[
    unpack 0x35002a5a, unpack 0x2a584127005a14, unpack 0x54b0826f6fa00a0, 0,
    unpack 0x976a4d28119b6535345, unpack 0x5330126e691c07fc749480732936e75449, unpack 0x942493ab2ad01a8d, unpack 0xa66400dfda300ff8e9b8603803f96004ec8d1,
    unpack 0x2503f9bf766a652883c7d755, unpack 0x148c3379008ee801278ce0732b1a016dc09078, 0, unpack 0x581c4593f9b8380f1101c15900ff0c2c98,
    unpack 0xa2fcbb360009238, unpack 0x14ec818b880579861111c1c7e18a3488, unpack 0x4c0e20c1c402bcb66c0a2d58, unpack 0x53b2066e62e0703c01870089fb6f1003b340c0]
private def t13 : Array ℕ := #[
    unpack 0x94c093a5d8418706db65140, 0, unpack 0xa76208df0dcbbfb6ecd9801ed340, unpack 0x1a03882173170681fedbb366007c6748c0,
    unpack 0x6c0e404dc50380ff2c8303f5b4e00e540, (0x600117298008200880000495081 <<< 144), unpack 0x976a4d2812802e00, unpack 0x2c0e1245ff1882600,
    0, unpack 0x16072802f86fdd817010e00, unpack 0xca93414078880eb5600, (0x640206010080281 <<< 192),
    (0x2400c30480040c1 <<< 193), unpack 0x1d1042fed0027000, (0x18072410014041 <<< 195), 0]
private def t14 : Array ℕ := #[
    (0x2600413000140d <<< 197), (0x481 <<< 240), (0x141 <<< 241), (0xb1 <<< 242),
    (0x1 <<< 243), (0x2d <<< 244), 0, unpack 0x6715e0b3280ff6dc98c40732b390,
    unpack 0x191900e681c07fb668054, unpack 0xe94137800ae6301e2203b2064c94, unpack 0xb03909273688039901474, unpack 0x29d94a37c68c0380317e2091c00e84,
    0, unpack 0x680e2fe386e9800, unpack 0x3a6041fd033681a, unpack 0x4bb0146e6fcbfb66900e6468232]
private def t15 : Array ℕ := #[
    unpack 0x12841274ab400, 0, unpack 0x1aafd74d4c820f13a, unpack 0x74e083e0bd67f6da99580,
    unpack 0x9662049c0701fed800, unpack 0x14cc4093a1000, 0, unpack 0x252705c0e07000,
    (0x1b <<< 246), (0x140082140005 <<< 205), unpack 0x54b1964ff8e82039a85a7a, unpack 0xa9632c9ff1d1007fb64900e00,
    (0x1800209 <<< 226), (0x1601401 <<< 225), unpack 0xa664fa000, unpack 0x4bb0964e2d1a0775cdea0260ffac0]
private def t16 : Array ℕ := #[
    0, unpack 0x64c40bfbb2c2207800, unpack 0x2a5841277aebb32d6a0, unpack 0xb03940177aebb331720,
    unpack 0xd01f458bf0c2a0390607eb7f2c57a0, unpack 0x290826ea080e307b6ed00, unpack 0x253004feca076ddb280, unpack 0x1d2144e6cbbfb685900,
    unpack 0x2a588837fc74401cc9680, unpack 0x2c0e3049d4401cc9880, unpack 0x30c9e402bd1807b97acfadfcb00, unpack 0x4bb1964fe6fe5812880e00,
    0, (0x3 <<< 249), unpack 0x152c2093bd000, 0]
private def t17 : Array ℕ := #[
    unpack 0x32a4d0501e2203800, unpack 0xd01c841b8b0501fe5e83c4050, unpack 0x4b32904fe6e1dfdb0400, (0x30085 <<< 230),
    (0x1 <<< 250), unpack 0x3230c5c5977f2f41e200, 0, (0x1200f183 <<< 222),
    unpack 0x536ae4023ebb020b4f75, unpack 0x14cc049b9a4501ce41a0, 0, unpack 0x2c0e5005f0dfa7200,
    (0x24008a0400441 <<< 201)]

private def tables := #[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17]
private def multiplier (j : ℕ) := ((tables[j/16]?.getD #[])[j%16]?).getD 0

private def checkAt (q : ℕ) : Bool :=
  let p := (rowOrder 6 7 6).symm (Fin.ofNat 252 q)
  fit (fastProduct 1 1 15 6 7 6 points multiplier p.1.val p.2.1.val p.2.2.val) q

private def w12 : RowWindow checkAt 12 := nextWindow (start checkAt) 12 (by decide +kernel)
private def w24 : RowWindow checkAt 24 := nextWindow w12 12 (by decide +kernel)
private def w36 : RowWindow checkAt 36 := nextWindow w24 12 (by decide +kernel)
private def w48 : RowWindow checkAt 48 := nextWindow w36 12 (by decide +kernel)
private def w60 : RowWindow checkAt 60 := nextWindow w48 12 (by decide +kernel)
private def w72 : RowWindow checkAt 72 := nextWindow w60 12 (by decide +kernel)
private def w84 : RowWindow checkAt 84 := nextWindow w72 12 (by decide +kernel)
private def w96 : RowWindow checkAt 96 := nextWindow w84 12 (by decide +kernel)
private def w108 : RowWindow checkAt 108 := nextWindow w96 12 (by decide +kernel)
private def w120 : RowWindow checkAt 120 := nextWindow w108 12 (by decide +kernel)
private def w132 : RowWindow checkAt 132 := nextWindow w120 12 (by decide +kernel)
private def w144 : RowWindow checkAt 144 := nextWindow w132 12 (by decide +kernel)
private def w156 : RowWindow checkAt 156 := nextWindow w144 12 (by decide +kernel)
private def w168 : RowWindow checkAt 168 := nextWindow w156 12 (by decide +kernel)
private def w180 : RowWindow checkAt 180 := nextWindow w168 12 (by decide +kernel)
private def w192 : RowWindow checkAt 192 := nextWindow w180 12 (by decide +kernel)
private def w204 : RowWindow checkAt 204 := nextWindow w192 12 (by decide +kernel)
private def w216 : RowWindow checkAt 216 := nextWindow w204 12 (by decide +kernel)
private def w228 : RowWindow checkAt 228 := nextWindow w216 12 (by decide +kernel)
private def w240 : RowWindow checkAt 240 := nextWindow w228 12 (by decide +kernel)
private def w252 : RowWindow checkAt 252 := nextWindow w240 12 (by decide +kernel)

theorem spans : CriticalTensor.Spans 6 6 7 15 := by
  apply from_bits (g:=1) (q:=1) (s:=15) (d:=6) (eLen:=7) (a:=6) points multiplier
  intro q
  have h := w252.verified q.val q.isLt
  have he : Fin.ofNat 252 q.val=q := Fin.ext (Nat.mod_eq_of_lt q.isLt)
  simpa only [checkAt,he] using h

end Six

theorem base_six : CriticalTensor.Spans 6 6 7 15 := Six.spans

namespace Seven

private def points : Array ℕ := #[
    0x1, 0x1, 0x1, 0x2, 0x2, 0x2, 0x4, 0x4, 0x4,
    0x8, 0x8, 0x8, 0x10, 0x10, 0x10, 0x20, 0x20, 0x20,
    0x40, 0x40, 0x1c, 0x53, 0x80, 0x24, 0x15, 0x5a, 0x21,
    0xf, 0xa0, 0x36, 0x6, 0x20, 0x11, 0x6b, 0x86, 0x28,
    0x41, 0x44, 0x1f, 0x64, 0xd7, 0xc, 0x76, 0x3f, 0x35,
    0x2c, 0x6d, 0x1, 0x5f, 0xf2, 0x2b, 0x57, 0x5, 0x1b]
private def unpack := unpack16 21

private def t0 : Array ℕ := #[
    unpack 0x87e2815c14c3872070158727d5aa0807d59759aa0701c54a3683, unpack 0xfd64083cac9b22e6d30f5a46640440678, unpack 0x1c001ca1078824382247301fea9aaa85aa20cce0047c0, unpack 0xec04f4395d524a0ec0cc07fcab47d0134e0403e00,
    unpack 0x3800384a0f541603983041cea8d099815f000, 0, (0x4000298c0023 <<< 288), unpack 0x100dea20ba1d8584f08560801d,
    0, unpack 0x1809fed806838480f2a3025740, unpack 0xc04f4305e92120f30ce80641e41ba00, unpack 0x220176074ac9203844407000,
    (0x40101801 <<< 247), (0x804478019 <<< 295), unpack 0xe6c5921070580e0891d2ac85a52401e10ec555d5b9, unpack 0x806f4381e95924078362132900bc8]
private def t1 : Array ℕ := #[
    0, unpack 0x2201701c0e000f200, unpack 0x3f590a0fa48483878473ab379000, (0x2a01a8028008092001117 <<< 254),
    (0x13012032f <<< 302), unpack 0xa402e4511d551b22e803a2a, unpack 0x1d809e002baaa48b9b01a3ab0, unpack 0x3a01bd1a0fa49603860c70510e340a80,
    unpack 0x520172840eac3b0848e0a21d1745400, unpack 0xa402e4511d51a2a000, (0x260240e4821012c0041 <<< 261), (0x43 <<< 309),
    unpack 0x721181e920a0e1013ce92d4306a62, unpack 0xc04f5085d52420e0c03ca8dd4a06e30, unpack 0x806f5393e95d2b0641e546ea51880, unpack 0x1100b80e0700c400]
private def t2 : Array ℕ := #[
    unpack 0xa402e1217e921a0e1013cee2000, unpack 0x900de810bd3b0f10000, (0x4c04b <<< 316), unpack 0x85d0e47a5140386a4713017327ee588f0034,
    unpack 0x3013c5217a61b54103c0073b1c87a918e360, unpack 0x54027a249eab24870f01eae83e64d0421fd54d00, unpack 0xec04fe88283c031408720823800, unpack 0x4404f0181e96520e1e91d0c71c000,
    0, (0x1d01 <<< 323), unpack 0x1445f436cc352e8300ecc, unpack 0x14805ca203b5d8720f3ab0001c0e0,
    unpack 0x900de262b9d59833a6843b00, unpack 0x1500dea70b806838024f3a680d03800, unpack 0x4806f0187e959240734ecc000, (0x201aa704100087 <<< 278)]
private def t3 : Array ℕ := #[
    0, unpack 0x300b95607a610249e8092e7dbfa61e9f8c, unpack 0x1805ca80b91203db34011733003fd30f000e0, unpack 0x15005ca10bd2c261c3c038a283804c7f878401e957d00,
    unpack 0x3b00b9545756a18720f04487358800, unpack 0x740378089f4ad968382c4000, (0xe002228000007 <<< 284), (0x3 <<< 332),
    0, unpack 0x900de270fd34ae4d91740190, unpack 0x3900bc3b5490838580722e854e80, unpack 0x1c95057a48283d032a375291017a6600,
    unpack 0x220172108ed5729104a07000, (0x2a01a852410809040113411 <<< 246), (0x29008040021 <<< 294), unpack 0x2b013c4e1fa5518284f4411737d4a00fe807a]
private def t4 : Array ℕ := #[
    unpack 0x28591e5fa564321c2c07a220ba13f43083fb48c720, 0, unpack 0x50b2182ea901870d01e546f7ad800, unpack 0x2900b85c4753b342fa000,
    unpack 0x1d809fd5a0000, (0x1101 <<< 322), unpack 0xac02e4407e904a0e1e11d68cea672024, unpack 0x1c809e880bb5d848474050f001ce956a47c9c4f90,
    unpack 0xc02e5203e95a21613c1047cdf43803fae27c80, unpack 0x1001bd1257a5750c3907822439a4604ffcc00, (0x2b0080e0c10810640302400021ac5 <<< 222), (0x3b0080d081080321 <<< 274),
    (0x10001 <<< 318), unpack 0x3013d48570a20e0a41c14079d148025, unpack 0x3a01bd4a5f0e00fadc32a3001ce9574d23130de8, unpack 0x1809e860bd24141c14279d4615211407b40]
private def t5 : Array ℕ := #[
    unpack 0x806f4015c388392c070908e449745da00, (0x45 <<< 201), (0x2011405071012c0018201 <<< 249), 0,
    unpack 0x2a01bd4607541283822472a4a09454, unpack 0x721117e9582c070b48e7564a09860, unpack 0x1100b80617541283862073a6a51500, unpack 0x1d809e872baa4901c29239d352af41ea00,
    unpack 0x39db74ac9283878073a84f5000, (0x1005041 <<< 253), 0, (0x1d00d421 <<< 307),
    unpack 0x1201bd461f420000, 0, unpack 0xac04f1181e900a8600, unpack 0x1201bd4e1fa7534193000]
private def t6 : Array ℕ := #[
    unpack 0xe806f4211c0908e68000, (0x43041 <<< 292), (0xe00000090420250009 <<< 264), (0x1008250c1000840025 <<< 262),
    0, unpack 0x220177674805200, unpack 0x1ce9ba750908e0d000, unpack 0x3900b80c57a564a01d48000,
    (0x40201 <<< 312), unpack 0x70007090de6841c964382a474a8fa2402eaca43b140461c, unpack 0x3b013d0047a486438304722e800388, unpack 0x142c2723aa4861c3507951b9bf652402ea8023380,
    unpack 0xec04f0113c4141c2d03a55a1bf400d3800, unpack 0xe000e1197e954740ca8c0073ee3000, (0x40201c2042005a000493 <<< 252), (0x1008843 <<< 306)]
private def t7 : Array ℕ := #[
    unpack 0x1facad23d24301ed0000, unpack 0x2900b9401fa75d8eac000, unpack 0xe000e0597e92180e69d581280, unpack 0xec04f1487c4a41cc19d259400,
    unpack 0x3013c585f5412838484f3a37db000, unpack 0x560278181e010670000, (0x1c80443021 <<< 299), unpack 0xe402e5201f4deab0e00e75642bd06128ab5,
    unpack 0x3b013d0a0f0428e4b01ee9914268548c068, unpack 0x76027a989e0851c9203d432284d0a9199140, unpack 0x1d00de2403d20420412e00, unpack 0x50b0043ea6e9d82a07220039c5000,
    unpack 0x390181e1a28000, 0, 0, unpack 0x1fac232fd2a8c15279d77d68b005b3]
private def t8 : Array ℕ := #[
    unpack 0x806f1115d5a461a81c0541c023bfb2ac100fd2310ec5011876e3, unpack 0x56027a1cee6841c10c383a4f4ab43694aca6a1d8049701187008ce, unpack 0x7eb0980ea82d870209e55eca4205c05801c2300e, unpack 0x39200de6801c12838724f220039c1c21c900babd2c8762808d3f2,
    0, unpack 0x56027a943ea905070608e000e72310752314801ca4, unpack 0xac04f1293d0dc30d0320c58, unpack 0x4037a343eaba0603ceac856080e8,
    unpack 0x201bc0e47569d868472a34265741d23130da8, unpack 0x3b013c0057540d01a21b0, unpack 0x28595a1f5613400070070, unpack 0xac04f1207e95904870b09e8882e0039fd0c20fed237ae7d0,
    unpack 0x1d809e8c2bd2b541c0395008560, unpack 0x76027a382f482c070209e44ea606800e0, unpack 0x4806f0217d50580e0a91d100b0ee6d501453864c0, unpack 0x4c04f0393e95ed30940f50c02c38a4d761601c0]
private def t9 : Array ℕ := #[
    unpack 0x3013c0e4f421a1be1073aa3008aeac2bd41453aae40, unpack 0xfd65183e95ed30058e1a8504c880, unpack 0x9809e0727d2bda61a81ea1bab02e980, unpack 0x75328c1e2110e1e03c1443ba3001cfe8710ff4145388300,
    unpack 0x1093e92180e1811d19768a61a09bb300, unpack 0x806f5005c4821c1d27d43a032eefb8203cad800700, unpack 0x2900bbb4ac160382a470510e00508e00, unpack 0x1d809e2f0bd2b5244130170e00e00,
    unpack 0x1c001e19d2b0580e0291c1443a20100ffa00, 0, unpack 0xec04f1785e9580b400, unpack 0x6027a848e0580e0891c1443c4097245800,
    unpack 0x3f581217a4160382a470510e00e03800, unpack 0x15809e8723aa4141e81a804b9a800, unpack 0x380038445754940384847041ce351000, unpack 0x14805c242fd3a9a29000]
private def t10 : Array ℕ := #[
    unpack 0x1c001c222baa4a01c242791106000, unpack 0x72032000, 0, unpack 0x560170b0ae4030e1a81d0c69c000,
    unpack 0xe402e1295d52500e1213d30c000, unpack 0xec04f1391e941a0e1803dfcc000, unpack 0xa402e1091e9582d07986a8000, unpack 0xd86a92187060df68000,
    (0x60254210200109001a3 <<< 257), (0x1d8091010004048601f <<< 263), unpack 0x361aa4861f50000, 0,
    unpack 0x201bc4c474a0000, (0x1d80942820801 <<< 287), (0x201a200c10f <<< 290), (0x4000218b05 <<< 296)]
private def t11 : Array ℕ := #[
    (0x98095193 <<< 303), (0xe806899 <<< 308), (0x100009 <<< 314), (0xec01 <<< 320),
    0, (0x1 <<< 335), unpack 0x740378189ea82c070548e00b0eeaa523321498, unpack 0x1fac232bd2bda61291c440021,
    unpack 0x1cc1b2a1e93c1073a2012dd55769d23130c50, unpack 0x14805ca50bd2bda61281c43603444646, unpack 0x520172848f4af6980a473ab44a860ba652, unpack 0x5400708c3e2500e0291d1025cd0180f0004,
    unpack 0x1c805c1a48603832074a4a09760, 0, unpack 0x3a01bd0817a76184a070d5615236b3540, unpack 0x60278a02e05a0e0093caba34b4802d]
private def t12 : Array ℕ := #[
    unpack 0x392183f4ac928381a07005870016e540861e500, unpack 0x8805e05d24a01c1123910098e0347463a, unpack 0xc04f4701e92500f4cc8ba3002c00e6a, unpack 0x15809e252bd3d0c352383a4b993f52843800,
    unpack 0x6027a380f492807640461dd4a56521d8a94, (0x1 <<< 95), unpack 0x1100b9425fa7564210c80, (0x7201 <<< 321),
    unpack 0xe000ec0e95d3b0a08e74d01907d400, (0x1d809 <<< 319), unpack 0x74037fb60150c00, unpack 0x1c801c8723d24a21c2123a8243bbee5007f400,
    (0x44022083002005200a41 <<< 256), unpack 0xe275613d5441927aa003b9bf7f9800, unpack 0x100dea223aa4a01d9041ce25d69199088, unpack 0x3b013c481f2e188414cc0]
private def t13 : Array ℕ := #[
    unpack 0xe402e5393c4141c3907802c3800b74ab523130c10, unpack 0x28580c1f025238880002a70, unpack 0x74037a8caf4ac160383a070058774654305430, 0,
    unpack 0x3f584e4fa5748024f4ab008460, unpack 0x3f58484fa512038504f005873a9800, unpack 0x1d00de800b81291c350800, (0x20100c005 <<< 297),
    (0x60250e10700009 <<< 277), unpack 0x38003b8b28d917401d0, unpack 0x1aad3b02a1805a, (0x13 <<< 330),
    unpack 0x3b013c4607a7598674000, unpack 0x3a991c17b960508ed4000, (0x220100e10015 <<< 289), (0x1d00d11 <<< 311)]
private def t14 : Array ℕ := #[
    (0x20114e11 <<< 301), unpack 0x1a1a03444636, unpack 0x76027a802e5a75600ba64a, (0x1 <<< 331),
    0, unpack 0x390ac1f4ac9483d03220039d2ad48c6a0, unpack 0x720293cb8688d4219340, unpack 0x64702423d4300b0e8c2a4d7772c0,
    (0x158094106004049001a89 <<< 255), unpack 0x50b01c0e3230000, unpack 0x6027a14af4ec3a8750c2a19680, unpack 0x389d560fa564901c31238288700500,
    unpack 0x3900c8e8661a2e82100, unpack 0x500172248ed461613ea1c019747e1f34b500, unpack 0xfd70ed5a86c6c10738000, unpack 0x1c94257a564a01c21000]
private def t15 : Array ℕ := #[
    unpack 0x1d00de2103aa0a41c29079d316000, unpack 0x6027a001ead43086c0680, unpack 0xe40723ab4d9b3ab4402d0, unpack 0xc02e4687e98761091d1023c000,
    unpack 0x3013d42573ab0908e94000, (0x1201aa7000001 <<< 286), (0xec0489c8002024000b41301f <<< 240), unpack 0x900de230bd20261c3d07951a2d54bba40,
    unpack 0x7eb0843e742423808c3804c7f408d3e83dc600, 0, unpack 0x26027a90bea82587a06546ea52402eaa6180, unpack 0xec04f1005c8861c3523a18c3a3ea2187a402e0861c900,
    unpack 0x5201701c1f490987a86946e8fd94a8118700, unpack 0x900dea22fd2b6030e1c11d0901dd525d300, unpack 0x1c90a5f6ac868a4600, unpack 0xac04f4197e97561203ce8c000]
private def t16 : Array ℕ := #[
    unpack 0x201bd445f6ab0a48e7466a15800, unpack 0x1809ea32fd3b4c00032, unpack 0x2b013c4a4f10d073067496a18350, unpack 0x3b00b8161f6a1211df6c000,
    0, unpack 0xa402f62e95829070d01ef4000, unpack 0x2a01bd08475364901c142391426000, unpack 0xfd64103d5da60000,
    (0x140000190081 <<< 291), unpack 0x1c001ca307d2bda668680d110, unpack 0x7eb0903f4ac12839832a4a0160070, unpack 0x10b894aea92507051125c000,
    unpack 0x3900b9405fa564901c1827952504a0, unpack 0x24037a88bf4ac92c3838473af792d00, 0, unpack 0x1809e032b9205704a0e1611c0161c007395d0748cca51568b]
private def t17 : Array ℕ := #[
    unpack 0xe000e0187c00ab8d041ce000909, unpack 0x602780cae4815c1283ca00b0e84cae83a46251569b, unpack 0x5383c90ab90d070248e00b0e84d2ac1194a42b6a3, unpack 0x1201bc4217a550f48e0839c6ab0a91b59aa29315,
    unpack 0xd070d01e54053332c8, 0, unpack 0xa1770e9d86688c20108, unpack 0x380039061fa564a41e8191001ce956a46261be58,
    unpack 0x26027884bf4eac80299948, unpack 0x3900bb03a564901c54c9c2ad348c4c367ed8, unpack 0x520170908f4ac90c385a4f01487008efea130403e6821e5580667c40, unpack 0x1fac0323d2ba761211cea1343ad23559d40,
    0, unpack 0xe402e5115d52420e041bfd1ba4c32ae9a46a91607f40, unpack 0x13013c0c4fa615838472a682a080, unpack 0x909f4c3b0540e0839dd59938572af6982187940a0b80]
private def t18 : Array ℕ := #[
    unpack 0x720170288f4ed30f41e9460131fd0234e4409c00, unpack 0x3013d465fa7698343400, unpack 0x142c822fb564214400, 0,
    unpack 0x724297dab206400, unpack 0x2b013d5a0fa4128384a0f2a4a4501c00, unpack 0x2a19d5c2000, unpack 0x1100bb03a564a41c2407951ca000,
    unpack 0x285dc3a7619a52000, unpack 0x341c2407951da000, 0, unpack 0xa1770e920a0e1a13caea000,
    (0x1008a3281081a091 <<< 270), unpack 0x390181eb7d0000, (0xa804a84300002801 <<< 272), unpack 0x4037abcbe8160000]
private def t19 : Array ℕ := #[
    0, (0x1500956000040195 <<< 275), (0x1 <<< 324), (0x741 <<< 325),
    (0x381 <<< 326), (0x89 <<< 327), (0xe1 <<< 328), (0x71 <<< 329),
    unpack 0xfd60513c8b41e61a1243bbed25a520, unpack 0xec04f5601d52530e0611d1005d09fa9201fc1d23b4d4b4, unpack 0x260278b02eac2b04001ce8321f4d231facf4, unpack 0x540378241f4ac14c38184750497001cfea1107523b4d4d4,
    unpack 0x1fac282fd2b2190e1603d1105d09fa1841fda47d6cd4e4, 0, unpack 0x142ca70b8868387a4f2a3747eca4805c00, (0x5001 <<< 293)]
private def t20 : Array ℕ := #[
    unpack 0x1500dea52fa163622000, (0x540351 <<< 313), unpack 0x1d809ea323a1b8600029, 0,
    unpack 0x3013d1257221070148ea4000, unpack 0xa406f0781e95d3b0c48e2820ee6de800, unpack 0xb274183e95929070509ea0a0eea0c07800, unpack 0x2c9d060fa564a41c04278024b80014,
    unpack 0x1c80de292fd3aac2d23aa0c3b9b620073900, 0, unpack 0x100dea007d2c161c09278324b804e74ab523e4e260, unpack 0x1c809e8103d2a8c3427a220bbd4a00fe9e80,
    unpack 0x806fe0e92420f52d1163c007391883a918e060, unpack 0x3b00b81e4f4369d5800a0, 0, 0]
private def t21 : Array ℕ := #[
    unpack 0x50b084bea924070248e3a000, unpack 0x150a08e74642b0400, (0x18091 <<< 315), unpack 0xc04ff6ca488a400,
    (0x1201a27 <<< 310), 0, (0xc04a8073 <<< 300), 0,
    unpack 0x1201bd4457a7560695686d2e8307474, unpack 0x721181e920a0f00ce9a9741803d, unpack 0xc04f5217d52500e1281c352e8301082, unpack 0x9809e050bb5d81a073a4a5652618a0a,
    unpack 0xa806f1103e9443d239177d000, (0x40000181 <<< 304), 0, (0xa806814904202580050805 <<< 248)]
private def t22 : Array ℕ := #[
    (0x76025 <<< 317), unpack 0x22017d36a82c070548e00b0ee855a80, unpack 0x4402f0d20361e90000, unpack 0x1d809fd0d0000,
    (0x1 <<< 334), (0x70000041 <<< 305), 0, unpack 0x1c805c862bb55d4b0000,
    0, unpack 0x1d809fd01a000, unpack 0x56027a04bf4eac84282600, (0x48068009042025800c40051 <<< 244),
    unpack 0x3a01bd0c5fa7564019440, unpack 0xa806f5385c0948e02a00, (0x80680cb0020209 <<< 276), unpack 0x540378b0aea760000]
private def t23 : Array ℕ := #[
    0, 0, (0x3a01a24001 <<< 298), unpack 0x2b013d0e47548283d032a3752800,
    (0x5 <<< 333), 0, unpack 0x4e173b74c1073805877558548c0a8, (0x220114a082001 <<< 285),
    unpack 0x2b013c424fa7504ba8084, unpack 0x2201701c2e01a0e0611c107380587755000]

private def tables := #[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23]
private def multiplier (j : ℕ) := ((tables[j/16]?.getD #[])[j%16]?).getD 0

private def checkAt (q : ℕ) : Bool :=
  let p := (rowOrder 7 8 6).symm (Fin.ofNat 336 q)
  fit (fastProduct 1 1 18 7 8 6 points multiplier p.1.val p.2.1.val p.2.2.val) q

private def w12 : RowWindow checkAt 12 := nextWindow (start checkAt) 12 (by decide +kernel)
private def w24 : RowWindow checkAt 24 := nextWindow w12 12 (by decide +kernel)
private def w36 : RowWindow checkAt 36 := nextWindow w24 12 (by decide +kernel)
private def w48 : RowWindow checkAt 48 := nextWindow w36 12 (by decide +kernel)
private def w60 : RowWindow checkAt 60 := nextWindow w48 12 (by decide +kernel)
private def w72 : RowWindow checkAt 72 := nextWindow w60 12 (by decide +kernel)
private def w84 : RowWindow checkAt 84 := nextWindow w72 12 (by decide +kernel)
private def w96 : RowWindow checkAt 96 := nextWindow w84 12 (by decide +kernel)
private def w108 : RowWindow checkAt 108 := nextWindow w96 12 (by decide +kernel)
private def w120 : RowWindow checkAt 120 := nextWindow w108 12 (by decide +kernel)
private def w132 : RowWindow checkAt 132 := nextWindow w120 12 (by decide +kernel)
private def w144 : RowWindow checkAt 144 := nextWindow w132 12 (by decide +kernel)
private def w156 : RowWindow checkAt 156 := nextWindow w144 12 (by decide +kernel)
private def w168 : RowWindow checkAt 168 := nextWindow w156 12 (by decide +kernel)
private def w180 : RowWindow checkAt 180 := nextWindow w168 12 (by decide +kernel)
private def w192 : RowWindow checkAt 192 := nextWindow w180 12 (by decide +kernel)
private def w204 : RowWindow checkAt 204 := nextWindow w192 12 (by decide +kernel)
private def w216 : RowWindow checkAt 216 := nextWindow w204 12 (by decide +kernel)
private def w228 : RowWindow checkAt 228 := nextWindow w216 12 (by decide +kernel)
private def w240 : RowWindow checkAt 240 := nextWindow w228 12 (by decide +kernel)
private def w252 : RowWindow checkAt 252 := nextWindow w240 12 (by decide +kernel)
private def w264 : RowWindow checkAt 264 := nextWindow w252 12 (by decide +kernel)
private def w276 : RowWindow checkAt 276 := nextWindow w264 12 (by decide +kernel)
private def w288 : RowWindow checkAt 288 := nextWindow w276 12 (by decide +kernel)
private def w300 : RowWindow checkAt 300 := nextWindow w288 12 (by decide +kernel)
private def w312 : RowWindow checkAt 312 := nextWindow w300 12 (by decide +kernel)
private def w324 : RowWindow checkAt 324 := nextWindow w312 12 (by decide +kernel)
private def w336 : RowWindow checkAt 336 := nextWindow w324 12 (by decide +kernel)

theorem spans : CriticalTensor.Spans 6 7 8 18 := by
  apply from_bits (g:=1) (q:=1) (s:=18) (d:=7) (eLen:=8) (a:=6) points multiplier
  intro q
  have h := w336.verified q.val q.isLt
  have he : Fin.ofNat 336 q.val=q := Fin.ext (Nat.mod_eq_of_lt q.isLt)
  simpa only [checkAt,he] using h

end Seven

theorem base_seven : CriticalTensor.Spans 6 7 8 18 := Seven.spans

end CriticalTensor.ConsecutiveSixBase

namespace CriticalTensor.SixConsecutiveBorder

/-- The two-face condition with the factors fixed and the two base axes allowed to differ. -/
def Holds {D E N : Type} [Fintype N] (X : Fin 6 → Fin 6 → ℂ)
    (Y : Fin 6 → (Fin 2 ⊕ D) → ℂ) (Z : Fin 6 → (Fin 2 ⊕ E) → ℂ)
    (x : N → Fin 6 → ℂ) (y : N → D → ℂ) (z : N → E → ℂ) : Prop :=
  ∀ T : Fin 6 → (Fin 2 ⊕ D) → (Fin 2 ⊕ E) → ℂ,
    ∃ U : Fin 6 → Fin 6 → ℂ, ∃ V : Fin 6 → (Fin 2 ⊕ D) → ℂ, ∃ W : Fin 6 → (Fin 2 ⊕ E) → ℂ,
    ∃ v w : N → Fin 2 → ℂ, ∀ i j k, (j.isLeft=true ∨ k.isLeft=true) →
      T i j k = (∑ t, (U t i*(Y t j*Z t k)+X t i*(V t j*Z t k)+X t i*(Y t j*W t k))) +
        ∑ t, (x t i*(j.elim (v t) (fun _ => 0)*k.elim (fun _ => 0) (z t)) +
          x t i*(j.elim (fun _ => 0) (y t)*k.elim (w t) (fun _ => 0)))

def Witness (D E N : Type) [Fintype N] : Prop :=
  ∃ X : Fin 6 → Fin 6 → ℂ, ∃ Y : Fin 6 → (Fin 2 ⊕ D) → ℂ, ∃ Z : Fin 6 → (Fin 2 ⊕ E) → ℂ,
    ∃ x : N → Fin 6 → ℂ, ∃ y : N → D → ℂ, ∃ z : N → E → ℂ, Holds X Y Z x y z

/-- On each new interior coordinate the remaining rows form one 6-by-2 rectangle. -/
def Wing (O : Fin 6 → Fin 2 → ℂ) (X : Fin 6 → Fin 6 → ℂ) (pair : Fin 3 → Fin 6 → ℂ) : Prop :=
  ∀ T : Fin 6 → Fin 2 → ℂ, ∃ p : Fin 6 → ℂ, ∃ v : Fin 3 → Fin 2 → ℂ, ∀ i j,
    T i j = (∑ t, X t i*(p t*O t j)) + ∑ t, pair t i*v t j

private def join {D L : Type} (old : Fin 2 ⊕ D → ℂ) (new : L → ℂ) : Fin 2 ⊕ (D ⊕ L) → ℂ :=
  Sum.elim (fun j => old (.inl j)) (Sum.elim (fun j => old (.inr j)) new)

private def embed {D L : Type} : Fin 2 ⊕ D → Fin 2 ⊕ (D ⊕ L) := Sum.map id Sum.inl

/-- Add one copy of a pair of narrow faces for each new coordinate; padding labels carry zero factors. -/
lemma extend {D E N : Type} [Fintype N] (X : Fin 6 → Fin 6 → ℂ)
    (Y : Fin 6 → (Fin 2 ⊕ D) → ℂ) (Z : Fin 6 → (Fin 2 ⊕ E) → ℂ)
    (x : N → Fin 6 → ℂ) (y : N → D → ℂ) (z : N → E → ℂ) (base : Holds X Y Z x y z)
    (pair : Fin 3 → Fin 6 → ℂ) (left : Wing (fun t j => Z t (.inl j)) X pair)
    (right : Wing (fun t j => Y t (.inl j)) X pair) (L Q : Type) [Fintype L] [DecidableEq L] [Fintype Q] :
    Witness (D ⊕ L) (E ⊕ L) (N ⊕ ((L × Fin 3) ⊕ Q)) := by
  classical
  let unit (p l : L) : ℂ := if p=l then 1 else 0
  refine ⟨X,fun t => join (Y t) 0,fun t => join (Z t) 0,
    Sum.elim x (Sum.elim (fun p => pair p.2) 0),
    Sum.elim (fun t => Sum.elim (y t) 0) (Sum.elim (fun p => Sum.elim 0 (unit p.1)) 0),
    Sum.elim (fun t => Sum.elim (z t) 0) (Sum.elim (fun p => Sum.elim 0 (unit p.1)) 0),?_⟩
  intro T
  obtain ⟨U,V,W,v,w,core⟩ := base fun i j k => T i (embed j) (embed k)
  choose p vL hl using fun l : L => left (fun i k => T i (.inr (.inr l)) (.inl k))
  choose q vR hr using fun l : L => right (fun i j => T i (.inl j) (.inr (.inr l)))
  refine ⟨U,fun t => join (V t) (fun l => p l t),fun t => join (W t) (fun l => q l t),
    Sum.elim v (Sum.elim (fun g => vR g.1 g.2) 0), Sum.elim w (Sum.elim (fun g => vL g.1 g.2) 0),?_⟩
  rintro i (j|j|l) (k|k|g) he
  · simpa [join,embed,Fintype.sum_sum_type] using core i (.inl j) (.inl k) (Or.inl rfl)
  · simpa [join,embed,Fintype.sum_sum_type] using core i (.inl j) (.inr k) (Or.inl rfl)
  · simpa [join,unit,Fintype.sum_sum_type,Fintype.sum_prod_type,ite_mul,mul_ite,Finset.sum_ite_irrel,
      mul_comm,mul_left_comm,mul_assoc] using hr g i j
  · simpa [join,embed,Fintype.sum_sum_type] using core i (.inr j) (.inl k) (Or.inr rfl)
  · simp at he
  · simp at he
  · simpa [join,unit,Fintype.sum_sum_type,Fintype.sum_prod_type,ite_mul,mul_ite,Finset.sum_ite_irrel,
      mul_comm,mul_left_comm,mul_assoc] using hl l i k
  · simp at he
  · simp at he

lemma to_rect {D E N : Type} [Fintype N] {d e r : ℕ} (ed : Fin d ≃ D) (ee : Fin e ≃ E)
    (en : Fin r ≃ N) (hs : Witness D E N) : RectBorder 6 d e 2 r 6 := by
  classical
  obtain ⟨X,Y,Z,x,y,z,hs⟩ := hs
  let jd := Equiv.sumCongr (Equiv.refl (Fin 2)) ed
  let ke := Equiv.sumCongr (Equiv.refl (Fin 2)) ee
  refine ⟨X,fun t j => Y t (jd j),fun t k => Z t (ke k),fun t => x (en t),fun t j => y (en t) (ed j),
    fun t k => z (en t) (ee k),?_⟩
  intro T
  obtain ⟨U,V,W,v,w,hu⟩ := hs (fun i j k => T i (jd.symm j) (ke.symm k))
  refine ⟨U,fun t j => V t (jd j),fun t k => W t (ke k),fun t => v (en t),fun t => w (en t),?_⟩
  intro i j k he
  have edge : (jd j).isLeft=true ∨ (ke k).isLeft=true := by cases j <;> cases k <;> exact he
  have h := hu i (jd j) (ke k) edge
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply] at h
  rw [h]
  congr 1
  let term (t : N) := x t i*((jd j).elim (v t) (fun _ => 0)*(ke k).elim (fun _ => 0) (z t)) +
    x t i*((jd j).elim (fun _ => 0) (y t)*(ke k).elim (w t) (fun _ => 0))
  change (∑ t, term t) = _
  rw [← en.sum_comp term]
  apply Finset.sum_congr rfl
  intro t _
  cases j <;> cases k <;> rfl

end CriticalTensor.SixConsecutiveBorder

namespace CriticalTensor.SixConsecutiveBorder

open CriticalTensor.ConsecutiveBorder

lemma holds_of_rank {d e r : ℕ} (X : Fin 6 → Fin 6 → ℤ) (Y : Fin 6 → Side d → ℤ)
    (Z : Fin 6 → Side e → ℤ) (x : Fin r → Fin 6 → ℤ) (y : Fin r → Fin d → ℤ) (z : Fin r → Fin e → ℤ)
    (hs : Function.Surjective ((matrix X Y Z x y z).map (Int.castRingHom ℂ)).mulVec) :
    Holds (fun t i => (X t i : ℂ)) (fun t j => (Y t j : ℂ)) (fun t k => (Z t k : ℂ))
      (fun t i => (x t i : ℂ)) (fun t j => (y t j : ℂ)) (fun t k => (z t k : ℂ)) := by
  classical
  rw [cast_matrix] at hs
  intro T
  obtain ⟨v,hv⟩ := hs fun row => T (coords row).2.2 (coords row).1 (coords row).2.1
  refine ⟨fun t i => v (.inl (t,.inr (.inr i))),fun t j => v (.inl (t,.inl j)),
    fun t k => v (.inl (t,.inr (.inl k))),fun t h => v (.inr (t,.inl h)),fun t h => v (.inr (t,.inr h)),?_⟩
  intro i j k hij
  obtain ⟨u,hu⟩ : ∃ u : Rows 6 d e,coords u=(j,k,i) := by
    rcases j with j|j
    · exact ⟨.inl (j,k,i),rfl⟩
    · rcases k with k|k
      · exact ⟨.inr (j,k,i),rfl⟩
      · simp at hij
  have hh := (congrFun hv u).symm
  simp only [hu] at hh
  rw [hh]
  change (∑ q : Cols 6 d e r, matrix (fun t i => (X t i : ℂ)) (fun t j => (Y t j : ℂ))
    (fun t k => (Z t k : ℂ)) (fun t i => (x t i : ℂ)) (fun t j => (y t j : ℂ)) (fun t k => (z t k : ℂ))
    u q*v q) = _
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    rcases j with j|j <;> rcases k with k|k <;>
      simp [matrix,hu,ite_mul,Fintype.sum_sum_type,Finset.sum_ite_eq'] <;> ring
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type]
    rcases j with j|j <;> rcases k with k|k <;> simp [matrix,hu,ite_mul,Finset.sum_ite_eq'] <;> ring

end CriticalTensor.SixConsecutiveBorder

namespace CriticalTensor.SixConsecutiveBorder

open CriticalTensor.ConsecutiveBorder

def wingMatrix (O : Fin 6 → Fin 2 → ℤ) (X : Fin 6 → Fin 6 → ℤ) (pair : Fin 3 → Fin 6 → ℤ) :
    Matrix (Fin 6 × Fin 2) ((Fin 6) ⊕ (Fin 3 × Fin 2)) ℤ
  | (i,j),.inl t => X t i * O t j
  | (i,j),.inr (t,k) => if k=j then pair t i else 0

private lemma wing_of_rank (O : Fin 6 → Fin 2 → ℤ) (X : Fin 6 → Fin 6 → ℤ) (pair : Fin 3 → Fin 6 → ℤ)
    (hs : Function.Surjective ((wingMatrix O X pair).map (Int.castRingHom ℂ)).mulVec) :
    Wing (fun t j => (O t j : ℂ)) (fun t i => (X t i : ℂ)) (fun t i => (pair t i : ℂ)) := by
  intro T
  obtain ⟨p,hp⟩ := hs fun ij => T ij.1 ij.2
  refine ⟨fun t => p (.inl t),fun t j => p (.inr (t,j)),?_⟩
  intro i j
  refine (congrFun hp (i,j)).symm.trans ?_
  change (∑ c : Fin 6 ⊕ (Fin 3 × Fin 2), ((wingMatrix O X pair (i,j) c : ℤ):ℂ)*p c) = _
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro l _
    simp only [wingMatrix,Int.cast_mul]
    ring
  · apply Finset.sum_congr rfl
    intro l _
    simp [wingMatrix,apply_ite,ite_mul,Finset.sum_ite_eq']

end CriticalTensor.SixConsecutiveBorder

namespace CriticalTensor.SixConsecutiveBorder

open CriticalTensor.ConsecutiveBorder

def seedX (s : Fin 6) (i : Fin 6) : ℤ := flags #[1,2,4,8,16,32] s i
def seedY (s : Fin 6) (i : Side 2) : ℤ := flags #[2,7,15,13,5,14] s (finSumFinEquiv i)
def seedZ (s : Fin 6) (i : Side 3) : ℤ := flags #[31,1,18,23,14,5] s (finSumFinEquiv i)
def seedx (s : Fin 2) (i : Fin 6) : ℤ := flags #[59,14] s i
def seedy (s : Fin 2) (i : Fin 2) : ℤ := flags #[2,1] s i
def seedz (s : Fin 2) (i : Fin 3) : ℤ := flags #[5,4] s i
def pair (s : Fin 3) (i : Fin 6) : ℤ := flags #[3,12,48] s i

private def M := matrix seedX seedY seedZ seedx seedy seedz
private def coreColumns := packedEntry #[
    0x1000000000000000000000040000000000000000000001000000000000000000000040000000041000000000000000000000041000000000000000000000041041040000000000000000000001041041,
    0x2000000820820800000000000000410410400000000000000208208200000000000000104104100000000000000082082080000000000000041041040000000000000040000000000000,
    0x80000002000000000000002000000080000000000000080000002000000080000002000000080000002000000080000002002000000000000000000000002000000000000000000000000000080000000,
    0x100004000000000000000000000004000100000020000000800000020000010000000400000010000008000000200000008000004000000100000004000002000000080000002000001000000040000001,
    0x40040040001001000040000000100000004000000000000004000000100000000000000100000004000100100000004000000100004004000000100000004100000000000000000000000100000000000000000,
    0x208000000000000000000000200208200000000000000000000008008208800800800020020000800400400400010010000400200200200008008000200100100100004004000100080080080002002000080,
    0x82082000000002002082041041000000001001041000000000000008000000000000000000000200000000000000000000008000200200000000000000200008008000000000000008208000000000000000000,
    0x400000000000000000000000400000000000000000000000010410000000000000000000000000410400820820000000020020820410410000000010010410208208000000008008208104104000000004004104,
    0x100000000000104100000080000000000082080000040000000000041040000000000000010000000000000000000000400000000000000000000010000000400000000000000400000010000000000000010,
    0x20020000000800000000020000000000000000000000020000000000000000000000000800800000000000000000000000020020000800000000000820800000400000000000410400000200000000000208200,
    0x8008000200200000000004004000100100000000002002000080080000000001001000040040000000000000800000000000000000000020000000000000000000000800000000000800800000020000000000,
    0x38000000000000000000000000000e000000ec000000000000000000003b000000000000000000000000ec0ec000000000000000000000003b03b000020020000800800000000010010000400400000000,
    0x38000000000000000000000e000000000000000] 84
private def corePreimages := packedEntry #[
    0x802800500025994040102100000100020000000800100009b0000300000000000080000000c928f156a41b440bc8f624b20020000000027900000000000404000c0010fa02280f10c00000000000000000000002000010104117841d000001040040,
    0x20000000000000400000c0010fa03680f10c0000080000000000000009c000010004117845d0080010400c2050a6258e116ac2008348135c000000024000000000000000002000000003990000000000040000040000fa00040f10400,
    0x9081b5d2216e86000118137c00000006500000000000000000000000000400000000000000000000001000037c000080000000000002000400019e100000000000004000000000000d0000320000000000080000000000000040000000000000000,
    0x4000000000000000000000000001005082258e116a82008348135c000000100000000000000000000000000003e80000000000040000040000fa00000f104000000001000000000003c41000000000200000000001000015,
    0x3000000000010102f0200000040000040000fa00b40f1040000080010002000400014210000000000000000000000000200000380000000000000000000000000010000000010000000000000400007c000020000000400000c0000fa031c0f10c00,
    0x3c0000000000000000000c828f141201b440bd8f624b20000004000053900020000000400000c0010fa02680f10c0000080000000000000001c000000000000000000000000004000021a000200040000000000000000013a000080010002000,
    0x1000000000001c410000000000000000000000000f200001e0002000400000010000c828f152a01b4c0bc8f604b200000000000010000000040000000000001000017c000080000000000002000400009e1000000000000000000000000080,
    0x2000400005b900000000000004000000100001344000000000000000000000000008000010104117841d0000000400500002000000000000000000000000000012000000010002000300000000003e802f0200000040000040000fa00bc0f10400,
    0xc024a05c30044400025000200000000040000000000000000020004000059900000000000000000000000000100000000802000400005990040000000010104117841d0000000400540000080000000000000000000c928f157a41b440bc8f624b2,
    0x4000240000010004117841d00000004000800001000000000000000000000000001784000000000000000000004000074000000000000000000000000000404000000000000000000000000010000010004117841d000000040000,
    0xc001005c10040400025000200000000080000000000000000000004000070000000000000000000000000000200000000] 98
private def coreTest := directCheck M (rows 6 2 3) (cols 6 2 3 2) coreColumns corePreimages
private def coreW4 : RowWindow coreTest 4 := nextWindow (start coreTest) 4 (by decide +kernel)
private def coreW8 : RowWindow coreTest 8 := nextWindow coreW4 4 (by decide +kernel)
private def coreW12 : RowWindow coreTest 12 := nextWindow coreW8 4 (by decide +kernel)
private def coreW16 : RowWindow coreTest 16 := nextWindow coreW12 4 (by decide +kernel)
private def coreW20 : RowWindow coreTest 20 := nextWindow coreW16 4 (by decide +kernel)
private def coreW24 : RowWindow coreTest 24 := nextWindow coreW20 4 (by decide +kernel)
private def coreW28 : RowWindow coreTest 28 := nextWindow coreW24 4 (by decide +kernel)
private def coreW32 : RowWindow coreTest 32 := nextWindow coreW28 4 (by decide +kernel)
private def coreW36 : RowWindow coreTest 36 := nextWindow coreW32 4 (by decide +kernel)
private def coreW40 : RowWindow coreTest 40 := nextWindow coreW36 4 (by decide +kernel)
private def coreW44 : RowWindow coreTest 44 := nextWindow coreW40 4 (by decide +kernel)
private def coreW48 : RowWindow coreTest 48 := nextWindow coreW44 4 (by decide +kernel)
private def coreW52 : RowWindow coreTest 52 := nextWindow coreW48 4 (by decide +kernel)
private def coreW56 : RowWindow coreTest 56 := nextWindow coreW52 4 (by decide +kernel)
private def coreW60 : RowWindow coreTest 60 := nextWindow coreW56 4 (by decide +kernel)
private def coreW64 : RowWindow coreTest 64 := nextWindow coreW60 4 (by decide +kernel)
private def coreW68 : RowWindow coreTest 68 := nextWindow coreW64 4 (by decide +kernel)
private def coreW72 : RowWindow coreTest 72 := nextWindow coreW68 4 (by decide +kernel)
private def coreW76 : RowWindow coreTest 76 := nextWindow coreW72 4 (by decide +kernel)
private def coreW80 : RowWindow coreTest 80 := nextWindow coreW76 4 (by decide +kernel)
private def coreW84 : RowWindow coreTest 84 := nextWindow coreW80 4 (by decide +kernel)

lemma seed : Holds (fun t i => (seedX t i : ℂ)) (fun t j => (seedY t j : ℂ)) (fun t k => (seedZ t k : ℂ))
    (fun t i => (seedx t i : ℂ)) (fun t j => (seedy t j : ℂ)) (fun t k => (seedz t k : ℂ)) :=
  holds_of_rank seedX seedY seedZ seedx seedy seedz (checked M (rows 6 2 3) (cols 6 2 3 2) coreColumns corePreimages coreW84.verified)

private def leftM := wingMatrix (fun t j => seedZ t (.inl j)) seedX pair
private def leftColumns := packedEntry #[
    0xa0054002000c0020004003,
    0xa005000a0050] 12
private def leftPreimages := packedEntry #[
    0x20420c00430c0c3002043042,
    0x810020010420] 12
private def leftTest := directCheck leftM (finProdFinEquiv) (sumFin (Equiv.refl (Fin 6)) finProdFinEquiv) leftColumns leftPreimages
private def leftW4 : RowWindow leftTest 4 := nextWindow (start leftTest) 4 (by decide +kernel)
private def leftW8 : RowWindow leftTest 8 := nextWindow leftW4 4 (by decide +kernel)
private def leftW12 : RowWindow leftTest 12 := nextWindow leftW8 4 (by decide +kernel)

lemma left_wing : Wing (fun t j => (seedZ t (.inl j) : ℂ)) (fun t i => (seedX t i : ℂ)) (fun t i => (pair t i : ℂ)) :=
  wing_of_rank (fun t j => seedZ t (.inl j)) seedX pair (checked leftM (finProdFinEquiv) (sumFin (Equiv.refl (Fin 6)) finProdFinEquiv) leftColumns leftPreimages leftW12.verified)

private def rightM := wingMatrix (fun t j => seedY t (.inl j)) seedX pair
private def rightColumns := packedEntry #[
    0xa00580010004003000c002,
    0xa005000a0050] 12
private def rightPreimages := packedEntry #[
    0x30c00810c1080810830010c3,
    0x20410820010] 12
private def rightTest := directCheck rightM (finProdFinEquiv) (sumFin (Equiv.refl (Fin 6)) finProdFinEquiv) rightColumns rightPreimages
private def rightW4 : RowWindow rightTest 4 := nextWindow (start rightTest) 4 (by decide +kernel)
private def rightW8 : RowWindow rightTest 8 := nextWindow rightW4 4 (by decide +kernel)
private def rightW12 : RowWindow rightTest 12 := nextWindow rightW8 4 (by decide +kernel)

lemma right_wing : Wing (fun t j => (seedY t (.inl j) : ℂ)) (fun t i => (seedX t i : ℂ)) (fun t i => (pair t i : ℂ)) :=
  wing_of_rank (fun t j => seedY t (.inl j)) seedX pair (checked rightM (finProdFinEquiv) (sumFin (Equiv.refl (Fin 6)) finProdFinEquiv) rightColumns rightPreimages rightW12.verified)

end CriticalTensor.SixConsecutiveBorder

namespace CriticalTensor.SixConsecutiveBorder

open CriticalTensor.ConsecutiveBorder

/-- Starting with the 2-by-3 base, each additional interior coordinate on both axes
requires three more old points. Further zero old summands may be adjoined. -/
lemma borders (k padding : ℕ) : RectBorder 6 (2+k) (3+k) 2 (2+(k*3+padding)) 6 := by
  let w := extend (fun t i => (seedX t i : ℂ)) (fun t j => (seedY t j : ℂ)) (fun t j => (seedZ t j : ℂ))
    (fun t i => (seedx t i : ℂ)) (fun t j => (seedy t j : ℂ)) (fun t j => (seedz t j : ℂ)) seed
    (fun t i => (pair t i : ℂ)) left_wing right_wing (Fin k) (Fin padding)
  exact to_rect finSumFinEquiv.symm finSumFinEquiv.symm
    (sumFin (Equiv.refl (Fin 2)) (sumFin finProdFinEquiv (Equiv.refl (Fin padding)))).symm w

lemma border_six : RectBorder 6 6 7 2 15 6 := borders 4 1
lemma border_seven : RectBorder 6 7 8 2 18 6 := borders 5 1
lemma border_twenty : RectBorder 6 20 21 2 56 6 := borders 18 0
lemma border_twenty_one : RectBorder 6 21 22 2 59 6 := borders 19 0

end CriticalTensor.SixConsecutiveBorder

namespace CriticalTensor.SixConsecutive

open Nat

theorem count_before_twenty (m : ℕ) (lo : 6 ≤ m) (hi : m < 20) :
    6*m*(m+1) ⌈/⌉ (2*m+5) = 3*m-3 := by
  interval_cases m <;> decide

theorem count_from_twenty (m : ℕ) (hm : 20 ≤ m) :
    6*m*(m+1) ⌈/⌉ (2*m+5) = 3*m-4 := by
  let r := 6*m*(m+1) ⌈/⌉ (2*m+5)
  have hden : 0 < 2*m+5 := by omega
  have hr : 3*m-4+4=3*m := by omega
  have hsum := congrArg (fun x : ℕ => x*(2*m+5)) hr
  apply le_antisymm
  · apply (ceilDiv_le_iff_le_mul hden).mpr
    nlinarith
  · by_contra! h
    have hpos : r+1 ≤ 3*m-4 := by dsimp [r]; omega
    have hmul := Nat.mul_le_mul_left (2*m+5) hpos
    have hcap : 6*m*(m+1) ≤ (2*m+5)*r := (ceilDiv_le_iff_le_mul hden).mp le_rfl
    nlinarith

end CriticalTensor.SixConsecutive

namespace CriticalTensor.SixConsecutive

private lemma progression {d m base gap : ℕ} (hb : Spans 6 d (d + 1) base)
    (hr : RectBorder 6 d (d + 1) 2 base 6) (hbase : base + gap = 3 * d)
    (hm : d ≤ m) (hmod : m % 2 = d % 2) : Spans 6 m (m + 1) (3 * m - gap) := by
  let t := (m - d) / 2
  have hs : d + 2 * t = m := by dsimp [t]; omega
  have hs' : d + 1 + 2 * t = m + 1 := by omega
  have count : base + 6 * t = 3 * m - gap := by omega
  simpa only [hs,hs',count] using
    grow_rect 6 d (d + 1) 2 base 6 t hb hr (cross_width_two 6 (by decide))

/-- The two small seeds give this bound on every middle side. -/
theorem spans_three_m_minus_three (m : ℕ) (hm : 6 ≤ m) : Spans 6 m (m + 1) (3 * m - 3) := by
  by_cases even : m % 2 = 0
  · exact progression ConsecutiveSixBase.base_six SixConsecutiveBorder.border_six
      (by decide) hm even
  · exact progression ConsecutiveSixBase.base_seven SixConsecutiveBorder.border_seven
      (by decide) (by omega) (by omega)

private lemma catalog_den (m : ℕ) : 6 + m + (m + 1) - 2 = 2 * m + 5 := by omega

/-- The small sides and the whole even progression attain the dimension count. -/
theorem spans_small_or_even (m : ℕ) (hm : 6 ≤ m) (covered : m < 20 ∨ m % 2 = 0) :
    Spans 6 m (m + 1) (6 * m * (m + 1) ⌈/⌉ (6 + m + (m + 1) - 2)) := by
  rw [catalog_den]
  by_cases small : m < 20
  · rw [count_before_twenty m hm small]
    exact spans_three_m_minus_three m hm
  · have large : 20 ≤ m := by omega
    rw [count_from_twenty m large]
    exact progression RectGrid.Twenty.spans SixConsecutiveBorder.border_twenty
      (by decide) large (covered.resolve_left small)

/-- On every remaining odd side a spanning witness uses one extra point. -/
theorem spans_one_extra (m : ℕ) (hm : 21 ≤ m) (_odd : m % 2 = 1) :
    Spans 6 m (m + 1) ((6 * m * (m + 1) ⌈/⌉ (6 + m + (m + 1) - 2)) + 1) := by
  rw [catalog_den, count_from_twenty m (by omega), show 3 * m - 4 + 1 = 3 * m - 3 by omega]
  exact spans_three_m_minus_three m (by omega)

/-- A single 21-by-22 seed at 59 points gives the exact tangent count
for every six-slice consecutive format. -/
theorem spans_of_seed (seed : Spans 6 21 22 59) (m : ℕ) (hm : 6 ≤ m) :
    Spans 6 m (m + 1) (6 * m * (m + 1) ⌈/⌉ (6 + m + (m + 1) - 2)) := by
  by_cases covered : m < 20 ∨ m % 2 = 0
  · exact spans_small_or_even m hm covered
  · push Not at covered
    rw [catalog_den, count_from_twenty m covered.1]
    exact progression seed SixConsecutiveBorder.border_twenty_one (by decide) (by omega) (by omega)

/-- The 21-by-22 seed is equivalent to the whole six-slice tangent family. -/
theorem all_iff_seed :
    (∀ m : ℕ, 6 ≤ m → Spans 6 m (m + 1) (6 * m * (m + 1) ⌈/⌉ (6 + m + (m + 1) - 2))) ↔
      Spans 6 21 22 59 := ⟨fun h => h 21 (by decide),spans_of_seed⟩

end CriticalTensor.SixConsecutive

namespace CriticalTensor.SixConsecutive

open Arxiv.«0805.3777» Set

private lemma rank_interval (m u : ℕ) (hm : 6 ≤ m) (span : Spans 6 m (m + 1) u) :
    ∃ U : Set (Holor ℂ [6,m,m + 1]), IsOpen U ∧ Dense U ∧
      ∀ T ∈ U, (6 * m * (m + 1) ⌈/⌉ (6 + m + (m + 1) - 2)) ≤ T.cprank ∧ T.cprank ≤ u := by
  classical
  let d := 6 + m + (m + 1) - 2
  let r := 6 * m * (m + 1) ⌈/⌉ d
  have hd : 0 < d := by dsimp only [d]; omega
  have hnum : 0 < 6 * m * (m + 1) := Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)
  have hr : 0 < r := by
    by_contra! hz
    have he : 6 * m * (m + 1) ≤ d * 0 := (ceilDiv_le_iff_le_mul hd).mp hz
    rw [Nat.mul_zero] at he
    omega
  have cost : d * (r - 1) < 6 * m * (m + 1) := by
    by_contra! hc
    have hsmall : r ≤ r - 1 := (ceilDiv_le_iff_le_mul hd).mpr hc
    omega
  obtain ⟨U,ho,hu,hupper⟩ := @CriticalReduction.upper_of_witness 6 m (m + 1) u span
  let Z := closure {T : Holor ℂ [6,m,m + 1] | T.cprank ≤ r - 1}
  have lower : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp
    (CriticalReduction.lower_of_count 6 m (m + 1) (r - 1) cost)
  refine ⟨U ∩ Zᶜ,ho.inter isClosed_closure.isOpen_compl,hu.inter_of_isOpen_left lower ho,?_⟩
  intro T ht
  have hlo : ¬ T.cprank ≤ r - 1 := fun h => ht.2 (subset_closure h)
  exact ⟨show r ≤ T.cprank by omega,hupper T ht.1⟩

private theorem generic_of_spans (m : ℕ) (hm : 6 ≤ m)
    (span : Spans 6 m (m + 1) (6 * m * (m + 1) ⌈/⌉ (6 + m + (m + 1) - 2))) :
    IsGenericRank [6,m,m + 1] (6 * m * (m + 1) ⌈/⌉ (6 + m + (m + 1) - 2)) := by
  obtain ⟨U,ho,hd,h⟩ := rank_interval m _ hm span
  exact ⟨U,ho,hd,fun T ht => (h T ht).2.antisymm (h T ht).1⟩

theorem generic_rank_small_or_even (m : ℕ) (hm : 6 ≤ m) (covered : m < 20 ∨ m % 2 = 0) :
    IsGenericRank [6,m,m + 1] (6 * m * (m + 1) ⌈/⌉ (6 + m + (m + 1) - 2)) :=
  generic_of_spans m hm (spans_small_or_even m hm covered)

theorem generic_rank_before_twenty (m : ℕ) (hm : 6 ≤ m) (hi : m < 20) :
    IsGenericRank [6,m,m + 1] (3 * m - 3) := by
  simpa only [catalog_den,count_before_twenty m hm hi] using generic_rank_small_or_even m hm (.inl hi)

theorem generic_rank_even_from_twenty (m : ℕ) (hm : 20 ≤ m) (even : m % 2 = 0) :
    IsGenericRank [6,m,m + 1] (3 * m - 4) := by
  simpa only [catalog_den,count_from_twenty m hm] using generic_rank_small_or_even m (by omega) (.inr even)

/-- On a dense open set of every late odd format, CP rank is one of two consecutive integers. -/
theorem generic_interval_late_odd (m : ℕ) (hm : 21 ≤ m) (_odd : m % 2 = 1) :
    ∃ U : Set (Holor ℂ [6,m,m + 1]), IsOpen U ∧ Dense U ∧
      ∀ T ∈ U, 3 * m - 4 ≤ T.cprank ∧ T.cprank ≤ 3 * m - 3 := by
  simpa only [catalog_den,count_from_twenty m (by omega)] using
    rank_interval m (3 * m - 3) (by omega) (spans_three_m_minus_three m (by omega))

theorem generic_rank_of_seed (seed : Spans 6 21 22 59) (m : ℕ) (hm : 6 ≤ m) :
    IsGenericRank [6,m,m + 1] (6 * m * (m + 1) ⌈/⌉ (6 + m + (m + 1) - 2)) :=
  generic_of_spans m hm (spans_of_seed seed m hm)

end CriticalTensor.SixConsecutive

namespace CriticalTensor.PackedTangent

/-- Concatenate fixed-width copies of a payload at the set bits of a selector. -/
def tile : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,_,_,_ => 0
  | n+1,w,s,v =>
    (if s.testBit 0 then v % 2^w else 0) ||| ((tile n w (s >>> 1) v) <<< w)

lemma tile_bit (n w s v i j : ℕ) (hj : j<w) :
    (tile n w s v).testBit (i*w+j) =
      ((decide (i<n) && s.testBit i) && v.testBit j) := by
  induction n generalizing i s with
  | zero => simp [tile]
  | succ n ih =>
    cases i with
    | zero =>
      simp only [tile,Nat.zero_mul,Nat.zero_add,Nat.testBit_or,Nat.testBit_shiftLeft]
      split <;> simp_all [Nat.testBit_mod_two_pow,show ¬j≥w from Nat.not_le.mpr hj]
    | succ i =>
      have ge : w ≤ (i+1)*w+j := by rw [Nat.succ_mul]; omega
      have sub : (i+1)*w+j-w = i*w+j := by rw [Nat.succ_mul]; omega
      have low : (if s.testBit 0 then v % 2^w else 0).testBit ((i+1)*w+j) = false := by
        split <;> simp [Nat.testBit_mod_two_pow,Nat.not_lt_of_ge ge]
      simp only [tile,Nat.testBit_or,low,Nat.testBit_shiftLeft,decide_eq_true_iff.mpr ge,Bool.true_and,
        Bool.false_or,sub,ih (s >>> 1) i,Nat.testBit_shiftRight,Nat.succ_lt_succ_iff]
      rw [Nat.add_comm 1 i]

export CriticalTensor.RectGrid (rowOrder)

lemma row_number {d e a : ℕ} (i : Fin d) (j : Fin e) (k : Fin a) :
    (rowOrder d e a (i,j,k)).val=i.val*(e*a)+(j.val*a+k.val) := by
  change k.val + a*j.val + (e*a)*i.val = _
  ac_rfl

/-- Binary entries of a pure tensor packed as one natural number. -/
def pureMask (d e a x y z : ℕ) : ℕ := tile d (e*a) x (tile e a y z)

lemma pure_bit {d e a : ℕ} (x y z : ℕ) (i : Fin d) (j : Fin e) (k : Fin a) :
    (pureMask d e a x y z).testBit (rowOrder d e a (i,j,k)).val =
      (x.testBit i.val && (y.testBit j.val && z.testBit k.val)) := by
  have hjk : j.val*a+k.val < e*a := calc
    _ < j.val*a+a := Nat.add_lt_add_left k.isLt _
    _ = (j.val+1)*a := (Nat.succ_mul ..).symm
    _ ≤ e*a := Nat.mul_le_mul_right a j.isLt
  rw [pureMask,row_number,tile_bit _ _ _ _ _ _ hjk,tile_bit _ _ _ _ _ _ k.isLt]
  simp only [decide_eq_true_iff.mpr i.isLt,decide_eq_true_iff.mpr j.isLt,Bool.true_and]

end CriticalTensor.PackedTangent

namespace CriticalTensor.PackedTangent

export CriticalTensor.ConsecutiveBorder.Binary (intBit fieldBit cast_intBit fieldBit_xor complex_surjectivity)
export CriticalTensor.BinaryLifting (lift_surj)

abbrev Row (d e a : ℕ) := Fin d × Fin e × Fin a
abbrev Col (d e a n : ℕ) := (Fin n × Fin d) ⊕ ((Fin n × Fin e) ⊕ (Fin n × Fin a))

private def coordinate (data : Array ℕ) (t axis i : ℕ) := (data[t*3+axis]?.getD 0).testBit i

private def matrix {d e a n : ℕ} (data : Array ℕ) : Matrix (Row d e a) (Col d e a n) ℤ
  | (i,j,k),.inl (t,h) => if h=i then intBit (coordinate data t.val 1 j.val)*intBit (coordinate data t.val 2 k.val) else 0
  | (i,j,k),.inr (.inl (t,h)) => if h=j then intBit (coordinate data t.val 0 i.val)*intBit (coordinate data t.val 2 k.val) else 0
  | (i,j,k),.inr (.inr (t,h)) => if h=k then intBit (coordinate data t.val 0 i.val)*intBit (coordinate data t.val 1 j.val) else 0


private lemma spans_of_rank {d e a n : ℕ} (data : Array ℕ)
    (h : Function.Surjective ((matrix (d:=d) (e:=e) (a:=a) (n:=n) data).map (Int.castRingHom ℂ)).mulVec) :
    CriticalTensor.Spans a d e n := by
  let x (t : Fin n) (i : Fin a) : ℂ := (intBit (coordinate data t.val 2 i.val) : ℤ)
  let y (t : Fin n) (j : Fin d) : ℂ := (intBit (coordinate data t.val 0 j.val) : ℤ)
  let z (t : Fin n) (k : Fin e) : ℂ := (intBit (coordinate data t.val 1 k.val) : ℤ)
  refine ⟨x,y,z,?_⟩
  intro T
  obtain ⟨v,hv⟩ := h (fun r => T r.2.2 r.1 r.2.1)
  refine ⟨fun t i => v (.inr (.inr (t,i))),fun t j => v (.inl (t,j)),fun t k => v (.inr (.inl (t,k))),?_⟩
  intro i j k
  refine (congrFun hv (j,k,i)).symm.trans ?_
  change (∑ p : Col d e a n, ((matrix data (j,k,i) p : ℤ) : ℂ)*v p) = _
  simp [matrix,x,y,z,Fintype.sum_sum_type,Fintype.sum_prod_type,apply_ite,ite_mul,
    Finset.sum_ite_eq']
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

end CriticalTensor.PackedTangent

namespace CriticalTensor.PackedTangent

/-- The actual packed tangent column replaces one of the three factor masks by a unit mask. -/
def wordColumn (d e a : ℕ) {n : ℕ} (data : Array ℕ) : Col d e a n → ℕ
  | .inl (t,i) => pureMask d e a (2^i.val) (data[t.val*3+1]?.getD 0) (data[t.val*3+2]?.getD 0)
  | .inr (.inl (t,j)) => pureMask d e a (data[t.val*3]?.getD 0) (2^j.val) (data[t.val*3+2]?.getD 0)
  | .inr (.inr (t,k)) => pureMask d e a (data[t.val*3]?.getD 0) (data[t.val*3+1]?.getD 0) (2^k.val)

private lemma fieldBit_and (x y : Bool) : fieldBit (x && y)=fieldBit x*fieldBit y := by
  cases x <;> cases y <;> simp [fieldBit]

lemma word_entry {d e a n : ℕ} (data : Array ℕ) (row : Row d e a) (col : Col d e a n) :
    fieldBit ((wordColumn d e a data col).testBit (rowOrder d e a row).val) =
    ((matrix data row col : ℤ) : ZMod 2) := by
  obtain ⟨i,j,k⟩ := row
  rcases col with ⟨t,h⟩ | ⟨t,h⟩ | ⟨t,h⟩ <;> rw [wordColumn,pure_bit]
  · by_cases eq : h=i
    · subst h
      simp [matrix,coordinate,cast_intBit,fieldBit_and]
    · simp [matrix,eq,Nat.testBit_two_pow_of_ne (fun v => eq (Fin.ext v)),fieldBit]
  · by_cases eq : h=j
    · subst h
      simp [matrix,coordinate,cast_intBit,fieldBit_and]
    · simp [matrix,eq,Nat.testBit_two_pow_of_ne (fun v => eq (Fin.ext v)),fieldBit]
  · by_cases eq : h=k
    · subst h
      simp [matrix,coordinate,cast_intBit,fieldBit_and]
    · simp [matrix,eq,Nat.testBit_two_pow_of_ne (fun v => eq (Fin.ext v)),fieldBit]

private lemma full_of_selection {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    (M : Matrix I J ℂ) (choose : K → J) (hs : Function.Surjective (M.submatrix id choose).mulVec) :
    Function.Surjective M.mulVec := by
  classical
  let P : Matrix J K ℂ := fun i j => if i=choose j then 1 else 0
  have mp : M*P = M.submatrix id choose := by
    ext i j
    change (∑ t : J, M i t * (if t=choose j then 1 else 0)) = M i (choose j)
    simp [mul_ite]
  intro y
  obtain ⟨w,hw⟩ := hs y
  exact ⟨P.mulVec w,by rw [Matrix.mulVec_mulVec,mp]; exact hw⟩

/-- A full-rank binary matrix of actual tangent directions suffices, with an arbitrary row order. -/
theorem spans_of_selected {d e a n len : ℕ} (data : Array ℕ) (choose : Fin len → Col d e a n)
    (rows : Row d e a ≃ Fin (d*(e*a))) (packed : ℕ → ℕ)
    (entry : ∀ row (j : Fin len), (packed j.val).testBit (rows row).val =
      (wordColumn d e a data (choose j)).testBit (rowOrder d e a row).val)
    (surj : Function.Surjective (Matrix.mulVec
       (fun (i : Fin (d*(e*a))) (j : Fin len) => fieldBit ((packed j.val).testBit i.val)))) :
    CriticalTensor.Spans a d e n := by
  let N := (matrix (d:=d) (e:=e) (a:=a) (n:=n) data).submatrix id choose
  have hs : Function.Surjective (N.map (Int.castRingHom (ZMod 2))).mulVec := by
    intro y
    obtain ⟨w,hw⟩ := surj (y ∘ rows.symm)
    refine ⟨w,?_⟩
    funext row
    have h := congrFun hw (rows row)
    change (∑ j : Fin len, fieldBit ((packed j.val).testBit (rows row).val)*w j) = _ at h
    simp only [Function.comp_apply,Equiv.symm_apply_apply] at h
    change (∑ j : Fin len, ((matrix data row (choose j) : ℤ) : ZMod 2)*w j)=_
    simpa only [entry,word_entry] using h
  apply spans_of_rank data
  exact full_of_selection _ choose (lift_surj N hs)

end CriticalTensor.PackedTangent

namespace CriticalTensor.PackedTangent

/-- Decode at most fuel sparse indices. Each positive base-4096 digit stores one plus its row. -/
def supportWord (m : ℕ) (relabel : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | fuel+1,z =>
    if z=0 then 0 else (2 ^ relabel (((z%4096)-1)%m)) ||| supportWord m relabel fuel (z >>> 12)

/-- Relabeling the sparse row support commutes with reading its individual bit. -/
lemma supportWord_read {m : ℕ} (hm : 0 < m) (p : Fin m ≃ Fin m) (f : ℕ → ℕ)
    (hf : ∀ i : Fin m, f i.val=(p i).val) (n z : ℕ) (q : Fin m) :
    (supportWord m f n z).testBit (p q).val = (supportWord m id n z).testBit q.val := by
  induction n generalizing z with
  | zero => simp [supportWord]
  | succ n ih =>
    by_cases zero : z=0
    · simp [supportWord,zero]
    let r : Fin m := ⟨((z%4096)-1)%m,Nat.mod_lt _ hm⟩
    have bits : ((2 : ℕ)^(f r.val)).testBit (p q).val = ((2 : ℕ)^r.val).testBit q.val := by
      rw [hf,Nat.testBit_two_pow,Nat.testBit_two_pow]
      simp only [Fin.val_inj,p.injective.eq_iff]
    simp only [supportWord,if_neg zero,Nat.testBit_or,ih]
    exact congrArg (fun t => t || (supportWord m id n (z >>> 12)).testBit q.val) bits

/-- Equip an integer table and its checked inverse with their finite permutation. -/
def fromTables {m : ℕ} (hm : 0 < m) (f g : ℕ → ℕ)
    (fg : ∀ i : Fin m, (f ((g i.val)%m))%m=i.val)
    (gf : ∀ i : Fin m, (g ((f i.val)%m))%m=i.val) : Fin m ≃ Fin m where
  toFun i := ⟨(f i.val)%m,Nat.mod_lt _ hm⟩
  invFun i := ⟨(g i.val)%m,Nat.mod_lt _ hm⟩
  left_inv i := Fin.ext (gf i)
  right_inv i := Fin.ext (fg i)

/-- A natural column address chooses first, second, or last factor variation. -/
def chooseCol (d e a r : ℕ) (hd : 0<d) (he : 0<e) (ha : 0<a) (hr : 0<r) (z : ℕ) :
    Col d e a r :=
  if z<r*d then .inl (⟨(z/d)%r,Nat.mod_lt _ hr⟩,⟨z%d,Nat.mod_lt _ hd⟩)
  else if z<r*(d+e) then .inr (.inl (⟨((z-r*d)/e)%r,Nat.mod_lt _ hr⟩,⟨(z-r*d)%e,Nat.mod_lt _ he⟩))
  else .inr (.inr (⟨((z-r*(d+e))/a)%r,Nat.mod_lt _ hr⟩,⟨(z-r*(d+e))%a,Nat.mod_lt _ ha⟩))

end CriticalTensor.PackedTangent

namespace CriticalTensor.Base21Normal

open PackedTangent
private def points : Array ℕ := #[10,15,16,6,29,34,5,128,39,11,32,21,3,192,1,14,12288,12,4,6144,7,2,44032,14,12,327680,19,8,851968,17,1,262144,61,160,4,9,80,5,28,224,416,24,16,64,54,32,288,57,112,8192,8,64,49152,27,96,24576,30,192,196608,52,144,2686976,18,48,1703936,25,512,9,42,1024,18,23,3584,10,44,768,832,26,1280,640,53,1536,39936,10,256,29696,49,2560,4096,11,1792,2162688,20,3072,655360,56,2304,4128768,4,40960,1,5,57344,2,35,16384,6,59,12288,672,33,49152,320,41,20480,18432,6,36864,17408,22,4096,40960,36,32768,131072,38,8192,2228224,43,28672,1310720,62,1572864,17,50,1048576,8,51,786432,28,13,393216,544,40,1966080,576,3,196608,256,48,589824,2048,58,1507328,43008,2,1310720,1024,45,262144,20480,29,720896,1048576,60,65536,3145728,15,131072,524288,55,524288,3932160,37,1083528,2130448,32]
private def fwdTable0 : Array ℕ := #[0x8a2642620f51211fd1201231226cb3680dc0b00af3670ae,0x3f0f812612504012422b0f736a36c36b3b73690f6263265,0x43788174688318287e74518937043936f0ab5750e212a0e3,0x31631931831c37537412b3732207530c421e21f21d09f371,0x37d10422c22d21b37c37a57a22222131537637737f31b317,0x37e22f31a37937838322e7eb7ec7ea64c74a38138000137b,0x1d01c01b01923423523623923338d044232000231230384,0x44b45d38938838638a23b38738c23a23838b2373c601f01e,0x3960dd8f18e04490f44260dba7ea754480b144c47123c44d,0x24275088574e6b90dfa7981d45574c74b0de74d74f44a08b,0x3b91273b80e47477494560768770e187a0fc23d87c7510e0,0x7520e73bc87b3ba1000c50e63720530540ff3bb0e576d438,0x25825a25910323e0e97ed7ef45710231d0e840e57940d101,0x40c1060410ec4595784581057540eb0097f410c38223f0ea,0x3c00ef7567c33bf1080430ee0423be7c51073bd0ed57c7f7,0x3ca4843c910a3c50f13c73c83c41093c30f03c13c246e01a]
private def fwdTable1 : Array ℕ := #[0x42c398a8389b44f45e0b30b27570f345c7557c910b4090f2,0xa7742f8b68a49a842ea7fa7b08c42da7da7a397432240450,0x24343443307875a45275945104b20287d8e1241431a84758,0x75e75f75d0c676c2455c175c18c187186188436223435244,0x19119018f18e7ee18b57724843f43e76143d76024724643c,0x4634624644407f218a00525b5763907ac7d295138f18d38e,0x3f17c446d4660454691924417f304746524a40f048249461,0x44444324b4734427c142747442a47642b4293f324d24c3f2,0x11010da7c0b47ca24f24e47d447446428763764762445472,0x1121114869ba08da8048510f8dfa864ab8de39910e6ba683,0x87f0fa8820fb04a0f976589c4c7a78a82113430a76a2da85,0x4ad05204d11643b11504c43a0490772521142512504ac748,0x45f1192537f57667677f0118884a814af4ae8801170c7879,0x4b245a00639239111b25411a4b122430157b04e7d44b07d3,0x467c218311e9917686ac7f141011d04f7f642146045b11c,0x184134ab77c62f846a45418146f7c72564703f411f46c453]
private def fwdTable2 : Array ℕ := #[0x47846838544e7c8129477475a026b325712818546725546b,0x57d57f19708e39c4b339e39d39b39a80180e47f9b37fd0b5,0x502704b84b62684b54b726776b76a93c7697762664b4135,0x26a2002012691ff02102602502402302202027126f272203,0x7714b990527827727576e2732760c30c826e48905126d26b,0x91d27c0564793032254bb30205527b27a12c91b0582794ba,0x4bd27d48a27e4110620575891ad58a58b4bc58758200a581,0x48d4c169c69b3f73f648c7f93f54bf27f9c348b6d8ac54be,0x80077a7739bb48f7757747729c1aa548e9c27fe7ff4c069d,0x3a03df3e128039f3a14c380657e0b64c24c4acaac1490ac4,0x9412815c29424c680b4812824c580712da2c48019519408f,0x1a47a828328428505905a07b19f26c19d20419b19a4c8a2b,0x3ed49347b05c05b3ee0ca1a176f19c28712e1a31a24821a6,0x9062263044cb05d28c77730590013028828b47e28a4c9289,0x41291e28e8ff1ac6ad58c88879c58303b94358047c05e4ca,0x802ad0acf7d53f880405fac25f64cd290ac04cc91a94a28f]
private def fwdTable3 : Array ℕ := #[0xacc7b27dbad3803812ace7795c5ad25c3a327785c45c65c7,0x3a33a278193f80980c7800b75c8ac39b67d65cb5c97dcad1,0x29293b80593d5ca2913e080a1984941320903e53e73e43e6,0x1312972990799ad9af9ae9ab2942055cc77f3e877e5e7293,0x29a29b0cb7fa9a906b5d25d15cf9aa5d05ce5cd491295298,0x6128d9074144130602a078390478278429f9b029d29e29c,0x90394690178558858603a98f5844920673074ce2275d3306,0x3f95d62a1ac9a2facb7d75d59521aa1a91a81a71a51ab947,0x5dd9bd9bf7875dc9bc5d97865d85db5d75da810acd5c09c0,0x2a32a25e3063a9e6d9aa3a345e15e05dfaa2abd7bd5dea33,0x93e2a519919619380880d0913a53e33e22a43a93a45e25e4,0x1a07fb7a520606419e7cba2a6de5e89b55e66c79407885e5,0x78906a5ec12f5e94874834882749b106613328606529607a,0x91c0685ee9195f15ef5ed5eba037709b45ea9ac3ef0cc9b2,0x5f247a00b94941506975b9215d42283089202a65f0944902,0x5f58867d8a2ea8791f6dc9275852a82a79485f49457935f3]
private def fwdTable4 : Array ℕ := #[0x5fa7f87e37d97daac72a99bea3080f5f9abf3fa5f85f7abe,0xa88abbaa16da811aa05fd7fc5fc5fe2aa5fba01abcaa4ac8,0x4df6092ad0923aa3ab2ac13c3a63a74d95ff2ab13b4e00b8,0x22074e192207113f60160260760560313e4de4dd4dc600,0x4e67dd60a81b2af6144e360c6089ca4e40802082ae20920c,0x4ec63e60d4ea95c4e77de4e84e59c80cda2260b2be2b00ce,0x9554f04ed5032299545094ee2b22b34efa5c4162b14eb7e1,0x2b82b66041496062b54f17e04f4a238c24f34f27df00c508,0x4fb82d6157e4a497b360f14b3fb4f74f67e92b9aa68297e5,0x7e7502a4b7b761182c6105014fc9cc60e14d4fd7e84fa82a,0x4d58f292e8203af3a81b21b31b192d1af0b982ba357e6ab0,0x3ec2bb81f2ba4954969171b08e21ae3e91b43ea497923093,0x49ba054998e38ec49a8f607c20d2bc61361206c20a3eb498,0x9c79c96199c649ea060cf9cba212bd49d8f563761761649c,0xa671bea273094a12b4a63a4aa642c049f7e2a60a0aa624a0,0x4172c22c179661e79579461d13661800d22a9a606d1c0504]
private def fwdTable5 : Array ℕ := #[0xa9d8e43fd9533fc2c34a3a9f653aaaaa961a8132b7a66908,0x62aa4da586294a5a37a3a7c0a38a3b4a4a5761c4a861b4a9,0x9313ac4da4db61f2c41370ba4aa78ba55a0ba318244a64a7,0x9169247a47a27a37a18f381e8f491362009493593092f4cf,0x6b16b06a407d9c58f77a68f906e20b1ba1b81b91b71b61b5,0x4d76d00d02c78ed2bf2c62c58f86388fa6364d6a096a56a6,0x6226237ad7978216218148c181c9568877aeabaa0495a4e9,0x817a26a5e8154f52c900e2f51382c84d34d0a61a5f30a4d8,0x3fe4d169278c626691aa7690ab56e0a5da69418625624816,0x5008268274f94ff4fe696697695a5a627694ab8ab38224f8,0x92a91462f06f7ccaac819ab193a818828aadaae78f6289c4,0x62e62d9392cb2ca13d13909592862c9294d43ae3ad92c62b,0x95b2cc95914000320e9369339324e293493793892b918915,0x13a0720732cf6326318ee14207007e64f2cd6b21412ce630,0x7980756342d195e14495d2d07cd9586dd1439576334d20d1,0x63a63900f14741921c4a21bf1bd1461bc1bb081074635145]
private def fwdTable6 : Array ℕ := #[0x65214a651650a6a2d29a781a95f6df63da6863c148a6563b,0x88988aab4a52a5614ca89a59aaf825823aa83ff88ba4ca36,0xab678da2914fa25a24a517b4a4e14ea4fa50590aaba39ab2,0x1775955940963b15a21571543b23b05145192d3152513082,0x65420f5985960981585972d65155185a31565162d51552d4,0xa18a1c2d815d15ea1a51f15b2d715a15c07fa075102fa159,0x98394e8ba1628d999065516088d6d18fd0d296015f2eca0f,0x1cf1ce16494b25c94f94c6d21636569123f01d02d9161680,0x1661d20271d195053c1678b796894d8b888f1658b901098c,0x2f983540a8cd16c16b2dd16916a2db1686b403c65a6582da,0x65e65d16f65b1708c08cc83616e4222dc6b64236b516d8a8,0x3b33b63b459258e5911c11c41720bb1c215317165f65c6c9,0x2df59a5996626602de5a85a76615a917432009732117331f,0x63fa166662e26652e12e3083a1ba12832210664a176632e0,0xac666b7a766aa13a1e66c0d3a11099668669833667640a10,0x30b25d30d5116d309a2e56d764d6d666f2e467066d67166e]
private def fwdTable7 : Array ℕ := #[0x2e997d83477b77c82f77d82e53b2e701198053d53a30c2e6,0x8da8ce4011501d48d067367403d6722ea8bc6c80aa2e897e,0x7b67bf7b98bf8d68bd6758318be8d78b08c983a8308938c8,0x58d6c25a058f5075055060bc1d81d91d71d54001d38c77b5,0x6bc1cc6bb5aa6bf6bd5a51cb1c71c91c809b1cd50e1ca593,0x88e6798fb084678a19a152116766775ac59b59d59f59c59e,0x67b67c8b20d49612eb50f5ae64a6496436416428fc88c5af,0x5b36828905b18b364e67e67d6e26e16e367f98967a9642ed,0x97f5b25b09846e56ae0129818386e431430f30e25e313837,0x50b50a0a02f103e6592f32f08d82ee6e76e641a2ef8b4681,0x5375365315335325348ae8ab8b58ac8ca8cb40350c50d402,0x1c36c31c60bd36e2f22f48d38c636d8af7b87be7ba8ad7bb,0x5ad6c01516c609c51751a31e5a45a13b56be5123cd1c56c1,0x6e82133262123243256c46c532351c6ca6db5ab3225a651b,0x9623288fe9655233270a1520522521a1451e6e951d524087,0x52c6d59876ec9678915266ebab96ea963525a20a1fa1d0d5]
private def fwdTable8 : Array ℕ := #[0x52b32a01398241b6ed52832925f9929856d45270a265752d,0x48c52fc69352a32b98a7ce98e6ee52996689298898b986,0x52f8d452e6ef32d98d8dc8cf02b02d02c02a0290282fb32c,0x8d56985398d15381d68db8d279f7bc5358c383953032e8c4,0x3301806f009d54a55254b5493cf3ce55185417f0a432f0a3,0x33a3393383373363346f133355054e54f54d5463325bf331,0x64b6486456f86446f76f46f36f533c6f608533b69f69e214,0x9696fb1ec33f8668576fa33d6f933e0d61e31df1dd1db1da,0xa6f3415555563102603116fd1e98588591e6a8e1e43406fc,0xa8aa739d2a6b41c34268c68d6fe68e6ff557909a5301478a,0x8748f08759da34734634534934834496c96d701702700343,0x9dd1f79e99d79ea5b91f889817c7034258e99f24249ee9dc,0x9fd54c96f3d23d13d085596e34b34a5530be1fc1fb1fa1f9,0x33534c34f34d70886370770570670497597a9719706f209e,0x6466a89949937926a76a90865b684a5b52152167903d334e,0xa45999851896a409a4a3c0d71e01de545867a3d647350709]
private def fwdTable9 : Array ℕ := #[0x31226135156d686685a0c68868968496b96a70b71571670a,0x70e70d68b717a08a7168aa7079da72015a9741d70c559554,0x99654439540490a4053526b70a578e69a699a8f85ba6ca6e,0x5ba9d95b79db03903803703603503471099e70f8718b1870,0x3d43d554817d1780c98560bf7cf9f07119f19ec9f35bc5bb,0x97b6cf97486090e86197917e8501799720fd3d73db3da3d6,0x8528477a90fe40ba4721821735371397771290f90c8dd90b,0xa3e9a20d81e25430a61dc3567913559986a3354a3f9976aa,0x6873579ce799a747141ef1f08428411eb7afa48849897848,0x1f4a90a951f117a6af01630041e84c1f61f5a0d1f31f23cb,0x40686c0a771a35935a7197187d03589cfa8d86899a86a3cc,0x17b84e84d86d5478ef86f86e9ed99d85e99c9e771b9e899b,0x86590d9110c09f735b9f69d485d9d571d71c71f7205b871e,0x97653f92692555a97c9730ac6cd7216cc6ce3dd5580c1978,0x54121a6a02196a156191089e86472289455b8a553e862540,0x9e41e117556072456472355e55fa4183e55d56255c7aa088]
private def fwdTable10 : Array ℕ := #[0x1e585a7b083b5668a78a65659e69e5542563a429d68530d9,0x86b99f01787841f5688728733932f639484b5671e81e7a6d,0x35c56b6b88a97277269d3a919d156a569a28a549a079a9a1,0x5718e689989a56f8ea7a056e8e58e88e79e140756c7288aa,0x9ff9f89de9f49f95749df5bd5be9eb9d85738eb9e0572570,0xad35e89d35d3de1fe2ff2fe3dc3d85b49b72fd0c29a58a0,0x6ab6a29b88958a18a289f72503303203103002f02e8a33d9,0x83f9e20a93609e3a4499583c72b35fa00089a0e72972a0a8,0x1ee1eda9c1ea9fb84083d72da467ab72c0da9a3007a43176,0x4209b9a987323612f773073172f72e84379ba9968f7b19d0,0xa93a8ca9479ea968458448698bb9cda9aa9ba8ba5b018a92,0x36336485c73e87674073840874173f9fa737008362846733,0x9fc74473c73d73b73a85f7399ef73636636584f742735734,0x7d19f57439fe]
private def fwdTable : Array (Array ℕ) := #[fwdTable0,fwdTable1,fwdTable2,fwdTable3,fwdTable4,fwdTable5,fwdTable6,fwdTable7,fwdTable8,fwdTable9,fwdTable10]
private def fwd (q : ℕ) :=
  let chunk := fwdTable[(q/16)/16]?.getD #[]
  ((chunk[(q/16)%16]?.getD 0) >>> (12*(q%16))) % 4096
private def bwdTable0 : Array ℕ := #[0x5fd5794f54713ed2610d5ab3a821dd15981f5cb43f051063,0x7107006f06e06d0f006caa1a1d99991589180d789705681,0xa63a6282682582782482382268d23923823723623523a234,0x1f79b7176932e536993b93a939938937936a67a66a65a64,0x1e51d31bd1b91271ab1b71621661ef16b0650e90e70dd01b,0x2f92e12db2cc2cb2b92ba25226925d2570b50b61be24222f,0x5ac5474f24c334a3ce3ea3de3653c53c23bb39c26a35f35a,0x6545d654c4c82b83c033c12c1b60a85ee5f25dd5de43b5d7,0x2a021c19b11709000fa749f07e08e886475c6d86305f3444,0x318d084c7cb7446fa6e664b6c363c5b85344b042c3a8324,0x2000a5f9d8024712a7da709ad97a9278428408027e979d,0x9488c47bc7386b65284a442031829621018c109108084003,0x4d94504553d134d2c994a2451c113c0b9035246a529d19cc,0x9a09408e004088a84a0097d8f88757f076c6e86645e055d,0xee0e80e20dc0d60d00ca0c40be0b80b20ac0200220a60a0,0xb496c9540a41ac1ae1aa01e01801200c08a1061000fa0f4]
private def bwdTable1 : Array ℕ := #[0x19819218e0d31020fc0f60ea0e40de0d804e0cc0c60c00ba,0x1f21ec1e61e01da1d81ce1c81c21bc1ba1b41a419f19e18f,0x3cc2c42a525403902120a2040ae01d01c01a00800700b009,0x43a4345ba4284225df5b95775294f72201fe3c432533f2d6,0x62c62649461a48860e47c6025fc5f65f05ea5e45d85d25cc,0x66265b65c65565865665064a6396446416386b46327cd71c,0x6ad6a76a169b69a69769869568968f68367d67766c671668,0x84395894c8b79bf99b95694b63fa809fd6c56c16b76b36ab,0x14d14c15113714a15a0281341361352031ff1ed02b1f884e,0x2b73ba2b52c62b32b23ad32721d3ac2a22a13ab16914f14e,0x4a54b62672eb3713763753743732c03722bf2c32c22c83bf,0x5f84ee5f75f55f45455435445425415404b44a84a94a74b8,0x67f67e74374e7487417467457477bd7c16b87bf6b56b94f1,0x8738f687297987187073673773583a73471b73268e68c673,0x989a8fa8e87d985a8c887a12a11884a0f88287497c9fe8f7,0x23ba5a00a8c38c28c18c08b98be99599499f99299199c988]
private def bwdTable2 : Array ℕ := #[0x64e5ca4c74405464c244144343e3bc3362b423012623d23e,0x330340325fa04b9ee9ec9699688e38e48607de7dc7586d4,0x5e05904c04d0194f446b3e63622de25a1d6132047046037,0xd10cb0a308107907606807507306906a06b067064062061,0x18a18917217117d16416114814214113a13012f09f123111,0x8077826fe67b1580ce0cd0cf2051f52011d91cd1b51b31b2,0x2322442412b624023f23c22b22822201000e01100d90e88a,0x27526c26e25e25625525124c24b24724a3c724823123322e,0x2f02ed35e2da2d42d22d02d52c53c32bb2bc2bd2a82ae29c,0x35435135235034e34f33d34033e3c134133733032f32a2f5,0x44b44242d4294234154093f63f53e33ae3a439f39e37d359,0x55a4524d64c64be4bc48347f50247e47a4ea466467462451,0x5dc5d15d45ce5bc5bb57a57655c55955852a50a4fe4fd4e6,0x6cf6ca6996a569669067265d65764864264063360a5ec5e8,0x79279677066176a71570f7117067006f96f46d96dc6da6d0,0xa59a58a5381d82165169f1fba9aa165787b97997ba79c798]
private def bwdTable3 : Array ℕ := #[0x7847836fd7016ff5714ec3e53643602d82dd25b2581d5998,0x6c07c80c503c04105d03e03d04003f04578578190f88988b,0x84183182b82081a80e8087ee7ea7dd7da7db7d77d26c26c4,0x87c87687886686385f85e85d85c85b8df85a85885285084f,0x8dd8e08dc8de8c78c68a88a78ab8aa8a98a68a089a88e881,0xa76a5ea5ca2f9ca9aa9ab9a698e97897697396792990d8f1,0x257bb7b6016015017013005001ac5ac4abeabfab2a9ba7c,0x4205f04f04a05004905c05b04304403b03a0380b7030027,0x15215006607707407a07d07c07807b20d06005a0d2053052,0x29b21921821b21721619310e11308f92da15a171dc1db156,0x4ab5b35b252e42a42b3a34aa4264273a73a231f31e29a29f,0xeb0e60e30bd0b30bb0af0ad0146be7c56bd6bf63763b636,0x8478467c29a09900ff0fd0f80f90720fb0f70f50f20f30ef,0x29ea5b9d3a57952951a60a5695395094e94f8e18cc8cb8ca,0x3d22ca2cf4bf4c14b34b53333223203233213a63a529d329,0x61358f50d50b48740337f2fb27b27a2771f317317016f674]
private def bwdTable4 : Array ℕ := #[0x1630c30c10df96b69d101ab8a339af92a92c7a37a071d733,0xa1b99791389b80b7935fb5834ff4633eb35c35b2ef26b1e7,0x11e11a11610f1751771741851790898b58b26a36a61e3a9f,0x1471461441401bb1b80260b002f13313112e12d1121221a3,0x10b20c08008307f09108b08518718618117f17e17b16815c,0x1cf10a07e1051e11de0db0d90c70a90971f91f012a128110,0x1f70f116d1f12001fa16a20e20216c16515d15f15e1601e2,0x2132d31882e22cd3ee25c20f20917620817817c1800821f4,0x28b28527f27927326d2433c83ca19d1990fe3c92c12a92a3,0x4e54db4d54d04cf4ca4cd4c04b24ba4bb3262ce366342291,0x1c51c41bf1b119552751051252052151b5155095f94eb4e0,0x27627026f26425925024e22d22922c22a22121a1df1d71d1,0x5303632f62f32dc2e02d12b11a72ab2a729429929527e281,0x42f43343243152c52d42557055f5534af5b45755e158e574,0x46546846d45f46145c56045845a44f4574454495c643d421,0x59b59a49349748f49159c59048648557b47747447347946e]
private def bwdTable5 : Array ℕ := #[0x7697427a17a279f79e46947073b73973a4f046c49e49859f,0x6597e47e27d67d07c96346467ca6436476356317c36fc652,0x82f82d8007ff80f81b8158098037f97f47e17eb7e77e67e8,0x9de9e270368a70770283d83b7af7ae8357aa7ac7ab7ad832,0x8558568548ce84984b84894d9bb8538f592e97ba059ef9e0,0x9f79f89f49f29e49db9119d289488c88d9108c584a845857,0xa3ba3890ca32a2ea26a25a1aa13a0ba089faa049f39ea9fc,0x21e29721f0e11d40480c20da149157023a4aa44a41a3fa40,0x73c6bb73f2e926526626836b26336a3f73672e62622602e3,0x7527507537517546ce6cd64d64964c63e63d7406bc6ba623,0x7607687cf7557d374c6c66c96c87d17497c764563a7c673d,0x851a47a4894194093f8ba9c193d8e78e5a5577f78e77c78d,0x34734434333531332b3123173003013073023052ad139381,0x39539138f38b38638438938738537e3783e7361349348345,0x3da3dd3d93cd3d83d43cb3b63313b43b03a039d3a1397396,0x42441641941741440f4054024012f73ff3f33f03ef3db3e2]
private def bwdTable6 : Array ℕ := #[0x48949545d44845344d42e44743747b43647d435438439430,0x52b4fb4f85135115044dd4f64d24d148d44a4c54c449b499,0x5ad5bf5be5b65b051f51c5a159558b58258156e56f56a535,0x6df45e6056036005ff5fe5564d35545f15ed5e25db5da5d0,0x5d577a6f705586f76776686e8f28ef86d86b7657637646e1,0x6b26af6ae6b16ac69279a69180167666964f50760f60d60c,0x6f56f06f26e96ee6ec6e46e56e26dd6db6d36d16cc6c76cb,0x77477977876e76f77275e75b7567577297187197166f16f3,0xa9289689889991d91990790898f90b90a90619077e790670,0x86286128027d27c92592483e59859959759481c58d58a588,0x99a78a2ea1e9a6f9708e98ee8ea55055154d974a6e9eb9ed,0x74b7c474a74f74d19109ba2d9286a46a26942065d354f54e,0x95e9d49d79d50067d56b07133b37cc7d87d97be73e7c07ce,0x6063b75e53f97d441c39a2726f86f67fe8046fb67866655e,0x82c81680a7fc7f87f67e37df79579478b786775777776586,0x89589788888087e87987786c86a8658678698688d185984d]
private def bwdTable7 : Array ℕ := #[0x93391f91e9129039008f08db8d98d78d88d68b68a28a38a1,0x9c39c09c59c49b29ac9a99a891c90190298a966964945935,0xa97a96a88a85a77a71a72a31a2ba2aa689fb9f99e69d69c2,0xab6abcaccacdacbacaac8ab9ab4ac6ac1ac0ab0a9ca98a99,0x9209c0930960950540aa1b00ab02d029acead1ac2ab7aba,0x13e13f13d1383e912b1291201070ed1040d70360bf0a109e,0x2c72490b113b2272262241ea1ca1cb1a9183184182145143,0x33433270970b70c28e3083032d922328a28928d28824f3d6,0x5a292662e58c5268903cf3b138c38836c35535835631d319,0x837aac9172e7a94a2198c5ef56c4fc4fa4f93f18eb9778e2,0x98456456d155a869f196d2be6ed5493bd53d53b53c53aa39,0x72e7b33928367b07b272d7b449c72f73062848a30ea91a0d,0x9478185e75ab3b918b10320b1f61fc0e516e0ec1ee17a518,0x47245944e31130d40b40c3fd3793142fc1d21d0154ad39a7,0xc814b0c905705805648449249f4a148048c40d4e4460478,0x2822832114183be34c27840e0e01e41cc0d416715b1e81c9]
private def bwdTable8 : Array ℕ := #[0x4062143a931a2aa32831b3aa2a629832d2fa30b2ff21528f,0x4bd53809856744c6085a95a657f58057c56950330a41b383,0x70a70848e49a4a34904815a559d59e61652261559156b4ac,0xa7f9f5a89a78a0c7238337877806a869e70d6e36d5728722,0xac39be9bd996a148e698298096eab1aaaaa9a95987986a8a,0xac99b59c7abd922a0e88588687a9498c9844a0196f8fd957,0x9b99b89bc9aea1f9a1aa89a38f487b9cf9e78da9e195a95c,0x1af02a1250a20bc0a51c0a1c0a7abb8ad8afa18a19932930,0x68475f66776161261e61f2e85653fe09d1c702c1ad02e1c3,0xa699e8a5d1a810ca3ca3d8b89818fca6c9e57218137fa77d,0x7b57a97b17a67a8a30a2c6a0a0aa099e311ca61a6aa6ba50,0x72c72772a714aa766d68268568811d7a779177b76d931725,0x82871e69c6a97a47a57247207317b781e8308344755686aa,0x19719496182983971f66b79772672b83f82e7b883883c71a,0x9ba5d955b4cba43a3a8b4a36a35a3ea3750e4cc4b712408c,0x2ec7ed66576275d55554855754a4c94d45375394ae08d8ae]
private def bwdTable9 : Array ℕ := #[0x96395b9ce96296092b89350035d2df24d35736f3e036d2d7,0x3fa2ee25f3df2532f23dc5c14b953f5c05ae5366759cd9e9,0x5314ad4a65b15c25af5b55b73f89dd9dc53e4b143c3e83e4,0x31c3af32c22532e5a75bd5c35c45c95335c55c85c752f532,0x67a66e68667967c2f13ec3f437036e3f23e12e42ac2af3b2,0x6075eb5e945b5cf5615cd5e65e356646f46a50c37715368b,0x8cd8c88a48a590590487f6877fb8147ec7717f57ef76b663,0x78f71070e9da95f8d49599d09659df8d595d9d99558d38d2,0x36881782a6808118197738127fd81080578c66f80c788704,0xa1e9349b69b49b09a28fe97597192fa798ed8ec8061eb66a,0x33a33933b3d333834634b11b6094f3a518faa8397ea20a22,0x38d40838e38a28c19ca9ea6da543153b53d52123d03c6353,0x9a598daa64964d84464de4564df4dc54b5a0274284287380,0xa49a4d8bf8b093c8ac93ea458bca029c69c8a2989da27a90,0xac78b19b7943a468bb8bd9b19b3a07a069ffa7ba7ea34a42,0xa4fad08cfacfa8bab5a4ba4e9cb9c9ad2a4c9428b3944946]
private def bwdTable10 : Array ℕ := #[0x660a739939095244e255291b6534da4ce5623d7207413a75,0x7f26ea7f165e6d765a75a65f6d26de7597e56eb6d66e76e0,0x37b3fc1a12a42b03b862da244ed57e62b62a4764544d77f3,0x97297f8f38f951651962151751a6104a2398390304523407,0x62562751e61149d4e848b98396aa878ffa7aa81a039f68fb,0x57257d585464aa259661851d51461b525a2389261c629624,0x88f920a1092189c60b5846044ef5016014e74e94e15734e3,0x11908711518d1181140991a611f1a208698b89e91691a918,0x9238839a4aaeaa389f61941f3fb1961a012110d1a51c619a,0x50839b50fa8daa4aa5a93a9d914aab99daadaafaa0a2899e,0x6175a35a45aa62250650561458948228641139939441d41a,0x40440039341241e5637f75931fd62f58761d5926205a84a0,0x2fd30938230f37a29337c41040a6ef2712903162f82922f4,0x30c3063102fe]
private def bwdTable : Array (Array ℕ) := #[bwdTable0,bwdTable1,bwdTable2,bwdTable3,bwdTable4,bwdTable5,bwdTable6,bwdTable7,bwdTable8,bwdTable9,bwdTable10]
private def bwd (q : ℕ) :=
  let chunk := bwdTable[(q/16)/16]?.getD #[]
  ((chunk[(q/16)%16]?.getD 0) >>> (12*(q%16))) % 4096
private def selTable0 : Array ℕ := #[0x15b15a15915815715415195f95715315281575a7021505c3,0xd2a29a28a27a26541a2516416316216116015f15e15d15c,0xaf8af7ae3ae236cae1ae0adfadc12aa41a40a3fa3e058a3d,0x9fc7e98838991551564a9b3db3cb3bb3ab393c5afbafaaf9,0x9e141d58f11456058c02d56a596a22a1c18f4fd5814fb5b7,0x63162d41f22766c3f512b08261961741e4f557954d613610,0x2c072e7626c05e76815d65d46859d912d6942bc6b4420658,0x6005f05e05d05905b05a05605705508942575d79f701035,0xec0eb0ea0e90e80e70680670630650640620612c19de05c,0x50b0f80f70f60f54277b53d20f40f30f20f10f00ef0ee0ed,0x52f2b50fb0fa0541721250531a196d8f110c2c542912019d,0x2c72c62c42c32c22bf2be2bd2bb2ba2b92b855b2b72b65b3,0x40e74740d40c40b40a10e4094084074064053f42c99bd2c8,0x4da4d94d85194d741941841741641541441341241141040f,0x4e84e74e64e54e44e34e24e14e04df4de4dd03f9ff4dc4db,0x5370660f90400425a29fb5345335325315304ec4eb4ea4e9]
private def selTable1 : Array ℕ := #[0x59f59e59d57e54454354254053f53e53d53c53b53a539538,0x5ae5ad5ac5ab5aa5a95a85a75a65a55a45a35a13b45a00ff,0x5d16296236163db5b85b25b15354c239c51d5042df2ca5b4,0x79b79a7997987977897577366d16c86a75b069564f63d62c,0x7ac7ab7aa7a97a87a77a67a57a47a37a27a17a079e79d79c,0x84f03684e3fc13284d84c84b20484a8498487ef8478077be,0x85b85a85984219b369858857855354854853852450851850,0x9919679659208f48ee8cd8cb1088bd8a77f187587385c47a,0xa10080a0e9faa0da0ba059f79f99f849ba200ab9f60c0993,0x1405cea46a45a44a43a305f7691a2fa2da2ca2ba1aa12a11,0xa6ea6d645a58a5416ba52a51a50a39a4f02f628116a47142,0xa9ba99761a98a97a78a761eda75a74a73009a711d7a70a6f,0xadaad92ed00eabfabeabdabcabb85dab4ab3ab2ab0aafa9c,0x9999afb11941b10b0fae937fae87c2ae7ae6ae5addadb43b,0x959b24b23943b22b2192eb19b18b17b16b15b138d3983b12,0x2e014000b38b37493b35b34b33b2c46bb2ab29b28b27b25]
private def selTable2 : Array ℕ := #[0x4b04a6d67180490481437440470460450440430416ac612,0x13b1115bb2550699c205296a0519ac05004f7b204e04d04c,0x5285c15255bf3c607207107006f06e06d06c50a52441a3f0,0x4f941b5765c83872a05c628b1a451352a5c435d0bd2760a8,0x27855a59855628d34a5115915903dd56312830b5755491fa,0x7807707607506b26257d06a59b3751bc9df44751f30c129,0x6aa1156976ad30d2f869663b6a93b51f80fc5b550507a079,0x61b34c61aa495ea6426154484c65e669822661463c3df13f,0x34d62f69a6006af62b5d34492125cf6ab62730e6663cb1fd,0x44a6406566822fa3f66695fb5e567f12c6526516503b70ad,0x321196ff2001046a36a15d86874213b81ff1d55c9a60657,0x6d971b77311a76f3cf70d35016e70c74e42370842274a705,0x1463fb13111c00b10778e6de11b7311451067667646c9087,0x87700d37e2978007ff7fa11d3157f33bd00c1da79033e44f,0x8147e88248398230b543c88218746687e3403fd7b31333a9,0x2f320c1e286d19e1470de0d507d07c07381a0cb7ee2840b6]
private def selTable3 : Array ℕ := #[0x7e526f7b987f26e26b26a26865926708326664326526407b,0x1097af4f744524c5c25233335bd44423746781127299d271,0x93929a0e128584083e83d8658383ea14a86280900f7c510b,0x45440099a13692899614b4d29111f38e597f9953c1010925,0x93d3ad8fb9ab8e110d2b094a36d91e29b9a29a19a099e99b,0x13a3da8b78db97a28897597442c8ff96c03cb0491d8ed8e8,0x1264d07d851c51b5b63b11ce5039624ac2b40e628a27503e,0x31e09317a45926107e34851242f5be22220d5bc11213ca04,0x5662635143724985165174835c746e4850a9165a075265c0,0x2cf6386a669060c2ce2cd4ee2cc2cb29c9c9274551594568,0x6bca7a2d52d40081eb1fc2d37402d29d42d16642d05ca622,0x35e2773493dc02b57a57812751a2ecab88742d77f081c2d6,0x93a2da2d917727346f5855001a549928c5840d352b583582,0x2e48f82dd8a00122f18b62de95020a9662dc1f49a89242db,0x5d23e02f96bf01e6bd2e81e90061fe64e5f60072e60052e5,0x3683676cc36636536436336219361c36136056c4fe35f32a]
private def selTable4 : Array ℕ := #[0x43157ba144303ed39338837137036f9b836e82c36b88436a,0x44244144043f43e43d43a439438437436324435434433432,0x3b355e55d55c56d0d45155014ff4ed9a44a882e4a445c443,0x44654f56556458e520a034f402a5625093f25611e555f58a,0xfe52e52952c51857357257150257056f59a49a56e56b569,0x59258748458617d17b57f31f57c5775741a72794f213d588,0x28e0bea1ea24a21a1ba19a1f59759c16717c45b320595321,0x6372512a262e62a6025eb4b04713890bf0aa1bb4704ad2a3,0x64b64a64964864764663f0315fc9d55891ba5d063e63a639,0x6c56c46c30336c212f6c13a51053ba6bb67b66865a65364c,0x3de52213e3f31fb6d00db3904776cf6ce6cd6cb6c76c644d,0x6b66b55ee6b369b6993373a05e369360fa3600434b593550,0x6d25d527b6306b16013386253c96243b66a56213a15f161d,0x1d63b974274100a71373f73573273072a7146f36ef6e26dd,0x8626974b44ca96749a8722a7487463f812e7457177433a4,0x4a27264a07520da751aa572475074f720a944614ca25474c]
private def selTable5 : Array ℕ := #[0x7e17da3807ea8167d47090747d98057c378d7777547536e4,0x8371358638618602ee8312eb85f7f281e88981b8067fb7f4,0x87086f32d86a35786c86b8698688678663ff9da7b4039864,0x3c48a27fe7fc3558803818720c91c78712994a67ec8184a7,0x1de9942080112ef90e99294f94c93c92b8f28e93ee8d09c0,0x3d9c41399c39c19bf46a9be99f4699199b39a790f926910,0xe59cf2489ce9cd9cc9cb9ca9c84579c72359c631c14e9c5,0x5e1665a34334a09238a16553239a089fe4c09d19364ab9d0,0x10aab62d8a565ed69d17ea4e61867069c6b2a4d5eca4ba4a,0x211f17dd0233aa7b10224ce81f1ef88d81dab77aeab5aa8,0xacbac70243d51dd2068761db20520785e88a833832ab988b,0x97c48198f921b31b30b2f94db2e3ecb06af6ad282632cace,0x68065466a4c83771d45de6365db38c49d0d76331e820ea6a,0x47466149e6602a668b0d865f0ae1bf65d23c66f65530f030,0x9a68323e66b44b2292fb1ea01b5cd67a01c68f3a31aa662,0x1d2a768d4755dd6a22925da1955ef5d96035d734f5ff084]
private def selTable6 : Array ℕ := #[0x70e2937077713e32fc71531176e3266fd09b70016d6fe76d,0x1d87374627670c60b13f970a70422b0b02153e41441c1711,0x7551d93bc1ee2ea73d7696e56e37396e072108871e6dc6d3,0x37a931856f54643537786d80346ee76075f75e75c78822d,0x31008c08b07f3048222309149ae03b99803a7e07ca03887a,0x2ac8304b948f84528282b84183c4263e78201986f70c80b3,0x7b77f9451891ac57b67f787b11e7f58798784cf7b03d33be,0x8934527e380e3fe7e21343e93027c88860ca19c2830a0259,0x9232e17591b9b532f42b9869708ec9b208f001ad1341ad7,0x9121210ac6b70d60b90ce0cc3917250dc0c70b77236e10b2,0x18c18817f16814f1384019ad1377196d71301238ba8a48fc,0x88c8347dc3bf1dc1d11cf1b71b58021b01b219275b72f787,0x3c38cc1f620b1f98353a81f09d61f23ab8083c07c67c73d4,0x1703cd3e6604b4527d27c27a32b7b808d27008a26d22e22c,0x8177bc7ba34245383aaca9d825a82a3567e682524580f77a,0x94718a92f9173433eb94294093f9979293199132f093b3d6]
private def selTable7 : Array ℕ := #[0x8f318b9b69b49b14552338fa8e41df9aa3c24bd2860b8949,0x90b8df97948029d2b20cf0ba34425d0a4090b039698f691f,0x95a42e2369db31d3ef95428935b8aeaf18a6124af30138f5,0x8c639b9638b31cd4828c929f1b80d18c70bc8c546d8ab8c1,0xfd5079e93b24ef45a4f3a063f15b9a028ca49790a9341a3,0x2f658d50c113a0c54a50858b3731b91904fa2252f54f13c7,0x6ae21154c54e6a869260ea173360959d752d55938a3354c4,0x3a23ca7d18818976ba2a538b0852e35f347261f6b96415fe,0x2aa28728128027f08e2145f85f238d65b66d0995e960d64d,0x39635c35934e33233133032932833c77932732531a306305,0x45644e42441c4044034023f73e83e53e22027166d43bb39a,0x49049148947d82f7ed89d47c77c88747b47947647396f8d5,0x4d34d14cd4cc4c95582a11a65555573741914af4864ae4a1,0xa91706a896356770af0d969f4b367319450d0814f84d64d4,0x16624d24e50f51052727e7101ac37a1970c59e576377533b,0x49c61e60b609a3b5fd5f05dc0944fc554a13a1809650e23a]
private def selTable8 : Array ℕ := #[0x6a0102a31a331011001d201a1d366367c634290632a32620,0x72d72b50671d71a6f448d6e616f1846df6db6ca6b86a468a,0x87d7bb2a8478aae77d70f795295aa779237b6f873a7381ec,0x8bc8a52218bb8a98858448288278038018947f67de7c07bf,0x9784aa8de8d88d7b0796e8d48d18c88c48c38c03478bf8be,0x96190994e94b91c99c42a9189163ac92390d31b8e78e68e3,0xe49771cb97697295d34597196b92c1e13d997e8ce968952,0x22320f2102244f6521309091a009e40e29a395b9879b9399,0xacd7df821accaa34a3aa4a5aa8ca5d4c354b2f72f45ba30a,0x3af1f70299f3002b43b40b2d9b0b05af5af2aecad6ad5ad0,0x2ae4bb3957eb0e00d00bb0b43460a60285489518b98b5110,0x1c67d62982ad17909f1864287e41d08437e717311f0e382d,0xaed89a7d5aeb3941b10dfaf07c17d71b34bc1c81827331c5,0x9ea1e61e089e7bd89c7d3aee4a58049e28468194922af4ba,0x8b26ed2ff3132b3b4198e8dc1a21cc29e2942162012e1546,0x323ac8ac980b317a88a816da2fe3122fd76b2e92e72e00cd]
private def selTable9 : Array ℕ := #[0x1f502710faff3ae38335835123d45f250339180181a55a59,0x69e6726b066e16a169098a7ca7b72c3a67293d033f89f953,0xa796e87843d175878375620333a8a12f201f76c3ce23b097,0x6791035e25f95cc7287827857817593a76e9a7d6e70206eb,0x7cfad80a124346516c68668846045d32268445e67d1e7019,0x2429dd6f13fa786a866f078a31425623f71f7122532527d0,0x8e22091b49b79018eb92d81018983b7cb21c21b80a7cc219,0x7ce7cd1743d897baf48f7b01b023d702697dafe8f9afd9a9,0x78b9e017125824689624489825b7d28954687fdad3813812,0x18d98d8b14bf9608da23412221f2b1217b0e21d4c70a2300,0x3e114167e213228a3c5e84f06f63524d521e98014c8ad8d9,0xc20c168c676a6739d8c29270255f43cca385e4118a37117,0x2498d68aa77ea7f6eca80a847727747707271a829128f674,0x9384969a59359bb39793739847e8fd3848e025f24724a0a5,0x1c998b1b64958dd1ca382386385b0b22092a232958b42b3f,0x9084c14948b490c9229bc4be96490798c8af93319f9901a0]
private def selTable10 : Array ℕ := #[0x3163089029441ad09c4cb176ac1218a85a824c59e89e6307,0xb4888e89022f148301ac2ac388f23121a7c987c149ac4892,0x4b260539e9ee5f566779646c70b4631af76a78c95683680c,0x8feb0d14d93e2966fa76873c6fc79177b37865e0c337d196,0x6fb2a91c29e3aa2a9238f8f09818a89559828d2b0cb09984,0x722a8b78f73418e4b779373b48e4b648c90591a0dd9e71c4,0xb1e25e35ab20b1d303a8f77609d09e257183240a8d33da90,0x9f10169f05453c89eb2e25479ec1e301593125c9890a3930,0x945b1f932b1b9888acaaa68e5e0b46b4739f0189ef1e49f2,0x3926f29d390624b90494695e8ef2600a798a98595c178903,0xa9f1aeb4973e77fa9e4b51c348b19960849fa5c1c0a6424f,0x675a5e60aa63a62376a66aa919a7656f9aada9d4b8aa037c,0xa694b42a4a5b38e0c4a6860748aaac4876781a9379606488,0x1bda614b1a6c]
private def selTable : Array (Array ℕ) := #[selTable0,selTable1,selTable2,selTable3,selTable4,selTable5,selTable6,selTable7,selTable8,selTable9,selTable10]
private def sel (q : ℕ) :=
  let chunk := selTable[(q/16)/16]?.getD #[]
  ((chunk[(q/16)%16]?.getD 0) >>> (12*(q%16))) % 4096
private def bases0 : Array ℕ := #[0x1701100b005,0x1e01a01801401200e006002,0x3002d02c02b,0x2302101f,0x2b025,0x5205104c04b,0x4b04a049045044043,0x5e05d05c05205105004604504404003f03e,0x7106e06d065062061,0x7707307106d065061,0x7207107006f06d,0x1000d,0x1101000f005004003,0x3503402f02e023022,0x2a029027026,0x3603503403102402302201f]
private def bases1 : Array ℕ := #[0x52,0x5f05e05c05b059058056055,0x59058057056053052051050,0x6c06b069066065063,0x83080077074065062,0x7d07c07907707607306b06a067,0x18016014006004002,0x1d01b01a01900b009008007,0x1801601500c00a009,0x3b03a038035034032029028026,0x3c03b03903703002f02d02b,0x5e05c04c04a04604404003e,0x5a05905505405304f04e04d04904204103d,0x4c04a049,0x83081065063,0x7807707606c06b06a]
private def bases2 : Array ℕ := #[0x8107b07506f069063,0x3001,0xc008007,0x1201101000e00d00c00b00a008007,0x3c03703002b02401f,0x3603403102a028025,0x57056045044,0x5905705604103f03e,0x6005d054051,0x6c069068,0x8408208007f06c06a068067,0x7e07d07c07b07a07207107006f06e,0x1e01d01a006005002,0x18017014013,0x1c01b01901601501301000f00d,0x3c03a024022]
private def bases3 : Array ℕ := #[0x38037026025,0x36035,0x48047046044,0x5c050044,0x4204003f03d,0x5905805705504d04c04b049,0x7e07d07c07b,0x8208108007f07c07b07a079,0x78077075074073,0x8408107f07e07b07907807507307206f06d,0x8406003c01e,0x191089,0x10e10a08a086,0x10e10b10a109006003002001,0x19118f18d089087085005003001,0x85001]
private def bases4 : Array ℕ := #[0x19018f10c10b088087,0x10b10a109,0x88087086,0x19118e18d10d10a109,0x19118d,0x6005004003001,0x3a039d298295,0x31d31c31b215214213,0x3a13a031d31c299298,0x216215213212,0x29a299298295,0x31c298214,0x31d31c31a319,0x31d31c31b31a299298297296,0x3a23a139f31e31d31b,0x3a139e215212]
private def bases5 : Array ℕ := #[0x299298295215214211,0x4aa4a84a6,0x52d52b52a529,0x5b25b05af52e52c52b4aa4a84a7,0x4a94a84a6425424422,0x52e52d52b529426425423421,0x52c52a4a84a6,0x426425421,0x5b05ae5ad4a84a64a5,0x52d52b4a94a7425423,0x5b25b15b052e52d52c,0x5af423,0x7bf7bd6b76b5,0x7c27be7bd73e73a7396ba6b66b5,0x73e73d73c73a739,0x6ba6b5636631]
private def bases6 : Array ℕ := #[0x7c27c07bd73e73c739,0x73b73a633632,0x7c17bf7be635633632,0x636633,0x7c27bf7be,0x6ba6b86b66b5,0x73e73d73c73b73a6ba6b96b86b76b6636635634633632,0xa56a55a529d29d19ce,0xa56a55a52a51,0x9d09cf9cd94c94b949,0x94e94c8ca8c8,0xa52a519ce9cd94a9498c68c5,0x8ca8c9846845,0x9d29d19d09ce846845844842,0xa5294a8c6842,0xa56a54a53a5194e94c94b949]
private def bases7 : Array ℕ := #[0x94d94c94b949,0x9d29d19d09cf8ca8c98c88c7846845844843,0x844843842841,0x8ca8c98c78c68c5,0x9d29cf9cd,0xa567c25b23a2192,0x19f19919318d09709108b085,0x12111b11510909d097091085,0x13302b,0x1ab0a301f,0xaf0a902b025,0x1db1d51571510d30cd,0x15114b,0xdf0d30c70c1,0x1f91ed175169,0x1ff1f91ed]
private def bases8 : Array ℕ := #[0x6d,0x3a92a1,0x32531921d211,0x3cd3c73bb3493433372c52bf2b3,0x235,0x2c52b3,0x3672e325f,0x37336d,0x36d3672e92e3,0x4033fd37f379,0x41b40f3fd28f283271,0x30d3072fb289283277,0x4b74a5,0x54152f,0x5bf5b353b52f4b74ab,0x4db4d54c9457451445]
private def bases9 : Array ℕ := #[0x55f55345744b,0x58357156b5654ff4ed4e74e1,0x47546f46945d,0x5f54ed,0x5a758952350549f481,0x61f61359b58f,0x62b62561f61961360d49f49949348d487481,0x7bd6b5,0x7c373f6bb,0x74573f,0x6eb6df6d366765b64f,0x7ed7e176975d,0x78d77b685673,0x8117f968566d,0x68b67f,0x823]
private def bases10 : Array ℕ := #[0x73371b,0x7b17a572d7216a969d,0xa69a519e59cd,0xa63,0x9e59df9d996195b955,0x97f9678fb8e3,0xa87a75a039f197f96d8fb8e9,0x8f5871,0xa0f883,0xaaba9fa939a399798b91f91390789b88f883,0xa8d985,0x99d991,0xa4593d8b9,0x8bf8b9,0x937,0xa4ba45a3fa39]
private def bases11 : Array ℕ := #[0xacfaaba87a6983b8177f37d562b6075e35c541b3f73d33b520b1e71c31a5]
private def bases : Array (Array ℕ) := #[bases0,bases1,bases2,bases3,bases4,bases5,bases6,bases7,bases8,bases9,bases10,bases11]
private def ones0 : Array ℕ := #[0x1001001001,0x1001001001001001001001,0x1001001001,0x1001001,0x1001,0x1001001001,0x1001001001001001,0x1001001001001001001001001001001001,0x1001001001001001,0x1001001001001001,0x1001001001001,0x1001,0x1001001001001001,0x1001001001001001,0x1001001001,0x1001001001001001001001]
private def ones1 : Array ℕ := #[0x1,0x1001001001001001001001,0x1001001001001001001001,0x1001001001001001,0x1001001001001001,0x1001001001001001001001001,0x1001001001001001,0x1001001001001001001001,0x1001001001001001,0x1001001001001001001001001,0x1001001001001001001001,0x1001001001001001001001,0x1001001001001001001001001001001001,0x1001001,0x1001001001,0x1001001001001001]
private def ones2 : Array ℕ := #[0x1001001001001001,0x1001,0x1001001,0x1001001001001001001001001001,0x1001001001001001,0x1001001001001001,0x1001001001,0x1001001001001001,0x1001001001,0x1001001,0x1001001001001001001001,0x1001001001001001001001001001,0x1001001001001001,0x1001001001,0x1001001001001001001001001,0x1001001001]
private def ones3 : Array ℕ := #[0x1001001001,0x1001,0x1001001001,0x1001001,0x1001001001,0x1001001001001001001001,0x1001001001,0x1001001001001001001001,0x1001001001001,0x1001001001001001001001001001001001,0x1001001001,0x1001,0x1001001001,0x1001001001001001001001,0x1001001001001001001001001,0x1001]
private def ones4 : Array ℕ := #[0x1001001001001001,0x1001001,0x1001001,0x1001001001001001,0x1001,0x1001001001001,0x1001001001,0x1001001001001001,0x1001001001001001,0x1001001001,0x1001001001,0x1001001,0x1001001001,0x1001001001001001001001,0x1001001001001001,0x1001001001]
private def ones5 : Array ℕ := #[0x1001001001001001,0x1001001,0x1001001001,0x1001001001001001001001001,0x1001001001001001,0x1001001001001001001001,0x1001001001,0x1001001,0x1001001001001001,0x1001001001001001,0x1001001001001001,0x1001,0x1001001001,0x1001001001001001001001001,0x1001001001001,0x1001001001]
private def ones6 : Array ℕ := #[0x1001001001001001,0x1001001001,0x1001001001001001,0x1001,0x1001001,0x1001001001,0x1001001001001001001001001001001001001001001,0x1001001001001001,0x1001001001,0x1001001001001001,0x1001001001,0x1001001001001001001001,0x1001001001,0x1001001001001001001001,0x1001001001,0x1001001001001001001001]
private def ones7 : Array ℕ := #[0x1001001001,0x1001001001001001001001001001001001,0x1001001001,0x1001001001001,0x1001001,0x1001001001001,0x1001001001001001001001,0x1001001001001001001001,0x1001,0x1001001,0x1001001001,0x1001001001001001,0x1001,0x1001001001,0x1001001001,0x1001001]
private def ones8 : Array ℕ := #[0x1,0x1001,0x1001001001,0x1001001001001001001001001,0x1,0x1001,0x1001001,0x1001,0x1001001001,0x1001001001,0x1001001001001001,0x1001001001001001,0x1001,0x1001,0x1001001001001001,0x1001001001001001]
private def ones9 : Array ℕ := #[0x1001001001,0x1001001001001001001001,0x1001001001,0x1001,0x1001001001001001,0x1001001001,0x1001001001001001001001001001001001,0x1001,0x1001001,0x1001,0x1001001001001001,0x1001001001,0x1001001001,0x1001001001,0x1001,0x1]
private def ones10 : Array ℕ := #[0x1001,0x1001001001001001,0x1001001001,0x1,0x1001001001001001,0x1001001001,0x1001001001001001001001,0x1001,0x1001,0x1001001001001001001001001001001001,0x1001,0x1001,0x1001001,0x1001,0x1,0x1001001001]
private def ones11 : Array ℕ := #[0x1001001001001001001001001001001001001001001001001001001001]
private def ones : Array (Array ℕ) := #[ones0,ones1,ones2,ones3,ones4,ones5,ones6,ones7,ones8,ones9,ones10,ones11]

private def shiftedCode (p delta : ℕ) :=
  ((bases[p/16]?.getD #[])[p%16]?.getD 0)+delta*((ones[p/16]?.getD #[])[p%16]?.getD 0)
private def code (j : ℕ) :=
  let k := sel j
  if k<1239 then shiftedCode (k/21) ((k%21)*132)
  else if k<2537 then shiftedCode (59+(k-1239)/22) (((k-1239)%22)*6)
  else shiftedCode (118+(k-2537)/6) ((k-2537)%6)
private def chosen (j : ℕ) := chooseCol 21 22 6 59 (by decide) (by decide) (by decide) (by decide) (sel j)
private def rowF (i : ℕ) := fwd i % 2772
/-- The selected geometric tangent columns in Markowitz row order. -/
def column (j : ℕ) := supportWord 2772 rowF 20 (code j)

private def valid (j : ℕ) : Bool :=
  (((fwd ((bwd j)%2772))%2772 == j) && ((bwd ((fwd j)%2772))%2772 == j)) &&
    (supportWord 2772 id 20 (code j) == wordColumn 21 22 6 points (chosen j))

def window (f : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => window f start n && f (start+n)

def Before (f : ℕ → Bool) (b : ℕ) := ∀ i < b, f i = true

lemma before_zero (f : ℕ → Bool) : Before f 0 := fun _ h => by omega

lemma extend {f : ℕ → Bool} {b n : ℕ} (earlier : Before f b) (h : window f b n = true) :
    Before f (b+n) := by
  induction n with
  | zero => simpa using earlier
  | succ n ih =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
    intro i hi
    by_cases h' : i < b+n
    · exact ih h₁ i h'
    · have he : i=b+n := by omega
      exact he ▸ h₂

structure RowWindow (f : ℕ → Bool) (n : ℕ) : Type where
  verified : Before f n

def start (f : ℕ → Bool) : RowWindow f 0 := ⟨before_zero f⟩

def nextWindow {f : ℕ → Bool} {b : ℕ} (prev : RowWindow f b) (n : ℕ)
    (h : window f b n = true) : RowWindow f (b+n) := ⟨extend prev.verified h⟩

private def proof0 : RowWindow valid 0 := start valid
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof32 : RowWindow valid 32 := nextWindow proof0 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof64 : RowWindow valid 64 := nextWindow proof32 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof96 : RowWindow valid 96 := nextWindow proof64 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof128 : RowWindow valid 128 := nextWindow proof96 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof160 : RowWindow valid 160 := nextWindow proof128 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof192 : RowWindow valid 192 := nextWindow proof160 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof224 : RowWindow valid 224 := nextWindow proof192 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof256 : RowWindow valid 256 := nextWindow proof224 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof288 : RowWindow valid 288 := nextWindow proof256 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof320 : RowWindow valid 320 := nextWindow proof288 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof352 : RowWindow valid 352 := nextWindow proof320 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof384 : RowWindow valid 384 := nextWindow proof352 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof416 : RowWindow valid 416 := nextWindow proof384 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof448 : RowWindow valid 448 := nextWindow proof416 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof480 : RowWindow valid 480 := nextWindow proof448 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof512 : RowWindow valid 512 := nextWindow proof480 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof544 : RowWindow valid 544 := nextWindow proof512 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof576 : RowWindow valid 576 := nextWindow proof544 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof608 : RowWindow valid 608 := nextWindow proof576 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof640 : RowWindow valid 640 := nextWindow proof608 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof672 : RowWindow valid 672 := nextWindow proof640 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof704 : RowWindow valid 704 := nextWindow proof672 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof736 : RowWindow valid 736 := nextWindow proof704 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof768 : RowWindow valid 768 := nextWindow proof736 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof800 : RowWindow valid 800 := nextWindow proof768 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof832 : RowWindow valid 832 := nextWindow proof800 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof864 : RowWindow valid 864 := nextWindow proof832 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof896 : RowWindow valid 896 := nextWindow proof864 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof928 : RowWindow valid 928 := nextWindow proof896 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof960 : RowWindow valid 960 := nextWindow proof928 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof992 : RowWindow valid 992 := nextWindow proof960 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1024 : RowWindow valid 1024 := nextWindow proof992 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1056 : RowWindow valid 1056 := nextWindow proof1024 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1088 : RowWindow valid 1088 := nextWindow proof1056 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1120 : RowWindow valid 1120 := nextWindow proof1088 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1152 : RowWindow valid 1152 := nextWindow proof1120 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1184 : RowWindow valid 1184 := nextWindow proof1152 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1216 : RowWindow valid 1216 := nextWindow proof1184 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1248 : RowWindow valid 1248 := nextWindow proof1216 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1280 : RowWindow valid 1280 := nextWindow proof1248 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1312 : RowWindow valid 1312 := nextWindow proof1280 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1344 : RowWindow valid 1344 := nextWindow proof1312 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1376 : RowWindow valid 1376 := nextWindow proof1344 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1408 : RowWindow valid 1408 := nextWindow proof1376 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1440 : RowWindow valid 1440 := nextWindow proof1408 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1472 : RowWindow valid 1472 := nextWindow proof1440 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1504 : RowWindow valid 1504 := nextWindow proof1472 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1536 : RowWindow valid 1536 := nextWindow proof1504 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1568 : RowWindow valid 1568 := nextWindow proof1536 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1600 : RowWindow valid 1600 := nextWindow proof1568 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1632 : RowWindow valid 1632 := nextWindow proof1600 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1664 : RowWindow valid 1664 := nextWindow proof1632 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1696 : RowWindow valid 1696 := nextWindow proof1664 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1728 : RowWindow valid 1728 := nextWindow proof1696 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1760 : RowWindow valid 1760 := nextWindow proof1728 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1792 : RowWindow valid 1792 := nextWindow proof1760 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1824 : RowWindow valid 1824 := nextWindow proof1792 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1856 : RowWindow valid 1856 := nextWindow proof1824 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1888 : RowWindow valid 1888 := nextWindow proof1856 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1920 : RowWindow valid 1920 := nextWindow proof1888 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1952 : RowWindow valid 1952 := nextWindow proof1920 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof1984 : RowWindow valid 1984 := nextWindow proof1952 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2016 : RowWindow valid 2016 := nextWindow proof1984 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2048 : RowWindow valid 2048 := nextWindow proof2016 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2080 : RowWindow valid 2080 := nextWindow proof2048 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2112 : RowWindow valid 2112 := nextWindow proof2080 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2144 : RowWindow valid 2144 := nextWindow proof2112 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2176 : RowWindow valid 2176 := nextWindow proof2144 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2208 : RowWindow valid 2208 := nextWindow proof2176 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2240 : RowWindow valid 2240 := nextWindow proof2208 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2272 : RowWindow valid 2272 := nextWindow proof2240 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2304 : RowWindow valid 2304 := nextWindow proof2272 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2336 : RowWindow valid 2336 := nextWindow proof2304 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2368 : RowWindow valid 2368 := nextWindow proof2336 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2400 : RowWindow valid 2400 := nextWindow proof2368 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2432 : RowWindow valid 2432 := nextWindow proof2400 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2464 : RowWindow valid 2464 := nextWindow proof2432 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2496 : RowWindow valid 2496 := nextWindow proof2464 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2528 : RowWindow valid 2528 := nextWindow proof2496 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2560 : RowWindow valid 2560 := nextWindow proof2528 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2592 : RowWindow valid 2592 := nextWindow proof2560 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2624 : RowWindow valid 2624 := nextWindow proof2592 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2656 : RowWindow valid 2656 := nextWindow proof2624 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2688 : RowWindow valid 2688 := nextWindow proof2656 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2720 : RowWindow valid 2720 := nextWindow proof2688 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2752 : RowWindow valid 2752 := nextWindow proof2720 32 (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
private def proof2772 : RowWindow valid 2772 := nextWindow proof2752 20 (by decide +kernel)

theorem spans_of_column_surjective
    (surj : Function.Surjective (Matrix.mulVec (fun (i j : Fin 2772) => fieldBit ((column j.val).testBit i.val)))) :
    CriticalTensor.Spans 6 21 22 59 := by
  have good (i : Fin 2772) := proof2772.verified i.val i.isLt
  have turns (i : Fin 2772) := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (good i)).1
  let p : Fin 2772 ≃ Fin 2772 := fromTables (by decide) fwd bwd
    (fun i => beq_iff_eq.mp (turns i).1) (fun i => beq_iff_eq.mp (turns i).2)
  let rows := (rowOrder 21 22 6).trans p
  apply spans_of_selected points (fun j : Fin 2772 => chosen j.val) rows column _ surj
  intro row j
  have same := beq_iff_eq.mp (Bool.and_eq_true_iff.mp (good j)).2
  change (supportWord 2772 rowF 20 (code j.val)).testBit (p (rowOrder 21 22 6 row)).val = _
  rw [supportWord_read (by decide : 0<2772) p rowF (fun _ => rfl),same]

end CriticalTensor.Base21Normal

namespace PackedGauss

/-- The lowest bit represents row zero. -/
def bit (b : Bool) : ZMod 2 := if b then 1 else 0

def decode (height w : ℕ) (i : Fin height) : ZMod 2 := bit (w.testBit i.val)

private lemma decode_zero (height : ℕ) : decode height 0=0 := by funext i; simp [decode,bit]

private lemma decode_xor (height w z : ℕ) : decode height (w ^^^ z)=decode height w+decode height z := by
  funext i
  change bit ((w ^^^ z).testBit i.val)=bit (w.testBit i.val)+bit (z.testBit i.val)
  rw [Nat.testBit_xor]
  cases w.testBit i.val <;> cases z.testBit i.val <;> decide

end PackedGauss
namespace PackedGauss

/-- Unpack the positions set in a sparse column. Digits are one plus the
zero-based indices, least significant digit first. -/
def indexMask (digits : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | fuel+1,code =>
    if code=0 then 0 else
      let i := (code % (1 <<< digits))-1
      (1 <<< i) ||| indexMask digits fuel (code >>> digits)

/-- Reconstruct the j-th unit lower-triangular pivot in direct row order. -/
def pivotWord (digits height j code : ℕ) : ℕ :=
  (1 <<< j) ||| indexMask digits height code

/-- Replay only earlier columns. A reference outside the permitted prefix
terminates the replay, so a purported certificate cannot introduce an
unjustified column. -/
def replay (digits bound : ℕ) (pivot : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,x,_ => x
  | fuel+1,x,code =>
    if code=0 then x else
      let k := (code % (1 <<< digits))-1
      if k < bound then replay digits bound pivot fuel (x ^^^ pivot k) (code >>> digits) else x

def lowerFit (w j : ℕ) : Bool := w.testBit j && (w % (2^j)==0)

/-- Check one factor column, including its diagonal pivot and its support
below the diagonal. Checks for different columns are independent. -/
def columnOK (digits : ℕ) (column pivot upper : ℕ → ℕ) (j : ℕ) : Bool :=
  (replay digits j pivot j (column j) (upper j)==pivot j) && lowerFit (pivot j) j

def windowOK (digits : ℕ) (column pivot upper : ℕ → ℕ) (offset len : ℕ) : Bool :=
  (List.range len).all (fun j => columnOK digits column pivot upper (offset+j))

def BeforeLU (digits : ℕ) (column pivot upper : ℕ → ℕ) (last : ℕ) : Prop :=
  ∀ j < last, columnOK digits column pivot upper j=true

lemma beforeLU_zero (digits : ℕ) (column pivot upper : ℕ → ℕ) : BeforeLU digits column pivot upper 0 :=
  fun _ bad => by omega

lemma extendLU {digits : ℕ} {column pivot upper : ℕ → ℕ} {offset len : ℕ}
    (before : BeforeLU digits column pivot upper offset)
    (checked : windowOK digits column pivot upper offset len=true) :
    BeforeLU digits column pivot upper (offset+len) := by
  intro j hj
  by_cases old : j < offset
  · exact before _ old
  have h := List.all_eq_true.mp checked (j-offset) (List.mem_range.mpr (by omega))
  simpa only [show offset+(j-offset)=j by omega] using h

private lemma replay_mem {h : ℕ} {S : Submodule (ZMod 2) (Fin h → ZMod 2)}
    (digits bound : ℕ) (pivot : ℕ → ℕ) (prev : ∀ k < bound, decode h (pivot k)∈S)
    (fuel x code : ℕ) (hx : decode h x∈S) : decode h (replay digits bound pivot fuel x code)∈S := by
  induction fuel generalizing x code with
  | zero => exact hx
  | succ n ih =>
    rw [replay]
    split
    · exact hx
    dsimp only
    split
    · apply ih
      rw [decode_xor]
      exact S.add_mem hx (prev _ (by assumption))
    · exact hx

private lemma lower_zero {w i j : ℕ} (good : lowerFit w j=true) (hij : i < j) : w.testBit i=false := by
  have h := congrArg (fun x : ℕ => x.testBit i) (beq_iff_eq.mp (Bool.and_eq_true_iff.mp good).2)
  simpa only [Nat.testBit_mod_two_pow,decide_eq_true hij,Bool.true_and,Nat.zero_testBit] using h

/-- A sparse LU certificate proves full binary rank, with independent
checks per selected column. Only the packed geometric columns enter the
resulting matrix. -/
theorem surjective_of_LU (h digits : ℕ) (column pivot upper : ℕ → ℕ)
    (good : ∀ j : Fin h, columnOK digits column pivot upper j.val=true) :
    Function.Surjective (Matrix.mulVec (fun (i j : Fin h) => bit ((column j.val).testBit i.val))) := by
  classical
  let M : Matrix (Fin h) (Fin h) (ZMod 2) := fun i j => decode h (column j.val) i
  let S := Submodule.span (ZMod 2) (Set.range M.col)
  have contains (j : ℕ) (hj : j < h) : decode h (pivot j)∈S := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      have checked := (Bool.and_eq_true_iff.mp (good ⟨j,hj⟩)).1
      have v : decode h (column j)∈S := Submodule.subset_span ⟨⟨j,hj⟩,rfl⟩
      have w := replay_mem digits j pivot (fun k hk => ih k hk (by omega)) j (column j) (upper j) v
      rwa [beq_iff_eq.mp checked] at w
  let L : Matrix (Fin h) (Fin h) (ZMod 2) := fun i j => decode h (pivot j.val) i
  have shape (j : Fin h) : lowerFit (pivot j.val) j.val=true := (Bool.and_eq_true_iff.mp (good j)).2
  have tri : L.IsLowerTriangular := by
    intro i j hi
    change i.val < j.val at hi
    change bit ((pivot j.val).testBit i.val)=0
    rw [lower_zero (shape j) hi]
    rfl
  have det : L.det≠0 := by
    rw [Matrix.det_of_isLowerTriangular L tri]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    change bit ((pivot i.val).testBit i.val)≠0
    rw [(Bool.and_eq_true_iff.mp (shape i)).1]
    exact one_ne_zero
  have onto : Function.Surjective L.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr det))
  have le : LinearMap.range L.mulVecLin ≤ S := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact contains j.val j.isLt
  rw [LinearMap.range_eq_top.mpr onto] at le
  change Function.Surjective M.mulVecLin
  apply LinearMap.range_eq_top.mp
  rw [Matrix.range_mulVecLin]
  exact top_unique le

end PackedGauss

namespace CriticalTensor.Base21NormalData

private def lowerPage : ℕ → Array ℕ
  | 0 => #[0x385233232045, 0, 0x6142bd2af20a06d, 0x95a61420f20b06d, 0x6942fc2f10a103f, 0, 0, 0x9a472d5443571770d90a7, 0x9fb73471936335b35a0a8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x6b567567467365b65a6592f42f22eb1690a103f03e, 0x8bd6742eb, 0x2f42f22f10a1, 0x23e04b]
  | 2 => #[0x1271261250f8, 0x46545924a, 0x7c63bf, 0x7c646e193, 0x23a236235233232, 0x42b2f9047, 0x2f9256, 0x76941141011e049, 0x41024b, 0x43c43b078, 0x4532030fb0fa04c, 0x452203, 0x88387a4ae1160fb, 0x87a75d5c21170c7, 0x7d54b1460, 0x84563e52a2a8, 0x272270204, 0x26f26e0c9, 0x76d4ae373246054, 0x373055, 0x75e5c20c6, 0x91c27c27b, 0x4bc47a226, 0x58c58b58a, 0x91c4bc30322612d, 0x28528405b, 0x3ef07c05c, 0x49447c29f29e29d29b05d, 0x7a94943ef3ee1a71a41a3, 0x90177828d, 0x9074cc4cb, 0xac3ac15f7]
  | 3 => #[0x90841428e, 0x90841428e, 0x94b91f91b48b27e, 0x2a3, 0x7fc272204, 0x297134067, 0xa15996650253, 0x92275c308229228, 0x945778131, 0x47d, 0x9b37fb0cd0cc06c, 0x9aa7fb48a26e0c9, 0x61420e, 0x9a741a21d, 0x7a720e, 0x915, 0x63314307f, 0x9238206024993ed, 0x2bf, 0xa228f649e2d013b, 0x799636082, 0x7991bd1bc147146, 0x128, 0x749, 0x224, 0x492, 0x9b2, 0x7a9, 0xa06, 0xa0a, 0x631, 0xa1b]
  | 4 => #[0x615, 0x7d57305284b14602a7, 0x153, 0xa17, 0x8fd, 0x6f8, 0x6a9, 0x522, 0xa42, 0xa45, 0xf6, 0x74e, 0xa7b, 0x110, 0x57e, 0x481, 0x199, 0x194, 0x4e0, 0x3eb, 0x8f5, 0x2cb, 0x178, 0x320, 0x5a45962d72d6159157, 0x96666a329, 0x6d464e2e6, 0x1c8, 0x31f, 0x331, 0x972, 0x75e75d5c237224621e0c5]
  | 5 => #[0x65a50d4044032f2, 0x9633283272140d6, 0x65852d528, 0xa5, 0x855332331181180, 0x35a3530a8, 0x5443571e3, 0x9e899c71c71b35b, 0x72a6a3, 0x9e39a472b72a0db, 0x97e82f77e77d77c2ea2e9, 0x87f, 0x55b, 0x35e, 0xb0, 0xb2, 0x3690dd, 0xa76, 0x45f, 0, 0x10e, 0x9b4, 0x4c5, 0x80d, 0x13c, 0x92e, 0x2c5, 0x154, 0x506, 0x6c4, 0x34b, 0xca]
  | 6 => #[0x90e, 0, 0x8a1, 0x277, 0x21f, 0xe7, 0x75e, 0x87a, 0x26f, 0x85117f17e17a179, 0x1a2, 0x7fb, 0x9b3, 0xa23, 0, 0x9cc, 0x2c8, 0x4d3, 0x8fe, 0x66d, 0x8b3, 0xa1e, 0x1e4, 0xa3d, 0x1e3, 0x854, 0x72d, 0x684, 0, 0xa87, 0x9bb, 0xa77]
  | 7 => #[0x89d, 0xfb, 0, 0xf9, 0x115, 0x116, 0x87a, 0xa82, 0x7f6, 0x7d5, 0x11b, 0x45b, 0x7f7, 0x769, 0x454, 0x7c8, 0x7c7, 0x468, 0x476, 0x469, 0x6cc, 0x74e, 0x74d, 0x74f, 0x87d, 0, 0, 0, 0x87d, 0x851, 0xa40, 0x372]
  | 8 => #[0x754, 0x31d, 0x380, 0x57b, 0x383, 0x74b, 0x384, 0x385, 0x38e, 0x3c7, 0x388, 0x45e, 0x7f5, 0x684, 0xa87, 0x9bb, 0xa81, 0xa77, 0x431, 0x89d, 0x749, 0x749, 0x87a, 0xa82, 0x7f6, 0x7d5, 0x57c, 0x45b, 0x7f7, 0x769, 0x454, 0x7c8]
  | 9 => #[0x6cc1fe124122, 0x6cc123, 0x266264263124, 0x45142d399398, 0xa7989d751126, 0x36936822c127, 0x44d37f376, 0x87f, 0x476, 0x469, 0x576, 0x376, 0x27b, 0xa2d, 0x770, 0x78a, 0x901, 0x286, 0x80b, 0x297, 0x468, 0xa2d, 0x9a7, 0x4dc, 0x9a7, 0x924, 0x8ee, 0x915, 0x4d5, 0x60a, 0x916, 0x4e3]
  | 10 => #[0x20d, 0x9cb, 0x81c, 0x4e9, 0x63f, 0xa5d, 0x955, 0x509, 0xa24, 0x81b, 0xaa7, 0xaa9, 0x82e, 0xab3, 0x82d, 0xab1, 0x8d1, 0x5a6, 0x515, 0x1c2, 0x3b2, 0x596, 0x516, 0x5a4, 0x599, 0xa08, 0x520, 0x15d, 0xa1b88e6d2, 0xa19, 0xa1b, 0x8fe]
  | 11 => #[0x8da, 0x94f, 0x984, 0x3f1, 0x950, 0x98d, 0x1d2, 0x94e, 0x65b, 0x16d, 0, 0x6b5, 0x6b5, 0x836, 0x6b7, 0x8c1, 0x65c, 0x6ca, 0x1c3, 0x175, 0x596320178, 0xa44, 0xa44, 0x59651a5152d52d4, 0x866, 0x97d, 0x79e, 0x84e, 0x704, 0x866, 0x97d, 0x330]
  | 12 => #[0x6f1, 0x7c7, 0x437, 0x455, 0, 0x46c, 0x747, 0x882, 0x884, 0x882, 0x7d3, 0x38f, 0x438, 0x7ef, 0x390, 0x952, 0x7d3, 0x7ad, 0x42c, 0x481, 0x80e, 0x809, 0xa2d, 0x80e, 0x80b, 0xa2d, 0x770, 0x288, 0x205, 0x770, 0x7a6, 0x26d]
  | 13 => #[0x7fc, 0x26d, 0x483, 0x7a9, 0x1a7, 0x786, 0x9ac5cf489207, 0x902, 0x947, 0x904, 0x948, 0x953, 0x904, 0, 0x92e, 0x8e3, 0x92e, 0x918, 0x496, 0x497, 0x8f3, 0x3ad, 0x932, 0x4d0, 0x931, 0x930, 0x936, 0x30a, 0xa28, 0xa68, 0x955, 0x505]
  | 14 => #[0x4a3, 0x6c4, 0x1c7, 0x1c7, 0x6c2, 0x6c4, 0, 0x6c3, 0x58e, 0x594, 0x6c3, 0x50f, 0x590, 0x5a6, 0x53d, 0x951, 0, 0x98d, 0x8ba, 0x8d1, 0x401, 0x8d1, 0x8d2, 0x402, 0x8db, 0x8cf, 0x868, 0x546, 0xa44, 0x1df, 0x868546, 0]
  | 15 => #[0, 0x9e5, 0x561, 0xa3d, 0x85b, 0xa8f, 0xa6e, 0x85a, 0x859, 0x568, 0x7b0, 0xa9d, 0x717, 0x842, 0x843, 0x7b2, 0x9d1, 0x3cc, 0xa96, 0xa91, 0xa0e, 0x3cd, 0x86b, 0x899, 0x9de, 0x5ba, 0x9eb, 0x9d8, 0x9ea, 0x36d266, 0x9b83da, 0x26b26a]
  | 16 => #[0, 0x7a9, 0x453452, 0x271270, 0x77026d, 0x9b09ac, 0x7fc7a6, 0x2af20d, 0x20d, 0x60c, 0x6132bd, 0x8fa8f8, 0x9c6, 0x7a7, 0x9c62cd, 0xa08511, 0xa18a13, 0xa1a678, 0x326214, 0xa13, 0x6a033a, 0x84b791, 0x5b7, 0xa48714, 0, 0x56221b, 0x542, 0x37d37c, 0x7e379761e6195054a34a14a041a30a2c2, 0x372220, 0x882747576220, 0x87d372]
  | 17 => #[0x87f754370, 0x378316223, 0x7f07d57d4378377316, 0x87f, 0x4b2393, 0x582304, 0x944907, 0x9904cf, 0x94a5d5, 0x955509, 0xa68955, 0x74d3b836c369368265, 0x57b37c22e, 0x57c4b239337d25b, 0x7ed7ec7eb74b, 0x7f87f276937a, 0x385233, 0x47244e233, 0x3c738523b, 0x23a235, 0x38e23a237236, 0x7c87c447123a, 0x46e46a44242c38e, 0x47244c38523b, 0x38e38d23b23a, 0x3c738e38c, 0x47238e38b385, 0x38b38a389387, 0x47245e44e44d, 0x87d87b, 0x7ee7d5458, 0x7ef7ad25a]
  | 18 => #[0xa788b78a5451398, 0xa797514c8432243, 0x886751, 0x87f76d75e75d436, 0x436435434, 0x75d5c2, 0x76175b75a, 0x88176075f, 0x7f176243e, 0x7ed7ec64d465463441, 0x7f47f325c, 0x4454443f424e24d, 0x7c47574713f3257, 0x7c53f53f2, 0x75647e45d44f386, 0x47e46a467, 0x7494ad253, 0x7494ae253, 0x88274a4ad43a, 0x7f6768767, 0xa9975c5294a3, 0xa03257, 0x7c97c84794704693f5386, 0x764473446, 0x7f525b, 0x7f5, 0x57b, 0x952390, 0x98d950, 0x98130c, 0x98230f, 0x993983]
  | 19 => #[0x78b311, 0xa98313, 0xa80a7ea7b74e42e265264, 0x266265, 0xa7674e369266, 0x6cc3b836d36c36b, 0x77776c76b, 0xa2c9439424b7269, 0x9423e9, 0x48827526b, 0x278277272271, 0x48a26f, 0, 0x9b35ed26f, 0x7a948a273270, 0x273271, 0x7a948a272, 0x76f278273, 0x9af770, 0x278277276, 0x488, 0x9ad771277, 0x9ab5d15cf48a278, 0xacb4be4b9, 0x7724ba27a, 0x9064bb4ba, 0x908778, 0x90841528e, 0x49347d, 0x4be41227f, 0x5885824be, 0xac69c46d9]
  | 20 => #[0x4c74823e23a1283, 0x943942809808482283, 0x93e93c80c8065cb4c6482, 0x7a9286, 0, 0x7a9, 0x9b2, 0x77049447c3ef, 0x47f28b28a, 0x5f25ec47f, 0x28c, 0x9065f25ec, 0x9459087785f128e, 0x91d91c9085f1415, 0x904900889, 0x94479d4cd, 0xac3ac1a335c85c7, 0x93c5cb293, 0x806, 0x7805e83e9, 0x9af9ac, 0x29a299298, 0x29a, 0x7a9299, 0x9b229a, 0x7a9, 0x7a949229c, 0x9b19b09ae9ac5d0492, 0xa049b17715eb29e, 0x7a949229f, 0x76f47c, 0x9057832a1]
  | 21 => #[0x785784783, 0xa318115f8, 0x57f4c52a4, 0x93f7896c85e45e3, 0x7896c85e63e33a6, 0x94193f6c8, 0x94591d5f1, 0x953949948947946, 0x94b91f6dd, 0x7da69e69d, 0x9bc7fd775, 0x91560a6016004e0, 0x9166086044d53ab, 0x9248f36014e03eb, 0xa237de60b, 0x81c6154e7, 0xa23a229cc60c49e, 0x2b42b3, 0x4f04172b4, 0xa65a644f04172b5, 0xa65a644a2, 0x2b92b7, 0xa676076054182b8, 0xa6779779561f61e4182c3, 0x81b5094f3, 0xaaaaa082a7ea654, 0x9184983ed2bc, 0x9319234e34d0499, 0xa229cc618617614, 0xa239cc2c82c02bf, 0x2c62c0, 0x2c82c72c6]
  | 22 => #[0xa65a4ba2895530a, 0x79561f, 0xa679a89606e0418, 0x88c8244003fe3fd, 0x9148f581f6204dc, 0x9c68fa8ee7a7, 0xa228ee49e, 0x8fb8f88ee7a7639, 0x9a72f62ca, 0x63b63a4f6, 0x92b91562c60a2cc, 0x92c62d62c, 0x95a8ef8ee6324d3, 0x9cb6502cf, 0x958634631, 0x9c695c95a8ee, 0x95f63f635, 0xa69a66a2495e63f, 0xab6a6ba5e9a86e1, 0x5a4517516515514, 0x5a351a519, 0x519517516, 0x664663599, 0xa1ba109618fe520, 0xa1d9618fe5112fb, 0x6d76d43f1, 0x8bd67465b, 0x8db8d16b5, 0x6b74232de, 0x8db8d16ca65f65e65d, 0x6c23b7321, 0x66466359a]
  | 23 => #[0x6c46c266459a, 0x6672e42e3, 0xa1766752251e2e4, 0xa1fa17a14, 0x83077e77c67266e, 0x6d76d464e, 0x98183082f77d77c512, 0x98183077e77d77c53e, 0x97e6c92ea, 0x64e53e, 0x8ca8c98bd894675, 0x8fe5102ed, 0xa1e8ff329, 0x8da88e67c, 0x8d96e841b2f0, 0x98b8d96ef6e852b, 0x8cc8cb8ac2f42f2, 0x8d465a2f3, 0x8c736f36e2f5, 0x8cb537535, 0x8d68d253a36f36e, 0xa62a60, 0x879394, 0xa93362, 0xab846b, 0x8ce8a9, 0xa10961, 0x8c632d, 0x32d, 0x9a65b5, 0x3df300, 0x9b88a489e3df3dd3d9]
  | 24 => #[0xa91a0e, 0x57c4b2, 0x4bc304, 0x9074cf, 0x9074cc, 0x944, 0x5d44cf, 0, 0x9215d5, 0xa68a28, 0xa624d9, 0x51230e, 0, 0x9939816d5, 0x838314, 0x315, 0x6fe312, 0x78b6fe, 0x56e352, 0x9939836d5529315, 0x9859829808386825b3, 0x37d37c37b37937831b319317, 0x31d31c31a, 0, 0x7ec7eb64d31a, 0x7f676857a, 0x7f87f276938437f, 0x7ed7eb38338238137c31d, 0x57a40f31e, 0x76257840e, 0x518322320, 0x6c46c2322321]
  | 25 => #[0x6c7, 0x6c358e51b518, 0x6c76c25a2, 0x6dc6c55ad59f59e, 0xa136e9326, 0xa139669636e9327, 0xaba9646e9, 0xa1da1ba19523521, 0xa1e8ff, 0x99398695094d94c, 0x98d9839518ba41c, 0x98f98d9518ba7cf, 0x8d28c6699, 0x98e8d06f052f, 0x83a531, 0x9a6857554, 0x9749279266f15c055b332, 0x85555354f, 0x55154f547, 0x6f2337335, 0x91189f8657233d434f34d339338337336, 0x9789103d4, 0x55354a3d03cf338, 0x3d434f339, 0xa8b9ea867, 0x8686a069f33c, 0x6a069f, 0x6a26a1, 0x6f76f56f4, 0x6fb6fa33f, 0x6fa6f86f7, 0x96a6fc341]
  | 26 => #[0x717, 0xa7078b, 0xa6c9d341d, 0x703702701, 0x34a349346, 0x426348347, 0x997545348, 0x34a349, 0x90b742407, 0x8f18ea703, 0x97b97297196f34c, 0x866856549, 0x3d435034f34e, 0x90c8de8a089572655c350, 0x96f8565543d4350, 0x8de8a06f2, 0xa3e999792, 0xa0e86b56e55a, 0x96e96d6b8, 0xa41a3f5b7, 0xa407926a4, 0xa409996a4, 0x868561546, 0xa759cf688, 0xa8e9d099b, 0x71b71935b, 0x9d571b35c, 0x9f79d69d5, 0x8aa71b56c, 0x8a489e3da, 0x8a38a2726, 0xa0199683d]
  | 27 => #[0xa459e4840, 0x732731, 0x9ff9f6738, 0x73f736735365, 0x9f673b738409366, 0x9f0850743737, 0x8f086e850737, 0xa84369, 0xa8436c36b36a, 0x74d36d36b, 0x74d3b836d36c, 0xa84a81a769bb75074e74d36d, 0xa86a7781e3b8, 0x8db8d68d28d18c753940136f, 0x98a8d95ad, 0x88274643a, 0x76e748747, 0x87d87b878373, 0x87b87a76e749, 0x754375, 0x88287f76e75e754748747376, 0x88488287f438, 0x380378, 0x37e379, 0x7f438437f37a, 0x38237f37c, 0x57b37d, 0, 0x7ed7ec7eb74b57c4b2393, 0x7ed7ec7eb64d381, 0x7f67f476857b57a384380, 0x7eb64d]
  | 28 => #[0x383382, 0x7f545b393383, 0x57c57b45b39138f, 0x7f47ed7ec74b64d, 0x7c77c646f454, 0x76576375647345d44f448447446, 0x38b38a389, 0, 0x47244d44c38a, 0x76347344642938b, 0x7c247444c4454433c738e38d38c, 0x7c77c647246f45444c3c738d, 0x7c77c646f46e46a45444e44242c38e, 0x7c53f43f33f2, 0x9527ef, 0x952, 0x577, 0x7d3, 0x7f5, 0x84c395, 0x879873, 0x997545, 0x6cc44a, 0x42d399, 0x6cc, 0xa878e0, 0x39d39c, 0x4b439e39d, 0x3e43aa39e, 0x3e23e03a239f, 0x3e53e2, 0x3a23a1]
  | 29 => #[0x3e23e03a2, 0x3e33e23a5, 0x3e63a4, 0x93e93c80c8065cb4c74c63e83e73e53e33e23e03a5, 0x3aa3a6, 0x9298e05a53df, 0x3ab3a8, 0x3ac3ab, 0x4d63b0, 0x93d76c76a3e53e43e2, 0x9236036024e34d53ac, 0x606601600, 0x936932, 0x9293af, 0x9328e37a462f3b0, 0x92f4d6, 0x3b33b2, 0x59458e3b3, 0x5923b4, 0x59258f, 0, 0x6c3, 0x6c7, 0xa87a86a778e18df81e74d6cc451, 0x74a749457, 0x76e439, 0x87c3bd, 0x87f76e, 0x87b878753, 0x7f87f5755, 0x756469454, 0x7c43c1]
  | 30 => #[0x757, 0x46f3c3, 0x7c746b, 0x7c746f, 0x3c93c8, 0x7c84683c8, 0x7c8, 0x7ca7c64694684543c9, 0x7c8468445443, 0x4853cb, 0x48547640a, 0xa96a0e, 0xa8e869, 0x5a5513, 0x54b3d0, 0x3dd3d53d2, 0x9fe3d2, 0x7226ce6cd55354c54b3de3dd3d5, 0x54d, 0x9fe, 0x3d83d6, 0x3dc3db3d7, 0x97c9758613db3d8, 0x3dc3d9, 0x3df3dd, 0x9b8, 0x97d97a9733dc, 0x97d8666d0, 0x7226ce3df3de, 0x6ce559, 0x9fe97d8667226d06ce559, 0x80e3e2]
  | 31 => #[0x3e83e5, 0xa2d80e80c807, 0x80e3e4, 0xa2d9415e5, 0x3e8, 0, 0x93e3e8, 0x94093c80b, 0x93e77f, 0x92f924, 0x92f, 0x92f820, 0x92f, 0x7703ef, 0x47c, 0x9b5, 0x94e8b9, 0x3f43f3, 0x7c4, 0x7c5, 0x471470, 0x7fa3f8, 0, 0xac67fa, 0x8037d6, 0x9c1811, 0xac0a31, 0xaa9a4a, 0xa9e954, 0x954, 0xab94f9, 0xab0aa9]
  | 32 => #[0x8db8d1, 0, 0x50c404, 0x6b5, 0x99790b, 0x545, 0x9e899c, 0x9e28e6, 0x877742, 0x47646f, 0x8ce8cd, 0xa49898, 0x7f5458, 0, 0x57a, 0x7ef577, 0x7d3460, 0x91e91c, 0x901581, 0x902585, 0x947585, 0x91d586, 0x956607, 0xa659a7, 0x9a7822, 0x960799, 0x8b4839, 0x98f52d, 0xa8fa70, 0x70f68a, 0xa75869, 0xa8f9d2]
  | 33 => #[0xa9aa97, 0x7f5461, 0x6b6424, 0x6b7534533, 0x9f38ea, 0, 0xa84449, 0x7c742c, 0x476446, 0x7c7477, 0x47542c, 0x7c7, 0x6cc451, 0xa7ea7b, 0x9a98a5, 0xa788a5, 0xa78, 0xa85759, 0x8e2, 0x87f435, 0x76075f, 0x88287f, 0x88487f, 0, 0x884, 0x74a, 0x882749, 0x884, 0x76075f, 0x76243f, 0x768767440, 0x762578]
  | 34 => #[0x465463, 0x7c746a, 0x7c2474, 0x445, 0x474, 0x763473, 0x47e448, 0x7cb7ca758, 0xa7fa76, 0x8f28e1, 0x75074e, 0x7cb45e44e44d, 0x7cb7c57c247447246e46c45e, 0x7c3756472469, 0x7c3, 0xa7ea7c89c45f, 0xa878e28e0, 0x76d75d75b75a, 0x87d87b87875b, 0x469, 0x7c9468, 0xa7a81e, 0x74a748, 0x7f07ee, 0x7ee579, 0x7ee, 0x7f7, 0x7d3, 0x7ca756, 0, 0xa7d89c, 0x9527d3]
  | 35 => #[0x9527d4, 0x7d3463, 0x9527ef465, 0, 0x577, 0x9527d3, 0x7c946a, 0, 0x7c7, 0x477, 0x7c3, 0, 0xab8, 0, 0x7c87c6, 0xa037c8, 0x7c36b4, 0x7cb7c8763476473, 0x765764476, 0x7c2476, 0x7c9477, 0, 0x765764763, 0xa036b4, 0xab8a03, 0x990582, 0x587584, 0x770494, 0x79d584, 0x7c47c2763, 0x907904, 0x80a57f]
  | 36 => #[0x80b57e, 0x93d806, 0x7a95d1, 0x9b25d1, 0x7ca7c57c2757, 0xa7ea7ca7b, 0xa2d93a8a45a6, 0x9b29ab, 0x9ab5ea, 0x9aa770, 0x94b904, 0xa305f7, 0xad05c1, 0x7795d9, 0xacf9c0, 0xacdabe, 0xaa49b7, 0x9b27a9, 0x587585, 0x9b0770, 0x80b809, 0x9188e3, 0x92e918, 0x92f8f3, 0x92f92e, 0x8f78ed, 0x8ed8e4, 0x638617, 0xa06617, 0xa229cc, 0x9c861a, 0xa63a61]
  | 37 => #[0xa63a0b, 0xa65a64, 0xa68a28, 0xaaa654, 0x61d61c, 0xa3ba39, 0xa5962b, 0xa59a4e, 0xa59a58, 0xa5961c, 0xa56a32, 0xa86a78a2e8e08df, 0xa82881749, 0x88388087a, 0xa8287c754, 0x885883880, 0x7f07ee7d4, 0x9527d357c, 0x9927f57f2, 0xa2d80f76b, 0x802782, 0x4b94b84b7, 0xa2b9b64b8, 0x94278077f4b9, 0xa2b9b680f8027fe, 0x90658c58b58a4bb, 0x91a9065ee, 0x9909229215d5582, 0x90490088958a, 0x94b94894791e91c, 0xac3ac1a309c4, 0xad18055c1]
  | 38 => #[0x69e69d4c2, 0x78777969e5dc, 0xa2c8075c34c94c4, 0x80757f4c5, 0x9b480f80a807, 0x80c8084c7, 0x93d80c808806, 0xa86a81a79a77a2e89d, 0xa2c943942, 0x9006ae58d, 0x9229075d54cf, 0x9214cf, 0x94b91f91b, 0xac4ac37d7, 0x9075d5, 0x936931, 0xa62a60, 0xab9ab4, 0xa23a22, 0xa62a60, 0x936932, 0x932930, 0x8fb638, 0x9c895b, 0xa68a28, 0x915600, 0x9154dc, 0x93192581f, 0x6014e0, 0x608606, 0, 0x60a6086046014e1]
  | 39 => #[0x9239156024e2, 0x923603, 0x936932, 0x61560d, 0x9cb615, 0x9cb9c9, 0x7de615, 0x9c995d, 0x81c, 0x637, 0x7e24ec, 0x4f34f24ee, 0x7e263f, 0x5044ef, 0x95550a509, 0xa5d509, 0x7e04f3, 0x7e14f4, 0x95d92382c81b603509, 0xa249557e150a5044f5, 0x9557e263f509, 0x9a7509, 0x7ea7e6, 0xa4a7b4, 0xaa9, 0xab3, 0x82b7e5, 0x82e, 0x9cd7e9, 0xab3, 0x827501, 0xab3]
  | 40 => #[0, 0xa4c7b8, 0xa3682c, 0xa62505, 0xa62a28, 0x5a1507, 0x508, 0x590, 0xa68955, 0xa62a28, 0x6b550c, 0x50e, 0x50e, 0x8d68d28c753a, 0x5a658e, 0x9625af, 0xa1ca18, 0x9506d3, 0x6c35a6, 0x5a1515, 0x6c25a451a517516, 0x6c05ab517, 0x6615aa519, 0x5a651b, 0x5a459659551a, 0x6c46c25a1, 0x6c76c35a65a2, 0x5ae5ac, 0x6cb6c5, 0xa15525, 0, 0xa15]
  | 41 => #[0x524523, 0, 0xa17a11524, 0x8848406335ea, 0xa21a20, 0xabaa21, 0x988892, 0x52e52d, 0x993986, 0x98c989, 0x98f7cf, 0x98f983, 0, 0x98c989, 0x98e8dd, 0x8c583a, 0x8d5, 0x538535, 0x537, 0x538535, 0x6b5537, 0x8dc7bd, 0x8d68d28c77bf7bc7b96b553a538, 0x8ce8bd8a96b767465b, 0x8d68d2, 0, 0x53e53c, 0x98197f6c9, 0x98d53e, 0x97e6c9, 0x9778a6, 0]
  | 42 => #[0x8a6, 0xa486a1, 0xa489e7, 0xa3d561, 0x9e99e8, 0xa449e5, 0x90f707, 0x9f3850, 0x9a6866, 0x54c54b, 0x9fe55354d, 0x8556f15c054f, 0x97b96f864, 0x551550, 0, 0x90f707552551, 0x864709, 0x863, 0x97b9768555c0, 0x96f856, 0xa9855a, 0xa98557, 0x78b6ff6fe68f68e558, 0x7006ff68f, 0x6cf6ce, 0xa72a71a0971856e, 0x97d927, 0x911723, 0xa4283f, 0xa427ab, 0xa42725, 0]
  | 43 => #[0x9e5854, 0x8546a1, 0xa4283f, 0x9e79d7, 0x9e6, 0x8a87b1, 0, 0xa6e85b, 0x87986c, 0x9a29a1, 0xa92728, 0x8aa729, 0x9e28e6, 0xa6da0d71770f70c68a, 0x8eb89a, 0x89b, 0x8ec8e7, 0x9e1, 0x9f38ec, 0x9ec9e0, 0xa009f5, 0x88387b, 0x9527ef, 0x7d3, 0x7f57ee, 0x7ee57d, 0x7f5, 0x7d3, 0x7f77f6, 0x80b57f, 0xa2d80e, 0x80e809]
  | 44 => #[0x91e585, 0x990944, 0x944587, 0x944, 0, 0x91e91d, 0x99091e, 0, 0x79d, 0x58c58b, 0x949794, 0x948947904, 0x91e902, 0x6c35a6, 0, 0x5a1594, 0xab9ab0, 0x5a65a5, 0x6c36bf, 0x6c3, 0x5a6596, 0x6c46c26615ad5aa5a45a059e59d59c59b59a598597, 0x6646635a3598, 0x5a059d599, 0x98d8da6ca, 0x6c4664662661, 0x6dc6cb6c5663, 0x5ad5a159d, 0x6c06bd5ad, 0x5a159f, 0x5ad5a65a15a0, 0x6bd5ad5ab5a65a1]
  | 45 => #[0x6c45a6, 0x6c76c3, 0x6c76bf, 0x6bf5a6, 0x6c36bf, 0, 0x5ae, 0x6615a9, 0x6c4662661, 0x6c4, 0x6bd6bc, 0x6c4, 0x6cb6c1, 0x6cb6c5, 0x9668fd, 0xa1e8b3, 0x8b98b4, 0x8b95b3, 0x94e8b4, 0x8b98b5, 0x9b9911, 0x898852, 0xa46898, 0x9de9d9, 0x9d9860, 0x9ec9da, 0x9eb5bf, 0x9d85be, 0x9ea5be, 0x9e0, 0x9ec, 0x9fe97b9769708557226cf6ce6cd]
  | 46 => #[0xabe9c0, 0xa8287c87b87a76e75e74a, 0xa2c94293d80e80c809806, 0xa337795c8, 0, 0xad381380477a, 0xad2acd7dd7dc7b35c8, 0x9bf7db779, 0xac49b75ca, 0xaa2aa19b7, 0x80a782781, 0xad0ac48057d6, 0xa9f9b1953, 0x9ab5d15cf, 0x9b27a9, 0x9ab7a9, 0x9b2, 0x9b29aa7fb, 0x9b2, 0x9909449229215d5, 0x94b9219049029007786ae, 0xacaa307d8, 0xaceaa3a349be9bd, 0xa307875db, 0xa30, 0xa307875dc5db, 0xac8a307e47da, 0xacca359c17be788, 0x9c09be9bd, 0x9c0788, 0xabeaa3a34, 0xabeaa37be]
  | 47 => #[0xaa46da5e2, 0xaca9c09bd7d86da, 0xa2b9b67cc5e55e4, 0x80f7fe5e5, 0xa2da2b93f80e6c8, 0x93e80e7896c8, 0x9439426df, 0xa9f9b195380b80a806, 0xa2b9b694394293e6df, 0xa049b59b27fc7a6, 0xa049b5771, 0x5f25f05ef, 0x9b39b29b09aa770, 0x94592191e6dd5f2, 0x91a7855f0, 0x94a92892191e903, 0x99091d91c, 0x907906905904785784, 0xa8894a928, 0x9048895f5, 0x949948900, 0xac1a2f5f7, 0xaccaca9c46d9, 0xaceaccacaa319c1, 0xad08055fa, 0xabdaa5a31a02810, 0xabdaa67ff, 0xad4acd5fd, 0x7fd5ff5fe, 0xabe7fd5ff, 0xac9ac8ac08876db, 0x92f9249238f3608]
  | 48 => #[0x92f91481f60a, 0x93693092491691481f60a606604603, 0xa62a2495d9559238c382c607605, 0x92e8e3606, 0x81b7e260e, 0x915608, 0xa5da249568c3, 0x9259189169157a3, 0xa2360d60c, 0x9148f58f481f, 0xa239c995d, 0x9c695d7df, 0x9cb8ed6b16a7, 0xa63a617e363f, 0xa4a7e97b4610, 0xaa9a9ea4a8e57b4, 0xa4e7b862b612, 0xa4c9cd7b4, 0xa228f67a7614, 0x9c87a761a, 0xa239c6, 0x82b82a7ea7e67e5, 0xa079ca9c89c7638618, 0xa239c995d81c638, 0x9a79567e0, 0xa07a069c88f7, 0xaaaaa0a59a58, 0xaaaa3ca38, 0xa8aa5aa59a57, 0xa6295579779661f, 0xa5f818795, 0x9179157a57a4]
  | 49 => #[0x9148f581f, 0x822798624, 0xa5d822, 0xa62a60, 0xa27a24817816, 0xa6a9a78226e1, 0xaaaaa8654, 0xa5b698695, 0xaae9c5790, 0xa59a51a50a4f62b, 0xaafaaea599c5790, 0x93a92c92a924, 0x938935934929, 0x93992c62f, 0x93992d92b919630, 0x92e92b9189158e3, 0x9597ce634633632, 0x8fb8f98ef639633, 0xa068ef81c638, 0xa079c89586de, 0xa61a0b95e63f, 0xa64a5da4b, 0x8fb8f9, 0xa0a, 0x8f9, 0xa68a62a6095695563b, 0xa6ba6895581b, 0xa69a62a2495563d, 0x81881781679679563e, 0xa6ba69a68a66a62a60a2496095695581b818817816799796795, 0xa68a24, 0xa17a11834]
  | 50 => #[0xa11, 0x8fd64b643, 0xa178fd64b, 0xa1764a, 0x6f96f864c, 0x64c, 0xa3e70a6a9, 0, 0xa3e64c, 0xa1798a8fd8da88e67d67c67b64b, 0xa1ba198fd, 0x8688676fa6f76a069f, 0x7f57ee7eb, 0x9816d86d7, 0x98294e8b9, 0xa82a159b3996882881749, 0xa8aa5aa53a37652, 0xaaca8a88b, 0xaabaa8aa7a4d693692654, 0xaabaaaaa0a9e9548e5, 0xa1aa08678677, 0xa10a089618da, 0x94e9138b9, 0x913, 0x8c66b565b, 0x8cb8c6, 0x6ca6b5660, 0x8dc8d38cd8c1, 0x8dc8d38376ca65f65e, 0x8ce8376b6, 0x8d48c76ca, 0x8c18366b7]
  | 51 => #[0x6c46c2662, 0x6dc6cb6c5663, 0x6dc6c46c1, 0xac78db6c9, 0xa1ca18833, 0xa1fa14667, 0xa1ba17a15, 0xa13a12a1183366d, 0xa1266d66a, 0xa108fe66d, 0xabaa21a20a1f, 0xa1da1ca18a12a1199183366d, 0xa1e9669629618ff, 0x67167066f, 0x98494f670, 0x8926ec671, 0x835830672, 0x98498197f94f6d86d76d4, 0x8d18cf675, 0x8db, 0x8d88ca8c98be8bd, 0x8d88d78bf, 0xa13833679678, 0xa1ba1998a67d679, 0xa1698a965, 0xa1e8fc8b388d, 0x98a96567d67c, 0x8fd8fc67d, 0xabaa2098a965964, 0x6e46e368067f, 0x6e36e2680, 0x9848bb89283077e77c6ec6e2681]
  | 52 => #[0x9678b86ed, 0x94e8b9, 0x9138b8, 0xa87a779bb, 0xa9868a689, 0xa98687, 0xa0d9cf688, 0xa7579a715, 0xa98a0d, 0xa98a0d, 0xa72, 0xa71718, 0xa7168e, 0xa74a6c68f, 0xa8fa6e700, 0xa9aa9379c, 0xaa8a5b78d, 0xa5b, 0xaa8aa7, 0x8dd8d06f0, 0xaa8a5b698, 0xaa8697, 0xaa882e, 0xaafa5b9c5829, 0x8dd8d28c6, 0x99f8716b8, 0x8b2, 0xa3077969d, 0xa339bf7db69e, 0xac6ac3ac1779, 0xa3ea3d6a0, 0xa4689884b6a26a1]
  | 53 => #[0xa41a3f8547917146ac6a36a2, 0xa0f72a6ac, 0xa0f72a6ac, 0xa48a40a3d, 0x6b16a76a6, 0xa0a, 0x9cb6b1, 0x9959946aa, 0, 0xa419a5, 0x9988487aa, 0xa449a472b, 0x7f57d47d3, 0x904902900, 0x982980839, 0xa96a8ea75, 0xa0a9599588fb8ef7ce6b36b2, 0xa0a9cb8f78ed, 0xa07a069c88f78ed6de, 0xab8a037c7, 0x8d48c78c6, 0, 0x8d88d7, 0x9f19ed8b2, 0x9fa9f98ab, 0xa84a7f81e, 0xa81a7da2e, 0x6c46c06bd, 0x6c46c36c06be, 0x6c3, 0x6c3, 0x6c4]
  | 54 => #[0x6cb, 0x6c5, 0, 0, 0, 0x6cb, 0x6dc6cb, 0xa78939, 0xac78db, 0x98d8da, 0, 0xa84a7fa7a, 0x8636cf6ce, 0x91189f8957226cf, 0x97d8668636d0, 0x97c90f862, 0xabba0aa05, 0xa1da1b991, 0x98d95094d, 0x98d6d7, 0x993986983, 0x98c989983, 0x9836d8, 0x98398183077e, 0xac5ac29c4, 0xaccacaa35, 0xabfabc887, 0xaa1a82a25a20a079c89b595894b94394293891f8d289d8467c77ac7697457266ef6e06df6de6dd, 0x94b94892091b904, 0x95c95a7ce, 0xa2b9b694193f80e809, 0xab6a6ba66a62a5ea249609556e1]
  | 55 => #[0xa6aa68a67a65a63a61a5d9a79569098c37e37e2, 0x9889686ec, 0x8918398386e86e4, 0x98896894f8bb6ec, 0x9829806e6, 0x9828d96e7, 0x98d9518b4839, 0x98594e8b98b5891, 0xa0f95c8807fc, 0x96396288f, 0xaba9918da88e, 0x988968892, 0x98c989988967, 0x98397f97e, 0x97f97e7cf, 0x98e8cc8b68af, 0x90f7076f2, 0x97390f89e7076f3, 0x97697096f864, 0x9959946f5, 0xa3d8686f86f6, 0x9959946f7, 0x6f8, 0xa41a019a57aa, 0xa489e486886779270a6fa, 0xa47a41a3f, 0xa46a3ea3d89886784b, 0xa74a6c7177006fd, 0x96c96b717, 0xa9887487384c, 0xa74a70a6ca5478b700, 0xa9ba96a72]
  | 56 => #[0x8b284771a, 0x9dd9db96e876703, 0x9ec9da9d896e, 0x9f39ef9db8f1, 0x864709707, 0, 0x9a696f856709708, 0x97c975709, 0x97790f864862, 0xa46a3e9a599a897, 0x96c71670c, 0x96b717, 0xa73a0d79e70f, 0xa90a6f85c70f, 0xa73a0da09718, 0x9ee870711, 0x9ef9dd99f, 0x9f89f77d0, 0x91090d90c, 0x9a59a3791, 0xa91a75a0e79a, 0xa6fa6d96b, 0xa6fa0d, 0xa6da0d, 0x99d86f85f71b71a, 0x8f085f84f, 0x9f79d69d599e99c86e721, 0x9e99e884f, 0x72172071e, 0x71f, 0x9ec9e0721720, 0x9de9dc9d973a721]
  | 57 => #[0x9eb9ea, 0x9799779268a6, 0x90e8a38a1, 0xa489e69e5854, 0x9e69e49e3840, 0x9118a3, 0xa97a94a8d9d2728, 0xa9287986c, 0x9f99f58ab8aa, 0xa49a48a0f89872b, 0xa0f9fc83e, 0xa45a449a499672d, 0xa23a22a1e9b387a, 0x9fc9e49e38417ac, 0xa9a844730, 0xa9aa93a759cf844, 0xa99733732, 0x879874, 0xa9ca939ce8bc87987486a, 0x9fb847738, 0x9fb85d73f, 0x9fb, 0x85d847743, 0x9fd9f685d850743, 0x9f08f087786e850741, 0x86073e73d, 0x73e73d73c, 0x9f087786074374073d, 0x9d986073e, 0x9de9dc9d9, 0x86085d, 0x877742741]
  | 58 => #[0x9ff9fb9f6742, 0x9e89e299c90b8e98e8, 0x9f39e18f08e7, 0x9ff9fd745, 0x9fd9f67d2, 0x88287f76e748, 0x74a, 0x87f87c87b87875475374a, 0x882, 0x76075f, 0x7f77f57d3, 0xa80a7e75074e, 0xa84a7fa7aa77, 0xa77a76, 0xa84a7989d87e751, 0xa87a7f, 0xa87a79a7789d88687e81e, 0xa8588687e, 0x87d87876e754, 0xa8288588487c, 0x9527f57f37ef, 0x7c87c67c4757, 0xab8a037cb7c87c6, 0x7c87c67c5, 0xa85a838e2, 0x88387b87876d75d75b, 0x88387d87b76d75d, 0xa99a68a289939929869527f57f2, 0x88388287d76075f75e, 0x88287f761, 0xa82881760, 0x88387f87d761]
  | 59 => #[0x87e7f47cb, 0x9527f17ef7d3, 0x7c97c7764, 0xab87c97c87c6765, 0xab8a037cb7ca7c97c87c77c67c57c47c37c2, 0x9b99377cc, 0x7f47f37f17ef768, 0x9527f77f67f17d47d3, 0x7f77f67d5, 0x77776c76b, 0x94193f777, 0x80c808806777, 0xa8288588388087f87876e, 0xa82882881880, 0x9b29b09ad771, 0x9b2, 0x9b5, 0x907905904, 0xad4ad2abe9bc, 0x9bc776775, 0xacdabe, 0xacdaa39bc7be, 0xa2d94194093f93c80f80c80b807802782, 0x94a94591d903901, 0xacdabea30, 0xac4ac37d67b3, 0xac4ac2aa4aa2aa19b7, 0x9809698b98b88b583583077e77d, 0x83582f77e, 0x9899879858b98b58b483582f, 0xa2c94393d80e809780, 0x94080b80a806782781]
  | 60 => #[0x94080d80a, 0xa2d809802, 0x907906904784, 0x990908907906905785, 0x91e906905904, 0x948904902, 0xabeaa3a34a30, 0xacfaa69c39be, 0x94193d93c80c, 0x9b29b09ad9aa, 0xa8fa6e85b, 0xaabaa0a0c, 0xab2aada5b, 0xab1aa7a37, 0x9f29ed8b2, 0xab3ab2aa9, 0xa3e9a5898, 0xa40a3e, 0xa3d995868, 0x94691d903, 0xa65a4b796, 0xa27a248177e1797, 0xa65a63a4ba0b7e3, 0xa5fa27822, 0xa66a5da24, 0xa96a91a75, 0xa8fa6e9a1, 0xa9ba9a9ce, 0x990953947, 0xa98a90a6f, 0xa94a93a8c, 0x8dd8d38d0]
  | 61 => #[0x9d98eb89a, 0x9259177a4, 0x917, 0x917916, 0x931930, 0xa049b57fc, 0xabb9c695b, 0xac7a1c833, 0x9b59b29ad, 0xa40a3f9a3, 0xa43a429d7, 0xa47a45a01, 0x9527ef7d3, 0xa62a60a5d, 0x95781d815, 0x8438427b2, 0x7b2, 0x9d1, 0xad2acd7dd, 0x9cd82d7b8, 0xa52a4f82d, 0x8c87c07b7, 0x8c88c07ba, 0xab49cd9548e582d, 0x8b07bf7bb, 0x8cd8ae, 0x8ae7bc, 0x8cd8c1, 0x8dd8dc8d0, 0xaccacaaa3, 0x98a8d98d68d48d28c7, 0x8db8d18c8]
  | 62 => #[0xa3ca3ba38, 0x7c67c47c3, 0x7ca7c8, 0x7c77c5, 0xab87ca7c97c7, 0x7c97c8, 0xab8, 0, 0xab87cb7ca, 0xa03, 0xab8, 0xa89a88a04, 0xabbab6936, 0xab7a6b937, 0xaba98f8d6, 0xa90a469fe, 0xa499f8978, 0xa949fc9b9, 0x9527ee7d5, 0x7f57ee, 0x9527f57ed7ec7eb, 0xad1accacaac5ac4ac3ac2ac18037d7, 0xac5ac4ac3ac2ac1a33a307dc7d8, 0xacaaa4a9fa35, 0xac6abf9c4, 0xac89bf7e47db, 0xac6a33a2f9c4, 0xaccacaaa3a347dd, 0xad4ad2acd, 0xa059c995d8f9, 0x9cb9ca9c895d, 0xa287e27e1]
  | 63 => #[0xa63a61a248c37e37e2, 0xa68a24a0b9578c27e3, 0xa69a66a63a24a0b, 0xab8ab59fb98e8dd, 0x9cd82b7ea7e97e6, 0xab4aa9aa7a4a9548e5, 0xa9ea368e57e8, 0xab3a369cd82a7ea, 0xab3aa9a9ea3ba39a389cd8e5, 0xab1aa7a36, 0x9527f77ec, 0x7f57f37ee7ed, 0x7f57ef, 0x7f77f3, 0x7f6, 0x9527f47f3, 0x7f7, 0x7f8, 0x7f87f5, 0, 0, 0x952, 0, 0, 0xad3acfaa5, 0xad0ace9c1, 0x9b39b09ad, 0x9b59b2, 0xad2acdaa3, 0x9b480f802, 0xaa69c39c2, 0]
  | 64 => #[0xacbac5ac2, 0x9b494080f80e80d80b80a, 0xad1ad0805, 0xacf813805, 0xad3, 0x93d80e80c, 0xa2c943809, 0xa2d, 0x94380e80c, 0x9b480f, 0xa2d94380c, 0xa2d94380e, 0x9b4, 0xa2d, 0x940, 0xac6ac0a31, 0xaceac69c1, 0xacbac5abc, 0xad3aa69c0, 0xa67a659a7, 0x8c288881d, 0xa5fa27817, 0xa5fa27956818, 0xa6aa5ea27, 0xab2aad93b, 0xaafaaeaad, 0xa6ba62a60, 0xa0a8fb8f9, 0xa68a248c2, 0xa86a78a77, 0x92f924914, 0x93293092f]
  | 65 => #[0x92e918, 0xa67a65a5e, 0xab9aa9a9e, 0xab0aa9, 0xa9e88c, 0xab4a9e, 0xaaca9e, 0xab4aacaa9, 0xaafaae82d, 0xab3aaaaa9a9ea8aa5aa59a58a57a3ca3ba398e582e82b, 0xaaea599c582e82d, 0xab9ab7ab5a52a4da4ca4a, 0xab3ab2aa9, 0xab2ab1aa7, 0x989987830, 0x98494f835, 0x98e8d08c9, 0x8d88d58c5, 0xa1aa16a13, 0xa1ba19a17, 0x9859839819138b88b4891, 0x8ce8c98b1, 0x8c88c18c0, 0x98295094d, 0x98d982951, 0x8d88d78d5, 0x8c98b1894, 0xa9d9d18a7, 0xa45a01996, 0xa47841, 0xa45a42, 0xa459e49e3]
  | 66 => #[0xa45a019fc, 0xa9d9d1843, 0xa9b9ce86a, 0xa9ba939ce, 0xa9ca9b86a, 0xa97a94a8d, 0x9f085d850, 0xa42a40853, 0xa489a3898, 0xa48, 0x99a, 0xa96a91879, 0xa91a0e86c, 0x9f38f086e, 0x850, 0x9f3, 0x97a976972, 0xa49a46898, 0xa3d998868, 0xa44a40, 0x96f863856, 0x97996f912866, 0x9a68de8a0, 0xa4699a867, 0xa98a6e85b, 0xa98a8f, 0xa98a6e, 0xa90a8ba74, 0x8b287685f, 0x9fd9ed9de, 0x9d999d8b2871860, 0x9fb9ee99e99d870]
  | 67 => #[0x97c975862, 0x90f, 0x97c8a6, 0x977975, 0x97d97c911, 0x97c977912, 0xa48a47a43a41a3fa3ea3d9e6898, 0xa3fa3d9a3, 0xa96a91a8e, 0xa9b9ce, 0xa96a918bc, 0xa96a8ea75, 0x9f39e899c, 0x9eb9ea99c, 0x9ee99e99d, 0, 0x8b2, 0x9ef9dd, 0xa8f879874, 0xa99a938bc879, 0x9db8f1876, 0x9ef9dd, 0xab0a31a03, 0x88388087b, 0xa98a8f, 0xa8288187d, 0x88587f87d87c, 0xa8288188087f87d, 0x884883882881, 0xab8a82, 0xa82885884, 0x883882]
  | 68 => #[0x885884, 0x884, 0x885, 0xa82, 0, 0xab8a85a03, 0xaccac09c1, 0xa68a63a62, 0x953904900, 0xab9ab3ab0, 0xaac, 0xab9ab4a9e, 0xa1ea158b3, 0xa1d991, 0xa158fd8fc, 0x98d985982, 0x980969913, 0x98994f94e, 0x984969968, 0x8ce8cd8cb, 0x9a69128a0, 0x9b897989f, 0x9a599a898, 0xa46a41, 0x9ec9e09dc, 0x9fa9e18eb, 0x9f99e19e0, 0xa7ca788e28a5, 0xa87, 0x9a69118a48a0, 0x9a6979, 0x911]
  | 69 => #[0x9b99b88a2, 0x9a6911, 0x9b99b89a6, 0x9a697d97a, 0xa7aa78a77a2e8b7, 0x9a6977974927, 0xa92a6e9d48a8, 0xa9da8fa6ea299d1, 0x8db8cd8c68bd, 0x9fa9e19e09d9, 0x9f99d98e7, 0x8cc8b68af8ad, 0x8cb, 0x8cc8cb, 0x8d48c78b0, 0x8cd8c78c1, 0x8cd8c9, 0x9ef9ee9dd99f, 0xa1aa17a16962, 0x98598094e8d9, 0x8d9, 0x8dd8db8d48cc8c68c18bd, 0xa84a7ea7da7ca789a9, 0x985982969, 0x98294e, 0x98d985951, 0x98498294f913, 0xa9ca95a949ce, 0x98e8db8d58d08cf8ca8c88c58be, 0x8db8d88cf8bf, 0x98d8da8d88d78d58c68c58c1, 0x8d88d7]
  | 70 => #[0x8db8d18c8, 0xa62a61a24, 0xa68a28956955, 0x8dd8d88d78d0, 0x8dd8d68d0, 0x8d88d78d0, 0x8dc8cd8c8, 0x8dc8db8d1, 0x8d48ce8cd, 0x98e8d48d08cb, 0x98e98d8db8da8d4, 0x8d48cd, 0x8dc8db8d1, 0x98e8dc8d0, 0x8d48d38d0, 0x98e8dc, 0x98e8dd8d88d68d58d4, 0x8d88d78d6, 0x8dc, 0x98a8d9, 0x8db8d78d6, 0xabaa94a88a6b992, 0x98d8da8d8, 0x98a8dd8dc8d9, 0x98a8dd8dc, 0x98d, 0x98e, 0x98e, 0x98e, 0x97c97591190f, 0xa87a83a798e0, 0xa86a7ea7da7ca7ba7a8f28e1]
  | 71 => #[0xa87a86a7aa78a778f28e2, 0xa80a7ea7ca7aa77a2e, 0x93293092f918, 0x9ca9c88f78ed, 0xa9ea39a38954, 0x9f39e18e98e8, 0x9e28ec, 0x9fa9f99f39e08ec, 0x9e99e89e1, 0x9f39e29e1, 0x9f59ec9e2, 0x9f59d9, 0xa0a9cb9c68fb8fa8f98f88f78ee, 0xa23a229c695c95a9598ef, 0xab7a6ba159cb9ca9c89b39969599589378fb, 0x9f39e29e1, 0x9f09ef9db, 0xa87a80a7e9bb, 0x932930923915, 0x9319309148f5, 0x932931925917, 0xa069cc9ca9c7, 0xa229ca9c7, 0xa059c68fa8f9, 0xabba0a9c895b8fb, 0xa23a229cb, 0xa239cb9ca9c99c895b, 0xa1e9669628fd, 0xa1ea1aa17a16963, 0xa21a208ff, 0xa21a20a1e, 0x94491e904901]
  | 72 => #[0x990948904, 0x990947, 0x94a91e91d, 0x99094891e, 0x99094891e907, 0x947944, 0x990944922921, 0x94794491e, 0xa68a67a65955, 0xa98a8fa8ba6c, 0x9f89f79f49ed, 0x97891191090d, 0x9a697c97797597492791190f90e, 0x97c979977927926912, 0x97a978977973912911, 0x97d97c97a975973911, 0x9b99a6, 0x9b8979, 0x98c989988984, 0x932925917916, 0x924917, 0x93692f, 0x936932931, 0x92f, 0x93192a, 0x99095394794594491f91b, 0x99095394b94791f91c, 0x91e, 0x945944, 0x947, 0x990953944, 0x990947945]
  | 73 => #[0x99094b948945, 0x947944, 0x93692e925924, 0x931930, 0x93693193092f, 0x9b89a697c977, 0x97c977974, 0x94b94a949948, 0x93993293192f, 0x939931930, 0x93993292c, 0x93292f92e, 0x938933930, 0x931930, 0x936932, 0x931, 0x937933, 0x93a936935933, 0x939938936, 0x93a936, 0x938, 0, 0, 0x93a, 0, 0, 0xabbab6ab1, 0xa7893f93d, 0x9b694394294193f93e, 0xa78a2d94393f, 0xa78a2da2ca2b943, 0xa2da2c941]
  | 74 => #[0x9b4943942, 0xa78a2b9b6943, 0xa9fa89a88a2ca2ba049b69b1953, 0x990953948947, 0x95394a948, 0x949947, 0x94b, 0, 0xa8899094b, 0, 0x953, 0x98d95094e94d, 0x98d98295195094f, 0x989, 0x98c988, 0x99398d982981, 0x98d98097f97e, 0xa99a68a28993992986, 0xa88, 0xaabaa0a56a39a38a32a0c, 0xa68a60a28, 0xa6ba5da24, 0xa62a27, 0xab7a6ba15a0aa06a059cb9b3996, 0xabba0595c95b95a, 0xabba22a0aa07a069ca95c95b, 0xa059cb9c895d, 0xa23a22a069cb, 0xabba0a, 0xa68a62a27a2495f, 0xa62a61a27a0b9d1990988, 0xa66a64a62a4ba28a279a8]
  | 75 => #[0xa1da1ba15a0898d, 0xac7abaa21a20a1fa1ea1498a966, 0xabaa20a1ba19a16a13966965964, 0xabaa20a1ea15966965, 0xa21a20a1d98d, 0xa21a20a1aa17a16a12, 0x98c989985969, 0x984, 0x98a989983982980, 0xa9da6fa0d96c96b, 0xa6fa0d9d196c, 0xa92a6fa6ea6d9d49d1, 0x9f29f199f96e, 0x9f39ef9e29e19de9dd9d8, 0x9fe97c97b977970, 0x9fe9b897d97a973, 0x9fe97c975972, 0x9b9978977976974973, 0x9fe9b89a697b977975, 0x9fe97c97b979, 0x97d979976, 0x9fe9b897b977, 0x9fe97b97a979, 0x9b9, 0x9b897d97c, 0x9a697d, 0x9fe9b8, 0x9a6, 0, 0x98b98998797f, 0x98d989988984981980, 0x98d985982981]
  | 76 => #[0x98f98d98b989987985, 0x98c987985983, 0x98d, 0x988, 0x98d98c989987, 0x98c, 0x98b98a989, 0x99398c98a, 0xac798e98c, 0, 0x98f98d, 0xac798e, 0, 0xac7, 0xa8ca62a28992990, 0xa69a68a66a63a27a249d1993, 0xa1da1ca19a18, 0xa94a88a6b, 0xac4aa2aa1a88a78a69a68a66a63a2ca2ba27a249d19b69b29b0, 0xa47a46a44a3e9e59a3995, 0xa49a46a45a429fc9e7998996, 0xab7a6ba23a15a059cc9cb9c89b3, 0x9f89f79f49ee9da99f, 0xa48a46a44a42a41a40a3fa3d, 0xa49a46a40a3d99a, 0xa41a3ea3d, 0xa98a96a92a8fa759d49d0, 0x9f39f09eb9ea9e99e29e1, 0x9f89f39eb9ea9d69d599e, 0x9f99f89f59f39ee9ec9eb9ea9e29e19e09d69d599f, 0x9fa9ef9ee9e19dd9db, 0xa98a8fa6ea55a299d2]
  | 77 => #[0xa96a91a559a2, 0xa9ca8fa6ea29, 0xa49a41a3f9a5, 0xa49a46a40, 0xa49a47a46a3f, 0xa98a96a92a8fa8ea75a009e79b9, 0xab6a6aa62a28, 0xa67a5e, 0xa84a7fa7aa78, 0x9b19b09ad9ab, 0x9b59b09ae9ad, 0x9b59b1, 0x9b39b19b09ae, 0xa049b19b0, 0x9b59b2, 0x9b3, 0x9b5, 0xa04, 0xa04, 0xacba2b9b6, 0, 0xacba9fa88a2d, 0xaccacaac5ac2, 0xa8ba48a47a46a43a3fa3ea3d9fe9ea9e6, 0, 0xa9aa97a8ca5c, 0xab8a85a84a82a77, 0xad3ad2ad19c0, 0xad3acf9c39c09be, 0xac9abda029c0, 0xacdac6ac3ac1abeaa6a30a2f9c4, 0]
  | 78 => #[0xad3ac6abe, 0xad3acfaceaa6, 0xad3acfaa6, 0xaceacbac6ac5, 0xab3ab2aafaa9, 0xa07a06a059cb, 0xabba059ca9c9, 0xa0aa07a06, 0xa229cc9cb, 0xa0a, 0xabba23a06, 0, 0xaaca9ea3ca3b, 0xa9ba98a93a8f, 0xa91a8fa75a0e, 0xa9da8fa8e, 0xa9da96a91, 0xa92a29, 0xa70a6fa0d, 0xa9ca96a91a6e, 0xa009f79df9d6, 0x9fd9f89f79f39ed9e99e89de, 0xa49a45a43a01, 0x9ec9eb9ea9da, 0x9de, 0, 0x9ef9de9dd, 0x9ec9eb, 0x9f59f09ec9e29de, 0x9ec9e0, 0xa009fa, 0x9f9]
  | 79 => #[0xa009fa9e2, 0x9f99f59f3, 0xa49a48a479e4, 0xa49a48a47a41a3fa01, 0xa45a44a43a40, 0xa48a44a429e7, 0xa48a46a44a40a01, 0xa009f59f39e9, 0xab0a94a31a039ff9fc9f3, 0x9f9, 0x9f89f79f4, 0x9f49ee, 0x9fd9fb9f3, 0xa009fa, 0x9fa9f49f0, 0xa009fa9f3, 0x9f89f79f5, 0x9fa9f9, 0, 0xa009f9, 0x9fd9fb9f6, 0xa009f9, 0x9f8, 0xa949fd9fc9fa, 0xa90a469fe, 0, 0x9fd, 0xa94, 0, 0xa90a46a00, 0xab0a31a03, 0]
  | 80 => #[0xa49a43a40, 0xac7abaab9ab0, 0xabaab8ab7a89, 0xabaab7a94a6b, 0xa23a22a07a06, 0xabba23a22a07, 0xabbab7a6ba0a, 0xa1fa19a18a17, 0xa90a72a71a6fa0d, 0xabbab6a6aa67a65a62a56a32a28a23a22, 0xa65a64a63a61a4b, 0xaabaaaa39a38a32, 0xa9aa98a8fa75, 0xa98a96a8fa6e, 0xa94a45a44a43a41, 0xa1fa1ea17a14a12, 0xabaa1fa1da19, 0xac7abaa1fa14, 0xa1a, 0xa1fa1ca16, 0xac7abaa1ba17, 0xa21a20a1da1ba17, 0xa21a20a1fa1da1b, 0xa19, 0xa1ba1a, 0xabaa1da1c, 0xac7a1fa1c, 0xa21a20a1fa1e, 0xac7a21a20a1f, 0, 0xac7a21a20, 0xacbac7abaab8ab6ab0aa2aa1a9fa97a95a90a8da8ba88a86a81a79a78a77a6ba6aa68a67a61a60a5ea5da56a49a48a47a46a42a3fa3ea3da32a31a2ea2da2ba2aa28a25a24a23a21]
  | 81 => #[0xac7abbabaab7a82a6ba45a44a43a41a22, 0xabbabaab7a82a6ba45a44a43a41, 0xabba48a47a46a40a3d, 0xa67a66a65a5ea5d, 0xab9ab4a56a32a2aa26, 0xab9ab3ab1ab0aacaa7a8a, 0xa6aa68a5fa5ea28, 0xa68a64a63, 0xa9ca9ba99a95a94, 0xabbab7ab6ab1aafaaeaa7a37, 0xacba9fa88a78a2c, 0xabaab7a94a89a88a78a6ba2d, 0xa87a84a81a80a7ca7ba2e, 0xab8a85a84a82a7fa7ea7da77, 0xacaac3ac1abfa30, 0xad2ad0acfac4ac1abeaa6a33, 0xaceacaac6ac0abf, 0xab7ab0a9ea56, 0xacdacaac3ac1aa4aa3a9fa35a34, 0xaceac6abeaa6aa3, 0xad3accacaabea9f, 0xab2ab1aadaabaa0, 0xab2aadaabaaaaa7, 0xa39, 0xab4ab3aacaa9a3b, 0xab9ab4ab0aa9a3c, 0xaac, 0xaaca9e, 0xa94a47a46a3fa3e, 0xa49a48a45a43a40a3f, 0xa49a48a45a41a40, 0xa94a46a45a43a42]
  | 82 => #[0xa44a43, 0xa49a48a47a43, 0xa46a44, 0xa94a48a47a46a45, 0xa94a47, 0xa48, 0xa94a49a48, 0xabbab7a94a6ba49, 0xa9da90a8fa8ea6d, 0xab3ab2ab1aaeaadaabaa7a8aa5aa58a57a56a4ea4c, 0xa69a66a65a62a60, 0xabbab9ab6ab5ab4ab2ab0aadaa9aa8aa7a52a4d, 0xad3accac7ac0abfabeab8, 0xab9ab3aa9a51a50a4f, 0xab9ab7ab4ab0aa0a59a58a51a50, 0xab9ab2aaea59a52a51, 0xab4ab3ab2aacaa9a9ea52, 0xad2acdac9ac8ac7ac0abfabeabcaa3, 0xab5ab2ab1aa7a5aa57, 0xa90a8fa8ba73a6fa6c, 0xa9ca9ba98a91a72a71, 0xab4ab3aabaaaaa9, 0xa8aa5aa59a58, 0xab3ab2ab1aa9aa0a9ea59, 0xab4aacaaaaa8aa7aa0, 0xab2ab1aafaaeaa8aa7a5b, 0xaafaadaacaa9aa7a9e, 0xa9ca9ba9aa98a97a95a94a8f, 0xa67a64a62a60a5e, 0xa6ba67a66a63, 0xab6a6aa64a62a60, 0xa6aa68a66a65a64]
  | 83 => #[0xa67a65a62, 0xa6ba66a63, 0xab6a68, 0xa6aa65, 0xa6ba69, 0xa68, 0xab6, 0xab6a6b, 0xab6a6b, 0, 0xabbab7ab0a9e, 0xa94a93a8ea8ca6f, 0xa9da6f, 0xa96a91, 0xa9da90a8f, 0xa98a95a8fa8ea75, 0xa9da99a94a73a72, 0xa9ba9aa95a91a90a8fa8ea74, 0xa90a8fa8b, 0xa9da9ba99a96a95a93a8ca75, 0xa9da9aa98, 0xa86a83a81a7ea79a77, 0xab8a82, 0xa80a7fa7a, 0xa87a86a85a84a83a7f, 0xa84a81a7e, 0xab8a82a7ea7da7c, 0xabaab8ab7a89a87a86a84a83a82a81a7f, 0xa84a81a80a7fa7e, 0xabaab7a89a87a86a84a7f, 0xab8a85a84a82a81a80, 0xabaab7a89a87a86a85a84]
  | 84 => #[0, 0xab8a83, 0xabaab7a89a87a86a85a84, 0xabbab7ab0a9ea94a88a86a85, 0xabbab7ab0a9ea94a88a87a86, 0xad3aceaccacbacaac7abeabcabbabaab1a9fa9ea9aa96a94a93a92a90a8fa8ba89, 0xac7ac5ac4abcabbabaab9ab8ab7ab6ab3ab1ab0aacaa7aa2aa1a9fa9aa99a97a94a92a91a8fa8ea8ca8aa88, 0xacbab0a9fa9ea9da94a90a8e, 0xad3acaac6ac0abfabea9f, 0xab9ab4ab3ab1ab0aafaadaa7, 0xa9ca9ba9aa94a90a8ea8c, 0xa99a92, 0xa97a96a95a94, 0xa99a98a94a93a8f, 0xa9ba96a93, 0xa9da9ca99a98a91, 0xa9da98a94a92, 0xa99a94a93, 0xa9ca9aa99a95, 0, 0xa9da9ba9aa99a96, 0xa9ca98, 0xa9d, 0xa9ba9a, 0, 0, 0, 0, 0, 0xacbab0, 0, 0xab4ab2ab0aafaacaaa]
  | 85 => #[0xacbac4abbab7ab6aa2, 0xacfaccac5ac3ac2abfaa5aa4, 0xad4ad2ad0acfaceacaabfabd, 0xad3aceaccacbacaac5abe, 0xad3acfaceac9ac7abaab9ab0, 0xace, 0xab9ab4ab2aadaa9aa8, 0xabbab7ab6aafaacaab, 0xacbab4ab3ab2ab0aaeaac, 0xab9ab2aafaab, 0xacbabbab9ab7ab6ab2aadaac, 0xacbab9ab3ab2aafaaeaad, 0xacbabbab7ab6ab1aafaae, 0xac7abcabbab9, 0xabbab9ab6ab4ab3ab1, 0xacb, 0xac7abcabbab3ab2, 0xac7abcabbab9ab4ab3, 0xac7abcabbab9ab7ab5ab4, 0xac7abcab9ab6, 0xacb, 0xac7abcab9ab7, 0xad3accacbac0abfabeabcabbab8, 0xad3accac7ac0abfabe, 0, 0xad3acfaccacaac7ac5ac2, 0xad1aceacbac7ac6ac5abeabc, 0xacbac6ac5ac2abfabd, 0xad3acfac9, 0xaceaccac6ac4ac3, 0xac5ac4ac2ac0, 0xad2acfacdaccacbacaac9ac1]
  | 86 => #[0xad4ad2ad1aceac4ac3ac2, 0xad1ad0accacaac5ac3, 0xad3acfaceaccac9ac6ac4, 0xad2ad0acfaccacbac5, 0xad4ad2ad1accacbaca, 0xaceacd, 0xad3ad1acfac8, 0xad2ad1acfaceacdaccac9, 0xad2ad1acc, 0xad0acdacc, 0xad1ad0acdacc, 0xad4ad1ad0acfacd, 0xace, 0xad4ad3ad2ad1, 0xad2ad0, 0xad4ad3ad2, 0, 0xad4, 0, 0]
  | _ => #[]

def lower (i : ℕ) : ℕ := ((lowerPage (i/32))[i%32]?).getD 0

private def upperPage : ℕ → Array ℕ
  | 0 => #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x1a, 0, 0, 0, 0, 0x1f01e01d01a]
  | 1 => #[0, 0x21, 0, 0, 0, 0, 0x26024023, 0x11, 0, 0, 0, 0x2b02a, 0, 0, 0, 0, 0, 0, 0, 0x3303002f, 0, 0, 0, 0, 0, 0x39037036035, 0, 0, 0, 0, 0, 0]
  | 2 => #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 3 => #[0, 0, 0, 0, 0x51, 0, 0, 0, 0, 0x3c00c, 0, 0x52, 0, 0x1000e, 0x6d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 4 => #[0, 0x4f, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x97, 0, 0, 0, 0, 0, 0, 0]
  | 5 => #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xaf, 0xaf, 0, 0, 0xb3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 6 => #[0, 0xc1, 0, 0x23021, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xce, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xdc0b50b20af, 0, 0, 0]
  | 7 => #[0, 0, 0xe2, 0xe3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x8c, 0, 0, 0, 0xf9, 0xfa, 0xfb0fa, 0xfb0e2, 0, 0, 0]
  | 8 => #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xa, 0xb5, 0, 0, 0x11010e08e, 0, 0x112, 0, 0, 0x78, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 9 => #[0, 0, 0x12108b, 0x122, 0x1140f80e1, 0xdd, 0, 0xac077, 0, 0, 0xe40e3, 0x12b, 0x56, 0x90, 0xcb, 0x12f, 0x5e, 0x25, 0x91, 0x26023, 0, 0x9008f, 0xe, 0xbb, 0xf00e, 0x96094, 0xd20d1, 0, 0, 0, 0, 0]
  | 10 => #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x2b029, 0x9d09c, 0, 0x153083, 0, 0, 0, 0x157155, 0, 0, 0, 0x15b, 0x80, 0, 0x15e, 0]
  | 11 => #[0, 0, 0x162, 0, 0, 0, 0x166, 0, 0, 0, 0x16a, 0x16a169, 0x16c16b16a02e02b02a, 0, 0, 0, 0x170, 0, 0x154, 0x98, 0x156097, 0xdb0da, 0xdb, 0x153, 0xc10c0, 0xfe0ad, 0x17016, 0x3a038, 0x3a039, 0x1790c0, 0x17a0fe, 0xa4]
  | 12 => #[0x9e, 0x13511f, 0, 0x18211f, 0x184, 0x185135, 0, 0, 0, 0x1161150e60e5, 0xec0eb, 0, 0, 0, 0x18e18c, 0, 0, 0, 0x184, 0x92090, 0, 0, 0, 0x197136, 0x197194, 0x12e, 0x12f, 0, 0, 0, 0x19e19b, 0x19e19b12f0cb]
  | 13 => #[0x19f1300cd, 0, 0x1a219e, 0x1a3, 0x1a4, 0, 0x19d0cd0cc06b, 0, 0, 0, 0x1aa1a81a6, 0, 0x3c03b, 0x1ad, 0xba, 0, 0, 0, 0x1b21b0, 0, 0x1b4, 0, 0, 0, 0x1b81b71b6, 0, 0, 0, 0, 0x1bd1bc, 0x147, 0]
  | 14 => #[0, 0x1540be, 0, 0x1c3173, 0, 0x1c2, 0x1c6, 0x9c, 0, 0, 0x1c8, 0, 0x1cc, 0x1cc1cb1c909c, 0, 0, 0x1d0, 0, 0, 0, 0, 0x151, 0x1d61d4, 0, 0x1d81d51d4, 0, 0, 0, 0x1dc, 0, 0xd8, 0x1df1de1dc1db]
  | 15 => #[0x1e0, 0x1e11e01de0da0d80d7, 0x1e20a7, 0xd8, 0, 0, 0, 0, 0, 0x1e91e81e6, 0, 0, 0x1ec, 0, 0, 0x1ef1ee1eb, 0, 0, 0, 0, 0, 0x1f51f41f2, 0, 0, 0, 0, 0x1fa1f91f8, 0, 0, 0xdd, 0x33, 0x22]
  | 16 => #[0x200, 0x2011a3022, 0, 0, 0x19b, 0, 0x19f, 0, 0x208, 0x2092080cf0ce, 0, 0, 0x20c209208, 0x20c06f, 0x20d141, 0x15a, 0, 0, 0, 0x213211, 0, 0, 0x216, 0, 0x218, 0, 0x21a, 2, 0x1c113706e, 0xc5, 0x12b0e3, 0x12b0f90e30c5]
  | 17 => #[0xac, 0, 0x22211a1030ea, 0x18d189183, 7, 0xb, 0x3c, 0x3b, 0xc, 0xd, 0x1bf00e, 0x1260f708b041, 0x21c, 0x2251040eb, 0, 0x11e1070ee, 0x1f01c01a, 0, 0x1f01a, 0, 0, 0x1201090f0, 0x235231193045, 0x231, 0x235, 0x239, 0x23a23323201d, 0x2001f01e01d01c, 0, 0xfd, 0xea, 0x18e]
  | 18 => #[0, 0, 0, 0x224079, 0, 0, 0, 0x118, 0x119, 0x22f, 0, 0, 0, 0x120, 0, 0, 0x115, 0x1170c8, 0x25118a1280e50ac077, 0x119, 0, 0x135129120, 0x12a120, 0x129, 0xa, 0x259, 0x25a259104, 6, 0x11, 0x12, 0x13, 0x14]
  | 19 => #[0x15, 0x16, 0xf6, 0x8b, 0xf60b20b10b008b, 0x1fe121, 0, 0, 0, 0x201200, 0xc4022, 0xc9027025021, 0x26c1a212f, 0, 0x202201, 0x26d19e19b, 0x26f26c0c9, 0, 0x19e, 0, 0x27426a2010c4022, 0, 0x27527126b26a202201, 0, 0, 0, 0, 0x12d, 0, 0, 0, 0]
  | 20 => #[0, 0x196090, 0, 0x26d1a212f0cb07c, 0x28407c, 0x28507c026025021, 0x28607c07b, 0x28628526d1a207c05b, 0, 0, 0x289, 0x28a27a279, 0, 0x27c, 0x1ad, 0, 0, 0, 0x292, 0, 0x206, 0, 0x296066, 0x286132026025024, 0x297287285134132, 0x29828628413205a, 0x29a07a, 0x206, 0, 0x29b, 0, 0]
  | 21 => #[0x2a0, 0, 0x64, 0, 0, 0, 0, 0x1ac, 0, 0, 0, 0x13c, 0x13f13d, 0x1b5, 0x20a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x14a, 0, 0x1b11af094, 0x1b91b8140, 0, 0, 0xd10cf0ce, 0]
  | 22 => #[0x1bf, 0, 0, 0, 0, 0x20c0d1, 0, 0, 0x139, 0x1000f, 0x13e, 0, 0x13b0d2, 0x142, 0, 0x20f13b0d2, 0x145, 0x149145, 0, 0, 0, 0, 0, 0x80, 0xd3, 0x164, 0x169, 0x16d, 0x16f16d16c, 0x2dc17216d16b, 0x1c5, 0]
  | 23 => #[0x1c71c51c31c2, 0, 0x2e2088084, 0x84, 0, 0, 0x25e, 0x12, 0, 0, 0, 0x160, 0x1600d60d3, 0x161, 0, 0, 0, 0, 0, 0x2f1, 0x1d7, 0xf, 0x18, 0x19, 0x182, 0x16e, 0x2100d3, 0x2e02c02b, 0x2fc, 0x34032030, 0x34032031, 0x1ff0ae]
  | 24 => #[0x1f4017, 0, 0, 0, 0, 0x305227131, 0, 0x307, 0, 0, 0, 0, 0x30c, 0x30c25e, 0, 0x30f, 0, 0x261, 0, 0x30f260, 0x31025f, 0x21c, 0, 0x317, 0x318, 0x3181191020e9, 0x230, 0x31822f22d105, 0x102, 0, 0, 0x1c71c51c31c21731540bc098]
  | 25 => #[0x32031f1c71c409d, 0x31f1c91c817415209c, 0, 0, 0x214213, 0x2140d6, 0, 0x15f15e, 0, 0, 0x1d0, 0x1d31d2, 0, 0, 0x2e02d02c, 0, 0, 0, 0, 0, 0, 0, 0x334, 0, 0x1fd, 0x1e01db0d7, 0x215, 0x33b21b, 0, 0, 0x86, 0]
  | 26 => #[0x3401ed, 0x15, 0, 0, 0, 0x17d, 0, 0, 0, 0x1fa, 0, 0x179, 0, 0, 0, 0, 0, 0x3131f7, 0, 0x217, 0, 0, 0x1dd177176, 0, 0, 0, 0, 0, 0x35a, 0, 0xae03203102f, 0]
  | 27 => #[0, 0, 0, 0, 0x363, 0, 0x36617c, 0xb40b30af, 0x3680dd0b1, 0xf7, 0xf7, 0x36a3692651100f60df08c, 0x1120f70e0, 0x1d91d71d4, 0, 0x18a, 0, 0x1000fb0e20c6, 0x1160fb0e70e60e2, 0x12c, 0x37124622121e18a12c0c50a0, 0x374, 0x222, 0, 0x49, 0, 0x377, 0x37b21c, 0x37c25b22e21c, 0x37c002, 0x37b37937837731a316002, 0x377]
  | 28 => #[0x37c105002, 0x38137c11c1050ec, 0x11c104, 0x37931b230, 0x1080f10ef01b, 0x24f, 0, 0x387, 0x38823d23c, 0x38838723c, 0x23b238, 0x385238, 0x38c23d23a237234, 0x234, 0x18e, 0x38f18f18c, 0x39025c, 0x39118b11c, 0x390259225, 0, 0x3942f7, 0x3a039038, 0xf5, 0, 0x398397, 0x10f, 0, 0, 0x39c, 0x39c39b, 0, 0]
  | 29 => #[0, 0, 0, 0x3a23a0283281, 0, 0, 0, 0, 0, 0x39f39d, 0x3a714013d, 0, 0, 0, 0, 0, 0, 0x155, 0x3b1, 0, 0x3b4, 0x3b51cb, 0x3b53b4321174098, 0x39836d36b2661fe12410f0f50de, 0x1150e5, 0, 0, 0x3ba128, 0, 0, 0xf40ef, 0]
  | 30 => #[0x3c0, 0, 0x1820f101f01d01b01a, 0x3c20f101b, 0, 0x3c10f20f0, 0x3c63c510a0f2, 0x3c50f40f20ef, 0x3c63c5, 0, 0xf3, 0x1f3, 0x3cc3591f51f2, 0, 0, 0, 0, 0x3d0, 0x3d1, 0x3d33d134d, 0, 0, 0, 0x3d62ff, 0, 0x3d91ff, 0x3d517f0fe, 0x17f17e, 0x3da1ff, 0, 0x3dd3dc3d83d53d1, 0x3a019512e090]
  | 31 => #[0x3a3133091, 0x3e0, 0x3a519a197092, 0x197, 0x3e33e0, 0x3e53a3, 0x3e63e5293, 0, 0x3e73e63a3294, 0x3a91b5094, 0x3ea, 0x3ea1b31b0, 0x3ec, 0x26d1a41a019b, 0x3ee26d1a019e, 0x3ef, 0x1d1, 0, 0x3f23c0, 0x3f2, 0, 0, 0x3f6, 0x3f7280, 0, 0, 0, 0x14c, 0, 0x3fd, 0, 0]
  | 32 => #[0x1d5151, 0x4011d5, 0, 0x40316d16b16a, 0, 0x405, 0, 0, 0, 0x3ca3c43c20f30f1, 0x2fa17117016e, 0x219, 0x10d, 0x40d10d, 0x40e, 0, 0x392, 0, 0, 0x1a8, 0x414, 0, 0, 0, 0x139, 0, 0, 0, 0, 0, 0, 0x1e6]
  | 33 => #[0, 0x39322511d11b, 0x16f, 0, 0x17d, 0x425, 0xb4, 0x3c4, 0x3cb3ca, 0x42802001d01c01a, 0x42a428, 0x42a, 0x399, 0, 0, 0x42f, 0x43042f113112, 0, 0x43242d399, 0x224079, 0x434224079, 0x4343702240ac079, 0x224189, 0x437183, 0x4384373bc3ba18d, 0x439, 0x4391280e6078, 0x43b43722418811604a, 0, 0, 0x40f, 0x43e]
  | 34 => #[0, 0x42c193, 0, 0x443, 0x444443185135, 0, 0, 0, 0, 0, 0, 0x447, 0x44c44242c3f23c93c738e38d38b38523b13510a0f2, 0x3bf23211f1080ef, 0x44e12a10c0f4, 0x42e08d, 0x43342d39a39910f, 0x2030c7, 0x23e20304c, 0x44f, 0x454185184, 0, 0, 0, 0x458, 0x459, 0x45a45910d0ed0ec00a, 0x45b422393392007, 0, 0x45d3ca38810c10b, 0x10e0b50b40b3, 0x38f19118c11a]
  | 35 => #[0x46045c, 0x45c44111d, 0x39018f, 0x46346244139038f, 0x46446239025c18b006, 0x46446246044141111e048, 0x44725012a, 0x46745544242c19318411f, 0x46845418213511f, 0x46945444242a18211f, 0x46a, 0x46b, 0x46c186, 0x46d42c428, 0x4683c738510a1080f20f10ef01b, 0x46c468256186, 0x46c46b44f, 0x46f46945444c42938c38a38802001d01a, 0x446429, 0x4734453f424c, 0x46744242a193, 0x47547446744544444242a, 0x47642c42b429428, 0x476, 0x47847646b46946844f18618213512a129, 0x308228226, 0x3c03b00c, 0x3ee, 0x3c, 0x47647446a3f3, 0x47d28f28b28905f, 0]
  | 36 => #[0x199, 0, 0x202, 0x483, 0x47646f46845444544340a3f23cb3c93c83c738e38810b10a1090f30f20f0, 0x110, 0x19a152, 0x4841a3, 0x488275, 0, 0x1aa, 0, 0, 0, 0, 0, 0, 0x29928613207a, 0x3b, 0x3ef29528820519e19c, 0x3e53e119a197, 0x1b31b21b0, 0x4961af, 0x4973eb1b51b41b2, 0x4974963ec1b41b31b0, 0, 0x49a, 0, 0x49c, 0xd0, 0, 0]
  | 37 => #[0x4a0, 0, 0x1c1, 0, 0, 0, 0, 0x4a7, 0x4a84a74a5, 0x4a94a5, 0, 0x431, 0x118, 0x1170fb0fa0c8, 0x3741181010e8, 0, 0x39019018f, 0x38f30218e11b, 0x393, 0x136, 0x3e53e1, 0, 0, 0x4b6269, 0x4b7, 0, 0, 0x47a309, 0x1ae1ad, 0x48b41227e1ab1aa1a9, 0x48c, 0x48d3f7]
  | 38 => #[0, 0x48e, 0, 0, 0x4800b6, 0, 0x482, 0x11411208e, 0, 0x28b, 0x308, 0x4cb4bc47a303, 0, 0, 0x4cc, 0x3ad, 0x30b, 0x3ff, 0x2be13b0d10d0073, 0x1c11bf1be147, 0x4d03ad3a813d, 0x3b0, 0x49c, 0x49f, 0x30b, 0x13c0b9, 0x4da0bb0b9, 0, 0x93, 0, 0x4de, 0x4df4da2ac]
  | 39 => #[0x4da, 0, 0x4e24d03ad1bb1b91b81b6140, 0x81, 0x4e4, 0x4e5081, 0, 0, 0x4e84e7, 0x4e9, 0, 0, 0x4eb, 0, 0x22a, 0x4ef2b32b2, 0, 0x4f14ee4eb, 0x4e22b9, 0x4ef22a, 0x4ed22a00d, 0x4f12c9, 0, 0, 0x4f84d214c, 0x4f9, 0, 0x4fb, 0, 0x4fd14e, 0x4fd4fa14e, 0x4ff4fa]
  | 40 => #[0x5004ff4fa, 0, 0, 0x4d11bf, 0x4d44d14a31c01be, 0x1c61c31540be0bd, 0x5061c71c61c40be0bd, 0x5060bd, 0x1be148147010, 0x50950422a, 0x4044011d502c02a029, 0x50b40402d02c029, 0x50b404, 0x50b4042f5, 0x1ce1cb, 0xd5, 0x210, 0x30d165, 0x3ce3b61ce1cb, 0x506153, 0x5085062d41c51731541530bc, 0x157, 0x2d6, 0x152, 0x3b12d5158156097, 0x5141c7153, 0x3ce3b615209d, 0, 0, 0, 0x51e, 0x51f51e15c15b]
  | 41 => #[0, 0x521, 0x522521, 0x43c, 0x522088, 0, 0, 0, 0, 0, 0, 0x52b, 0x52c41c, 0x52d, 0, 0, 0x530, 0x53132f, 0x532, 0x533, 0x53250d404, 0, 0x53250e50d50c50b, 0x5355345334244232db, 0, 0x5391d702d02c02a029, 0x12, 0, 0x53b1cf166, 0x53d1d2167, 0x34033030, 0x53f]
  | 42 => #[0x540, 0x21b21a219218, 0x542, 0x1e31e10d9, 0x396, 0x1e01dc1760da0d7, 0x30, 0x36, 0x2fe1790c30c0, 0x3cf, 0, 0x3cf33209e, 0, 0x54a, 0x54e333, 0x547180, 0x54f, 0x55054f54753f, 0x54f332, 0xbf, 0x313262, 0x555, 0x261, 0, 0, 0x555262, 0xad, 0, 0x89, 0x55d, 0, 0x55f]
  | 43 => #[0x1e2, 0x56121b0da, 0x561089, 0, 0x56455f, 0, 0x566, 0, 0, 0, 0, 0, 0, 0x313, 0, 0x56f, 0, 0x571, 0x57242617d, 0, 0x57457156f, 0x12b, 0x4b239230225a18e10d, 0x57746644041019018e, 0x57746546446345a422, 0x40f00a, 0x57a40f40e40d25b25a259, 0x57b4b225c25b225, 0x57a45940e0ed0e9, 0x480199, 0x57e495481199196195133, 0x57f57e495199136]
  | 44 => #[0, 0, 0x58203b00b, 0x583, 0x58458349327d03c00b, 0x58458347b416, 0x58458103c03b, 0x587583582, 0x588, 0x5875835821ae00b, 0x58a, 0x58a1ae, 0x581, 0x1ce, 0x58e513, 0x58e50f5075061cc1ca1c8, 0x501, 0x5133ce, 0x5925133ce, 0x593, 0x59458e1ca1c9, 0x5172e12e02d72d6157099, 0x3b12d7159155, 0x159, 0x1d2172167, 0x1c71c31c2174, 0x51d, 0x508507, 0x59459058e5085071c9, 0x59c, 0x59c59450f, 0x59d598595516514156]
  | 45 => #[0x59559451551450f3202d41cc1ca1c91c8178174156098, 0x58e50f3b7, 0x5a259458e5133b2155, 0x5a35195182d5, 0x5a45a359459359258f50f3b73b53b31ce1cb158155, 0x5a5513, 0x5a551c3b6, 0x5a65a559359258f3b53b4, 0x1c2173, 0x5a9, 0x5a65941ce1cb, 0x5a71c61c4, 0x5ac5a75a65a25a159e51d51c51b51832409d, 0x5ac5a251b1c71c6152, 0x522088085, 0x51f0d60d5, 0x1d1, 0x5b1, 0x5b23f11d1, 0x3f1168164, 0xc2, 0x219, 0x5b6, 0x1f9, 0x5b81f9, 0, 0, 0, 0x5bc, 0x5bd5bc5bb5ba, 0x5be, 0x55354a3d3]
  | 46 => #[0x49048f48d, 0x4573bb3731150e80e50c6055, 0x4c73e03a0282281, 0, 0x5c4, 0, 0x5c55c4, 0, 0, 0, 0x293, 0x5c93f9, 0, 0x1a51a3, 0x5ce492, 0x5cf489488, 0x5d05ce492, 0x49229a2982962861320cc07a, 0x5d2, 0x4cc4cb308305228227, 0x58d5855814cf4cc4ca47f413305, 0, 0x5c1, 0x5d6, 0x5d8, 0x5d9, 0x5da, 0, 0, 0x5dd, 0, 0]
  | 47 => #[0, 0x5dd, 0, 0, 0x5e319a, 0x3e73e63e32a5, 0, 0x5cd5cb3e53e1293133, 0x5e75e63e33a52a5, 0x3f01a119f, 0x4894883f0, 0, 0x5d349448a3ef28826e2051a219d0c906c, 0x586309, 0x2a1, 0x5ee41600c, 0x30728e228061, 0x5ef5ec47f28c, 0, 0x1ad, 0x1ad, 0, 0x48c, 0x2a2, 0, 0, 0, 0, 0, 0x5e0, 0, 0x4e14df4dd4da3eb2ae]
  | 48 => #[0x4981b5, 0x6016004e34d63b03ac3ab3a83a72ad, 0x50a5055044f44f32b92b6, 0x4df497, 0x4f04ed41714a00d, 0x6044e04972ac1b41b21b0, 0x417, 0x6064971b113f, 0x4e40cf0ce081, 0x4dd095093, 0x4e72af209208, 0x20d20a209, 0x49b, 0x4ed, 0x4fd, 0x3fe3fd3fc, 0x4a8, 0x60f5024f8, 0x20e20b0d0, 0x20e, 0x60c6094e84e64e549e2b1, 0, 0x49d, 0x60b4e749c2b0, 0xe00d, 0x49f07d, 0x4aa, 0x61b4aa, 0x4aa, 0x50530a1bf, 0, 0x4db138]
  | 49 => #[0x95, 0, 0x6222b2, 0x62230b, 0x4f2, 0x419, 0, 0, 0, 0, 0x629, 0x3ae2cc13a096, 0x4e34d53ae, 0, 0, 0x1b21b00ba070, 0x4e914414307f, 0, 0x49c143071, 0x49f, 0x4a12d1, 0x2c11bd1bc147146076, 0x63349d143, 0x6374d7, 0x6386374d7, 0x6194f62f62ca22b, 0x509148, 0x50530a1c01be1bc149147, 0x6252c2149, 0x63d63b63a50941a149148010, 0x509, 0]
  | 50 => #[0x640, 0, 0x640523522, 0x643, 0, 0x645, 0, 0x647, 0x648, 0x6436422ee, 0x64215f15e, 0x33f33a, 0x45838025b25a104103, 0x30c25e, 0x5b35b230f25f, 0x4ad43a2872531300cd07b067, 0, 0x651, 0x6274a414b, 0x4a4, 0x21215a, 0x2fb, 0x3f11d1164, 0x65752d5283f11d10a3, 0x2fd, 0x6595352f4, 0, 0x536, 0x65c171, 0x17217016f16e, 0, 0x65b16d16a]
  | 51 => #[0x5aa3b73212df, 0x5aa5a859b59a58e5183222e0098, 0x6625ae5ac5aa5a95a851c, 0x1d9, 0, 0x2e4084, 0x520084080, 0x6410d4, 0, 0, 0x526, 0x668511, 0x6693292ec1600d50d40d309a, 0, 0x163162, 0x66e, 0x66e53b30d2e82e72e5, 0x66f66e53e2e92e6012, 0x1da1d6, 0x673151, 0, 0, 0x665325, 0x64b, 0, 0x5b0, 0, 0x85, 0, 0, 0, 0x67e6702e5162]
  | 52 => #[0, 0x67f67e5b35b1, 0x682657, 0xe00df0de0dc, 0x313262, 0x685, 0, 0x358, 0x6861ea1e91e81e7, 0x686, 0x68a689, 0x68b, 0x68c, 0x558343, 0x1e7, 0x3622f8, 0x628, 0x691, 0x6926914f7, 0x2fd, 0x6915014ff, 0x695, 0x6954fb, 0x696695629628, 0x69453132d, 0x39035, 0x69a, 0x5d94c148e, 0x69c5d95c848e, 0x69c4bf, 0x6496461e41e0, 0x5b733c]
  | 53 => #[0x562354217, 0x21b, 0, 0x5443562191e3, 0, 0x6a507e, 0x6a64e408107e, 0, 0x6a8087, 0x6a9087, 0, 0x6a31770db, 0x46146045c42241111e11d, 0x58d5855845811ad03c, 0x6825b35b1013, 0x41f3cd3011f5017, 0x6a76a66396326312cf2ce, 0x6a76a66a5, 0x6342cf07d, 0x47147046d469454, 0x65a5355332f42f2, 0x6b565f65b659423, 0x6b616f, 0x69b039036, 0x572, 0x456427, 0x113111, 0x5a65a1507, 0x5a65a15945901cd, 0x6bc5a65a15945901cd, 0x6bc5ac5ab5a65a45a25a159551c51a519516323157, 0x6bf6615ab5aa5a85a45a15945905173b73212df1cd157]
  | 54 => #[0x6c06be6bc5ad5a65a059e5941ca09c, 0x6c16bc6636615ab5a059f59d59a, 0x6c26c16bd6615ae5ac5aa, 0x6c36c26c15ae5ac5a2323, 0x6c46c36c16c06be6bc5ae5ac5a7, 0x6c46c21c71c6, 0x6c66c55a55a251d3ce, 0x6c45ac431034, 0x6c76c46c26645a65a559b59359258f3b72e1, 0x6c96c76c56c36c26c16bf6646635a359959751a514, 0x6ca6c96c76c66c56c46c36c16bf6646635a359959751d159, 0x6ba44a397, 0x541, 0x55c3de, 0x6cd5593dc3d6, 0, 0x6394ea, 0x16115e, 0x25d, 0x6d32da1d1, 0x260, 0x6d552e52d, 0x6d652e, 0x6d764e, 0, 0, 0, 0x6345e74693f02a91d712a11e118114, 0x1ab1aa, 0, 0x5e95e75e62a6092, 0x63c2d3]
  | 55 => #[0x63f60e6076054182b714a, 0x67f, 0x41b30f, 0x6e2, 0x6af013, 0, 0x41b1d2, 0x6e56e36af68267e310, 0x1a1, 0, 0x526161, 0, 0x527, 0x53e53c53b, 0, 0x32e, 0x54f54e54733433318109e, 0x6f1, 0x54d3d109f, 0, 0x1e41e01db0d7086, 0x6f456355e, 0x6f66f433d086, 0x6f76aa, 0x6f76a96a469f64c647645355, 0, 0x6a069f33c, 0x68e1ed, 0x341, 0x556394311, 0x68e015, 0x68b]
  | 56 => #[0x69b, 0x344, 0x5ba1fc1fa, 0x4251fd1fa1f817d, 0, 0x705, 0x55454934c, 0, 0x70554003002f, 0x6a9648, 0, 0x70b, 0x68a41e, 0, 0x68b68a41e016, 0, 0, 0, 0, 0, 0x3cc1f41f3, 0x70c68941e016, 0x71670d70b68c68a56e555, 0x71771668b, 0, 0x719, 0x35c35b, 0x17c, 0, 0x71d, 0x5bf574, 0x71f5b95b8574]
  | 57 => #[0x71f71e5bf5be5bd5bb, 0x53f, 0xc3, 0x56554221b0da, 0x565560, 0x72355c0c1, 0, 0, 0x56c, 0x40c2192180a9, 0, 0x17708a, 0x4d30cd0c8, 0x361, 0, 0x690688, 0, 0x731395, 0x7322f8, 0, 0x734, 0x735, 0x735734, 0x737, 0x367, 0, 0, 0x73a739367, 0x5be, 0x73b72071e, 0x73b364, 0]
  | 58 => #[0x409363, 0x426408407349346, 0x572548036035, 0x73b73a, 0, 0x45743a4394373ba370183, 0x74643a37118a0ac, 0x4573bd3bb128101077, 0x7464574383bc3b9, 0x7494364354343b9, 0x57c57b57945a25911b1061040ed0eb, 0x44b, 0x6ba4560e0, 0x74d6cc68411211010f10e0f50b50b208c, 0x4323681261250f8, 0x74e6840df0dc, 0x75074f74d24308c, 0, 0x3bc128101, 0x7494af43c43b118116078, 0x57710d, 0x46e46942c3c13bf1930f00ef044, 0x7566b447247146f45444e4293c738d38a388387239237236, 0x75645e45d3f23c038e10c109, 0x114, 0x57645345223e0fb0fa0e404b040, 0x4520fd0fc, 0x7555294b34a325a255240, 0x75a74a7474531881870c7, 0x74774643d43a375374370221, 0x7494ad436435245224115079, 0x75a45345243822420318d]
  | 59 => #[0, 0x57746546243e249, 0x4784764684554462f9258, 0x7636b446f40a3cb, 0x7637566b448547647346945e44e44c42938a38912910b0f3, 0x6c5, 0x76246643f41039024b19018f006, 0x46145c, 0x45b0ee0ec0ea0e9, 0, 0, 0x482267, 0x75e75d75a7534b04af43d3bd247, 0x75f74a7474ae43b4391891871160fb04d, 0x5ed48a27626e026025023, 0x76f4943ef2760c4, 0x77049247c29e, 0x47f, 0x490, 0, 0x774490, 0x490, 0x76b4b54b43e83e53e239f39b19813608f, 0x309229131069, 0x7745d94c149048e, 0x5c54ce, 0x5ca491, 0x6825b35b1168, 0, 0x5b152a, 0x76a5804b84b626826708f, 0x5e85cd]
  | 60 => #[0xb8, 0x5804b5198136, 0x77258a4ba, 0x7835854154141aa1a91a803b, 0x7836ae58d4ca47f28b, 0, 0x5e05df5da5d95d8, 0x48f, 0x482, 0x7717705ed287134, 0x3112611e71e5, 0, 0x692, 0x15014b, 0x6b8, 0x6924fa4f9, 0x6a95b7, 0x79171440c, 0x6a91e1087, 0, 0, 0, 0x795, 0, 0x149146, 0, 0x1e6, 0, 0x5891a9, 0, 0, 0x53632e]
  | 61 => #[0x5bf5be570, 0, 0x7a2, 0x7a37a24de13f, 0x7a34d0, 0x1a1, 0, 0, 0x3f029a29707b, 0xff, 0x89, 0x8a, 0x192191190, 0x624623, 0, 0x1f0, 0x7b0567566, 0x7b01f1, 0, 0x612, 0x14f, 0, 0, 0x7b44f914c, 0, 0x7b97b6171170, 0x7b9, 0x7bb, 0x7a0, 0x6da5e15df, 0x7bb6c15ad53a36f2f5, 0x7b74024011d81d61d4]
  | 62 => #[0x4a6, 0x75875648547646b45e45440a3c83c73c63c43c338810c10b10a01b, 0x7c27646b447e47646945d44738625812a129, 0x7c37c275847644844744644542c42a429428, 0x7c36b447147046e4673f53f224e, 0x7c47c375747946945d44f4473f53f225724f24d, 0x7c647546f42c42b3c22f9, 0x7c77c647546b46a42c42b2f9046043, 0x7c476475847e47746a44844544444342c250193, 0x7c97c67c47c375748546b4684544454433c93c33bf, 0x7ca7c77c67c57c37c275747647447046c4684544443f53f23c825624e24d24c, 0, 0x1bb, 0, 0x6c552b, 0x3d4, 0, 0, 0x7ad23f192, 0x7d346039330222511a, 0x7d364d57843e38137c31c319, 0x6d95f74ce060, 0x7b36d95f75c74ce291, 0x7875e25e15e05de5da, 0, 0, 0x7d969d2aa, 0x7be7b35df, 0, 0x6394e8, 0x4e84e649f, 0x5055044f24f14ee4ec4eb]
  | 63 => #[0x60e, 0x63f, 0x79779563c61e, 0x73652f, 0, 0x7b87b44f714c, 0x6105034f83fc, 0x4fe, 0x61060f4fe, 0, 0x7d457946111d1060ed, 0x64d39139038137e37c25c105, 0x7eb7ad74b39038f37d37c37b25b22e22d18e, 0x7ed7eb7ad76264d57846546239138f24a24918b, 0x7ee7ed7eb7ad75574b64d57946545944140f39138f38331d25a24a24011b1061041020ed0ec0eb0e9042, 0x7ee7d576964d57d57945a45945840d3841071060ee0ed, 0x7f07ef7d47687676ad57c4b1411302, 0x7f17f07ed7ec7eb7ad76976857d57a45b39339038f38237f37e37b37831c31b31931731622319218f18c, 0x7f27f07ee7ed7eb7d57d47d37676ad4b1411393392007, 0x7f37f17f07ed7eb7d576257845840e3be31e23f, 0x7f47f17ed7eb76274b57c57b57857745b40f40e39138f38438338031e31d107103102, 0x7f47f27ee7d46ad57d46639025c24b, 0x7f67f37f07ef7ee75557745841040d3be, 0x7f67f57f47f07ee57d40f40e40d10d00a, 0, 0x48d3f7, 0x78a77026d1a2, 0x7fb7a95d14884831a31a2, 0x5fe5fd, 0, 0, 0x7ff]
  | 64 => #[0, 0x7fe781198133, 0, 0x803, 0x804, 0x7895e6293, 0x8067815c34c94c44c30b7, 0x8075c357f4c94c64c3482, 0x8088074c64c319512e, 0x8088067fe76c57f480, 0x80a80958057e480136, 0x80a80957e4c54811960b7, 0x80c80b580495, 0x80d57f57e1990b80b609108f, 0x80e80d80b80a809495199, 0x3fb3f83f73f6, 0x810, 0x801, 0x80048f, 0x418, 0x7af, 0, 0x63a5094f62f62ca13900f, 0x816626419, 0, 0x819629, 0x63b4f62f622b14813701000f00e, 0x6396374e7, 0x7af63f4eb, 0x42f36d36a0f7, 0x6213eb, 0x3ed1ba1b7]
  | 65 => #[0x8204d64994983ed3a92bb, 0x419418, 0x4f93ff3fe3fd, 0x8234f93fe, 0x8244ab4002c4, 0x824823, 0x826, 0x827823501, 0x7b5, 0x7e97e561d61c6164fc, 0x8296984a9, 0x7e55914fd4fb4f7, 0x829790, 0x82d14e14c, 0, 0x67166f, 0, 0, 0x677, 0, 0x82f77e6d86836575b45b35b21d116409b, 0x16e, 0x170, 0x30f25f, 0x1d0, 0x6b76b6531530423, 0, 0x7b1, 0x8a, 0x83d72c0db, 0x83d55e, 0]
  | 66 => #[0x7ac, 0x7b01eb, 0x8421ee, 0x79c72f690, 0, 0, 0x737, 0x56355d0ff089, 0x564543, 0x849, 0x84a, 0x3cc2f71f4, 0x569301018017, 0x573571, 0x84e54817c, 0x84f84e, 0, 0x5b75b640c219, 0x793, 0x8535615465443571e30ff0d9, 0x552, 0x8555521800c2, 0x85555235034f338330, 0, 0x6865681ea, 0x8595681ea, 0x85a1e71e5, 0, 0, 0, 0x7a173f56f, 0x73f735364]
  | 67 => #[0x3403203102f, 0x8616d0, 0x861541540, 0x86370870654f54e54153f, 0x86355c5415400ad, 0x8630c2, 0x85884b6fb6fa543, 0x8537aa6ab0ff, 0x3cd3cc1f61f4, 0x8698438423cd1f11ec, 0x86a8453cc1f51f2, 0x84d6b0301017, 0x85084f71c, 0x86d84e72171e71d71c, 0, 0x86f, 0x87086f85f71d5b9, 0x871711, 0x85b78b5565552f7262261, 0x86b7323cc2f81f71f4, 0, 0x875, 0x7c847002c, 0x576, 0x85b3942f71e6, 0x87876e74974657637337237121f0c50ac, 0x87a76d75f75d7475c25764ae37224621f21e1171000e7053, 0x87876075f3bd3bb, 0x76043d43824822418d189188, 0x87b7f47cb76e76175e75d74a5c24b043a2532521171150c704e, 0x87e87d87c87a7f47cb76d76176075e75a74a5c24352482472452440c7, 0x87f87b8787537494393bc1281161010e80e6]
  | 68 => #[0x88087f87a8787494573b93721281000e70c6077, 0x88187f75f74a747438, 0x88287f87b7545763760f9, 0x88388074943c1180fa078, 0x88488288187f87c87a87876d75d7537497484ae4ad436435252251244, 0x88588388288187f87e87b8787f67f57f37ef7ca7c77c67c576e7587557547537523be, 0, 0x4d941941830b, 0x58928f1ac, 0x5004f94003ff, 0x88a591, 0x88b8275014ff4d2, 0, 0x88d6d267a52015d15b, 0x88d5b0085, 0x6d464f3f12da, 0, 0, 0, 0x7ba40b, 0, 0, 0x84b849714218216, 0x897, 0x574, 0x7a1572, 0x5be, 0x433430, 0x89c6844300e10e00df0dc, 0x5b5034030, 0x89e8967263da3002ff1ff, 0x89f8950c2]
  | 69 => #[0x8a089e7265b535f35e2fe0c30ae, 0x8a15b5, 0x8a089f896726, 0x8a272635f17a0fe0ae, 0x81e, 0x8a08950c2, 0x87985a5674201e81e6018, 0x83c79b, 0x67465940b2db, 0x89b7a16b956f, 0x8aa89b89a56f, 0, 0x8ac, 0x8ac7b9, 0x8ae8ad7bb53953440136e, 0x8ad7bc7b96b565a53753553450e50c404403, 0x8ad83640b, 0x872871870710, 0x6440d5, 0x6825b12ef, 0x8b46825b1, 0x8b18b08af8a98366f040b, 0x45f4500b4, 0x8b58b489168364f5b4, 0x8b88b58b48916835b4, 0x8b98b81d0011, 0x8b93f11d21d11d0028011, 0x86a846, 0x8328317c06756731d6151, 0x676402, 0x8b18a98366ca67466065b538535533530, 0x8be7c07b6676402]
  | 70 => #[0x8c08376b76b62dd2dc17116c, 0x88881d, 0x7e063f4f500d, 0x83a7a032f02e02d029, 0x8c483a7bd52f1d7, 0x8c583a6995395315302fd, 0x8c48c08b07bd7bc7ba536, 0x8c48c07c07bd, 0x8c88c78c18af83617016e, 0x8c989483b831, 0x8c98c68c18bf8bd8944012eb1da, 0x8ca8ae83b8317ba7b6, 0x8cc8c98c88377bc, 0x8cc8c88c18b18b08af89452f, 0x8cd8c88c78c68c18c08376b565d50d4034024012de1d516c16b16a151, 0x8cc8c98c88b18ae8ad8368317c07bc7bb, 0x8d08ce8c98c58c08b18328317c01d91d61d4, 0x8d08c68c57bd02b, 0x8d28c47a053a5395361d7, 0x8d38d28c48b07bf7bc7a0, 0x8d28d18ce8c78c68c18b18366b769966065f539, 0x7cf52b, 0x8d08ce8c18c08376ca6b665e1d91d4172, 0x8d58d48d38cf8c58be832, 0x8d38d28c78c08b68b18ae8a989483b7bf7ba7b765c2fa171, 0x8d98d48d38d18cf8ce8cc8cb8ca8c88c58bd8ad8ac8946f069467567465a50d50c4032fd2fc2f12eb0a1, 0x8da8d98d88d08cf8cd8c78c08bf8be8378326b567665d5355324242de2dd16f, 0x8da8d98d78d58d48ce8c98c88c58bd8b68b08af6f0694675673, 0x8dc8da8d58d48d18d08cf8c78c18b18366ca6c16b76b666065e65d5ad53940236f36e2f31da1d91d81d6172, 0x8a0857549179, 0x39a11410f, 0x81e75074e48645644b44a44943139a113]
  | 71 => #[0x8a54ac45142d399398241, 0x8a543342d39924108d, 0x8214d64961b1, 0x49f49e, 0x4a63fe, 0x573, 0x8e65bf5be57457356d, 0x8e78e68ab8aa56c, 0x8e686d56d, 0x8e757357142617d03a039038037, 0x8e7571, 0x8eb8ab72957156c, 0x6b26a66392c82c60d107e, 0x6314d32cd20f07f, 0x8e48858848817ce7496b16a665049b49a142, 0x8e7847743737572, 0x8f08ea85d84f84771a704702701425344, 0x74c44b3970f50df0de08c, 0x6066026014e34dd3eb3ab3a72ae2ad093, 0x6213ad095, 0x8f381f7a57a47a36206086004972c51b413c, 0x6176132bd20e20b, 0x8f649a0d007d, 0x6d120c, 0x6d16374ea4d8, 0x8f98f78e481c7a74e949e49b2c72c62c02be, 0x7df60b, 0x88f88d5af085, 0x8b388d6ea522088085, 0x8fc88d67a5af52551e5102ed2ec, 0x8fc5af525510, 0x6ae58d306]
  | 72 => #[0x900587584, 0x90190088979d78658758558449347d, 0x9019007945f558758658447b41600c, 0x90258758503b, 0x902785783, 0x90590488979d7725885855845835824bd4ba49347d30327d279226058057, 0x9027865d44cf308307228, 0x9079067855d45854cf4141aa1a8, 0x81422b137, 0x85b78b, 0x712406396, 0x8a085771354917e, 0x8a68a38a28a186286172354117a, 0x86655b, 0x8a0866857549, 0x8de8628617133db3d73d5, 0x90c8a2726, 0x9115b50c2, 0x8bb8b96ed681, 0x7a57a47a37a24d03ad1ba1b81b6095, 0x9148e381f7a57a46204dc1b21b0138, 0x91591481f4dc4db1bb1b91b7138, 0x9168e37a57a4, 0x9179168217a34d54d01b1, 0x9187a5, 0x90590390179d7857786ae5ef5ec58d4cd4ca47f41330629028c28b03c, 0x90488958c4bd4121ae063, 0x91b90490290188958d5855814131ad, 0x91c9049029015f141541430628d, 0x91d9049015f158558241530328d27c22613112d059, 0x91e90290179d5855814cd4132901ab1aa1a91a8, 0x91e91d58858658227f27e]
  | 73 => #[0x92091f91e91c91a9089069057847726dd5f25ee58a5884be4bb4ba48b41227f12d00b, 0x92191e9089069059049039017787725824cf4bc48b41230427b, 0x91891691582081f7a36086024e34de4993ed14013f093072, 0x9239189169159148f482160a6066016004d54d03ac13d, 0x9159148f481f7a46214db1bb1b7138, 0x9128a68a089f8958636ce6cd3de0ad, 0x9268a089e3da, 0x92091f91e91d91a9087947846dd5f25f05ee, 0x9199164d5, 0x9294d63ae3a9, 0x92a92591691591462c60a2cb, 0x92a9198e362e1af, 0x92c9259159148f48e381f63062f62e60a4e313e096, 0x92c92a9259199177a5, 0x92e92a9299188214d64d54d0, 0x92f92c9299259189178e37a262e4d63af3ae3ad3a91af, 0x92f9259249238204993ed3ec2bc1bb1ba1b8, 0x93193092f92e92c92b92a92491962f13a, 0x92f92d92c92b9259249189178f58e381f4db4962c51b31b2, 0x93393292f92e92c9299239189179158f362d497, 0x93492f92e92b9299259238f48f362d4983eb3ea2cc2cb13e, 0x93593493192f92e92d92b92a9179158e363062c, 0x93693593192e9249189179158f38204e34d04994982bc2bb, 0x93793192f92d92b92a9249167a57a462c6204db, 0x9389379369349339301bb1ba1b9, 0x93993593492a62d, 0x9368197cd503, 0x93980e8088067896c84822a6, 0x77f6df3e9, 0x93c80e80c80876c76a, 0x93980e80a8076c85e557e4c54812a3197194, 0x93c93980d80c80a8077fe7897826c85e457f4c52a42a3]
  | 74 => #[0x94080f80e8088067fe78277f76c4b84b5198, 0x94093e80c80a80680278178077776a4b84b74b64b43e93e83e53e23aa39d39b269268, 0x93d7cc77f6df5e95cd, 0x9219079039029008897785d54cc4cb2271ad, 0x9449089039024154142a7062, 0x94594491c90890179477858c58b27b12d, 0x94694592292191e90388979458b5824cf4bd4bc47a3043032261ae, 0x94794694592292191e9019008895f4229, 0x9489459289201ab1a9, 0x94994492879d5f358958447b, 0x94a94694492091f91e91d9039019008897945f45862a9, 0x8b88906d325d, 0x8bb25d1d1028, 0x94d8b98928386ec6e76e36e25b35b241b013, 0x94e52a168162, 0x8386d56d351231430e30d, 0x8396ee6e553b52d52c41c, 0x94b94894592191e9069059027f87f57f279d78678375c5d45895854933072a02292281ac068, 0x95294a94894794692291d91c91b91a9089049038897f87f57f279d78475c5f55f45f35f25f05ec58747d47b2a806a, 0x8e57e778c, 0x4ee4d94d44d1, 0x95581b63f60550a4f04ed41722a, 0x95581d7af6255094f64d94d44d12f62c9, 0x9378f88ee8ed8858848817ce7496b36506396346326314d32d013b, 0x6de, 0x8f781c6de63761a4ea4e9144, 0x81c7de6384e74e64d84d72b0, 0x9598fa8f88ee81c7a76396386336324d32cd, 0x95b6d16a76a66a54d807e, 0x9578c28888156354a0145, 0x95e95394a94994794492892291d91c91b91a9079069059049037f87f77f57f47f37f17ef7b278576763f6355f05ef254, 0x95e7996361be1bd]
  | 75 => #[0x8da88e6565203292ed2d815c0d3, 0x8fc67c, 0x67d678326, 0x88f67d67b5b05af5100d5, 0x9648ff8fc8da88f88e6eb6ea52551f0d6, 0x8ff8b3669510, 0x9138bb8b8681527, 0x9678ba89332b014, 0x94e8dd8dc8d98b58916d665864f5b452e52d528, 0x83c7b27b17176fd5673411ed, 0x86a8437b271770c1f0, 0x8a77b27b171670c70b5661ec1eb, 0x87178f6b869b69a353, 0x8f18f087685d84f84771a7047011fc, 0x86470870654d3d3, 0x9128a089f8956ce5593de3dd3db3d93d8, 0x96f8646f309f, 0x91191090d90c8a38a28a186285172355c55b5400fe0ad, 0x96f9278a48648516f355b3da35e0fe0ad09f, 0x9739128de8a0895, 0x974971331181, 0x97096f8de8a489e8648627096f25543d4350, 0x9759749729719119108668648567077067055543d434f34d33609f, 0x9779749118a6, 0x97892792691190c8a689f8627136d053f17f, 0x97997797297192792691290f90e8de8a28a18a085785155454934c34b17f17e17a1790ca0c10c00bf, 0x97a9779129118a28668655b52fe, 0x97b97597196f92792690e8668638557226cd5c055b55234b3311810c20a5, 0x97c97891190c86117a0fe, 0x9689678ba8936ef32c, 0x96894d8b889289183983883582f77e6e86e36e26d86d467f67266f527, 0x8b58b46d76d66d464f64e5b452e528]
  | 76 => #[0x98097e6ee6e552c014013, 0x9699688dd8dc8d98b589352a, 0x98296894f94e8928906ec163, 0x98398294f94e89083082f168, 0x96896794e94c8936d532a260, 0x98598395094c8b98b883877e77c6d36825b352951231531431030e30d2e725f25e25d165, 0x98498398298197e96995194e9138b98b58b48918396e86d764e53e41b2f02ea, 0x98798698598497e96894f94c8ba8926ee6ed6ec6d552d52c52a52941c32b32a, 0x98498196994e9138dd8dc8db8d98ba83983582f77c6ef6e86e76c952b2f02ef1d31670ab028, 0x98998897f95195094d8db8306d46d36c967151230c2e92e6, 0x98998498298197f94e8db8ba8b98b589183983577c6e76e66c96af53c2e81d0166013012011, 0x98b98a98998898698396894f94e91389265852d527260, 0x98c98a98897f95195094f94c8db8ba8906ed6d36c968153e53d1cf168166165163162, 0x98d98a98798498097f97e94e8db8ba8b98b88906c953e53d1d3028, 0x98d98395594994892881b7f87f57f263b5f352c4b3, 0x98e98c98a98895f8888156352d2, 0x98d8da6d2511210, 0x98b9839689138d67cf65852e52741c014, 0x99095394291e91c91b7705ca5c94cd4c949447c3ef3ee, 0x89886885884b6fb6fa6f76f56f45461e41e01dc, 0x83f, 0x95a9378fa8ef8ed7a76de6b36b16a66a56394d849e2c82c7, 0x90b8b287278f405037, 0x89884a8486ab5441e31dd, 0x85284b7926485b63511e10d8, 0x99989884a849792356, 0x87986c72856b, 0x8f086e86d850740739409, 0x87084e72171e17c, 0x99d8eb8b289b87687185f85d7a173f736735, 0x89a876875872870710570, 0x87979b420018]
  | 77 => #[0x3cc1f51f2, 0x84579b56a, 0x99a86885284b7915b75b61e10d8, 0x9a399a86885485284b79172a6ac6a26a05b75b656254233a21a216215, 0x99a9948988688527936aa5461e10d8, 0x91187986c728, 0x9555094f62f6, 0x9a795590981b814, 0x6ba456, 0x7a97705eb5d15cf49448a47c29f29d277274, 0x7fc7fb7a65ea5d01a41a21a11a00cd0cc0cb, 0x9ab7a95eb5cf29d29c, 0x9ac9aa7fb7a95d35d049229e29c29b299286132, 0x9ac7a62071a1, 0x9ad9ac7fb5d22060cc, 0x9af9ad77176f49447c29f, 0x9b09af9aa7fb5d1, 0x9b19b09ac7fc7fb7a678a5d249220619f19b13012f, 0x9b19aa7a678a5d1488484, 0x9b39b19b09af9ae9ac9ab9aa94894791c7fe7a977177076f4be4b948a278272271204, 0x9b49b29b19b09af9aa94894791c7fe7fc77177076f5ed5ea5d35d15ce4be4b94894882952782752722702072041a71a519c065, 0x9b59b49b195394294093d93c80f80e80c80b80980680278278177f5e85cb495294293292091, 0x6da491, 0x97d97b97997897597092691291190f8de8a08988678638628578557227096f16cd5c0554552551547339330, 0x9b897c97b97a97897697390f8a089f8988958678668658567087076f155354f54c54a3cf339337, 0x421, 0x89d87e7526844270e10dc, 0x8007735c14c0, 0x8138058047885dd5c6, 0x5de, 0x8007db77969d69c4bf, 0x9bf8137db7795c8]
  | 78 => #[0x9c08118058035c13fa3f9, 0x9c17fa5c148f48d3f83f7, 0x9c19c08117885de5c1, 0x9c39c28017ff, 0x829790502, 0x95d95b8f88f67de7a763861761360b2bd2af20d, 0x95d81c6374ea4e94e8, 0x9c795d81c7de63963863761749d, 0x9c89c79c695d8f76a761560d4e449a0d00ce, 0x9c99c87df61a61560c4e64e549f2b1, 0x9ca9c99c79c695a8fa8f67a761320e20d141, 0x9cb9c79c68f66150cf08107d, 0x8277c14fa14e, 0x85984472f5681e91e6, 0x85b85a7151e8, 0x9cf86a8698431f31ec, 0x9d09cf84279a41f3011ec017, 0x9d18a88a787985a84c5673941e81e6, 0x9d196b96a87385a84c7176fe41d3111ed, 0x9d29d19a29a19a08a787987384c83c56a569566, 0x575, 0x86d85e407, 0x9a37ab7aa6aa6a90ff08a089087, 0x5ba, 0x9d88b28728707105bf5bd5bc5bb5b8, 0x9d99d85bf5be1f9, 0x9d88755ba1f9, 0x9d99d85bd5bc5b8, 0x9d98f18eb8757a1570, 0x9dc9da8995ba1f9, 0x9de9d95bf575574, 0x9df9de9da9d81fd1fc1fb]
  | 79 => #[0x9de9d98ec8e789a57557456f, 0x9e19df9de9d98ec89b5bf573570, 0x84983e72e, 0x9a589786885884b7aa79270a6fb6f96f864933e, 0x9e49a58978688678548407aa79272572470a6fa6f96f8649646645565560, 0x9e585483f56355e5431760da, 0x9e59e39d79a59a399a99899489786885384984884183f83d7ac72e6aa6a856455d360, 0x9df8e98e657556d408, 0x9b999c8f087786e8507d2744740739, 0x9e89e19dc9d98ec8e98e88997424073493483451fd1fb1f8, 0x9ea9e89e29e19de9dc9db9d899f9975bf5be5bc5bb545406396039038035, 0x9eb9ea9e29e09df9d599d8eb89b89a57056f, 0x9ec9eb9ea9e09d999d87086085e71f5b9, 0x9ed9e19d98f087187086e86085f85e85072171b71a54835c, 0x9eb9ea9e09df9db9da9d89d599e99c96e96d8f087686f78f72971c71a7197026b835d35a0a80a6, 0x9eb9ea9e89e29de9dc9db9d899f9978f18ea899704545426425348347345, 0x9ef9ee9e89e29e09de9dd96d90b8b278f545405353, 0x9f19df9d87125ba1fd1fc1fb1fa, 0x9f29f19ec9e89e29e19dd9db9da99796d8f18ea54534a347, 0x9f29f19ef9ee9de9db9d899e96d8f086e85d84f84772171b71a7037027016b956c35d, 0x9f39f09e19e08f08ab8aa8477437387296b9, 0x9f59f49f39ef9ed9e29e09de99f99796e90b8f18ea8e670342640539634a346, 0x9f69f19ef9ee9ed9ec9e09df9dd9db9d599f8f08ab8aa87687186f86e85d85074373873472171b7196b96b869b69a, 0x9df9d59b97d2744, 0x9f79f39f29ef9ec9eb9ea9e29de9dd9dc9da8b28728717d07115be5bd03a037035, 0x9f99f79f69f59f49f39f29f19ed7d0, 0x9fa9f99f69f59f19ee9ec9eb9da9d87d01fd1fc, 0x9fb9fa9f79f69f49f39ed9e89d69b985e7d2745575, 0x9fc9fa9f69b97d2, 0x9fb9fa9f79f49f39f29ed9dc9da9d97d07125bf5bb5b8, 0x9fe9fd9fb9fa9f99f79f59f49ed9ea9de9dc99c90b8ec8e98e887785074574273f73e73a738736409365, 0x9ff9fe9fd9fb9fa9f99f79f69f39f09ee9ec9eb9ea9e89de9d999c8ec8e98e887786d74274174056d545408407406]
  | 80 => #[0x9e69d7854840725562542, 0xa009fa9f39f099298e8db8d98d88d68d583a59146c186, 0x9fc9b99928d67d2479, 0xa039b99929378857cc766479, 0x9cc9ca9c99c795d8f77df6a761a60d609, 0x9cc9c99c66d1615, 0xa059cb9ca9c79c69599588fb8f88f68ed8858848817496b36504d349e2d02ce0d2074, 0x9916d2511210, 0x71870e68b, 0xa069c89a79389379369359329319308208144ab3ec, 0x90941822b00e, 0x78c, 0x68a, 0xa0d9ce85b79c79a7156906896851e6, 0xa019fc9e39a48988407ac72a6ac6a3, 0x8ff8fe66a666084, 0xa10a088ff8fc7a867c67b66d66c66b6562ee161, 0xa11a10a0898d8ff8fe8da7a86566415112d9, 0xa1298a9669639628fd67d6785af0d5, 0xa138337a8, 0xa129668fc8b388d6675255222e4088085084, 0xa15a14a11a109918ff8fe7a866c66a66966652552251e2e30d4, 0xa1198d8da88e6eb526523522328, 0xa17a12a10a0898d98a9629618ff8fe8fc88f67a6676665b05202e22d815c15b, 0xa17a13a11a0898d8da66b21116115e15a, 0xa19a18a17a14a13a11a0899198d98a96588e83467967766565564015f, 0xa18834, 0xa19a16a15a10a0898d98a9629618fe83366d66a0d4, 0xa19a13a1199183466c66b668, 0xa1da1aa16a13a10a0898d98a9649639629618fe8fd83366d6686446426416405112fb2d915f15e, 0xa1ea1ba19a18a15a12a1098a9659616796656555112fb21221115a, 0xa1ca1ba1aa15a14a12a0ba0aa06a019ff9fd9fc9f99ea9e79e69cc9b99b89b69a799698b98a98797e96696596496095895795594894794494293993693391f9098da8d78d28c38c28a38a288588488288084684183e7f77f67e27d47d37cf7ca7c87c27ac7697647637447266ef6e16e06dc6c56c46c16ad5ad5a65a159e53a4c84b047e45d44f447446386324]
  | 81 => #[0xa1ea1da1ba1aa18a16a14a12a0fa049cb9b59b299198d96696395c8da88e8858848838828807fc6e967b64a6445225213283272140d60a2, 0xa1da1ba19a18a13a0fa049cb9b59b298d98a96595c8858848838828808337fc6e967967765551132521315a, 0xa22a1ea0fa049e39b39a499a99989888588388287d87a79272d72a6a43610db0aa, 0x8227ae799624623075, 0x88c825, 0x88b88a78e652, 0x8188164d94d1, 0xa27a0b8187e179763f61f5094f5, 0x9ce9a18bc87987484c2f7, 0x93681a7cd78e, 0x9b59b49b195394293f93c80f80e80c80a8088067805e85cb5c34c74c63e9283282, 0xa0494294193c93980f80a8098077cc7896c85e357f2a4, 0x97a93a8e08a481e75074e74c6cc6bb6ba5a648744a449431427397, 0x9a98b78a589c87e0b4, 0x5f6, 0x9c09b78138048037dd7d677a7795c95c55c4, 0x8878105f8, 0xa2588c824400, 0x9c39c09bf9bd7db7da7d87875db5d6, 0x9c39bd8115d75c13fa, 0xa349c39c19bd6da5e15d75c13fa, 0x7ea78d692, 0x78d692653627, 0xa37a2aa0c93681a7cd4ab150, 0x828500, 0xa3988b88a, 0xa3aa388287c15915014fa4a6, 0xa3a826824591, 0xa0fa019a484183e72b6ac69f35433b217, 0x9e586879171454654440c3572190d9, 0xa019e69e59d79a59a399a99899599486885384a84884183d7ab7aa6ab55e, 0xa3da019e489889779270a6a4647560355]
  | 82 => #[0xa40a3da019e69d79a599a8978588526f756454333f33e, 0xa3f9d79a37ac6a90ff08a089087, 0xa42a41a3ea3da23a22a1ea04a019b39a499588588388287d87a85385284183f83e79372d72c563543, 0xa43a3fa3d9e599a9998548407257246a455f, 0xa42a3d9e59e49a399a9998547aa7246f96f86f769f64c64964864656555f351, 0xa45a41a3fa23a22a1ea049b39a499888588388287d87a84883d72d72c3600ff08a, 0xa43a40a019e6841, 0xa46a45a40a3da1da17a15a07a06a05a049fc9e79e59d79cc9cb9c89b39a599899699599486883f7ab7936f66aa6a856355e55d33d, 0x9fd9fc9fa9f89d09b99787d1, 0xa3ca39a36a0c9c595482e82d82a7ea7e679062b6166114fc4fb, 0xa28a0b9558c37e363f60e50a, 0xa36a3293682c7ea7e67cd6936544f74ab4a4, 0xa319fd9fb9c198e8dd8dc8da8d78d08c66995f846d32d2fc, 0xa3ca398e588c82462a4a84003fd2c4, 0xa4ea3ca39a329547c14a9, 0xa4e8297904a714f, 0xa3ca3a88c88b82d8268247b5, 0xa009fd9fb9f79f39ee9ea9e09df9de9dc9d599d98e8dc8708607fd7c773e73d6db6b45ff5fe478, 0x82e14d, 0x90a79e, 0xa0e9a179b68b3cc1f2, 0xa4ea38a0c88c82562a, 0xa56a4ea0c88c8257c162a61d4ab4aa4a94a74a64a5, 0xa4fa32a2582d15014f, 0xa58a57a3ca3ba39a3882e69769669562861d61c, 0xa539c582d829698696, 0x93b93682e8278197cd7906986976954ff4fa, 0x9ce8bc86a421019, 0x8227ae, 0xa5da4ba28a2795681881779563d625, 0xa5ea0b9a89578c28888228157af7986e06266246224d94a14182c32c1, 0xa5ea289a782281b6262b614a]
  | 83 => #[0xa60a249a788882281d8158146234d44a34a24a01c1, 0xa61a60a5d9579568c2888818817, 0xa62a61a5fa5ea0b9579098227981bf, 0xa63a619a7418, 0xa63a61a5fa5ea28a279579558c28177e37e27e079661f61922b00e, 0xa65a64a61a5fa0b9a89a796095e9568c38188167e17e079963d63c63a61e6194a14a041a2d22d12c221d1c01bc, 0xa66a65a5fa4ba279a895e95581b63f63650941a148146145010, 0xa66a61a5fa5ea5d9578c288882281d7ae7984192f613900f, 0xa67a66a64a4ba279568c38227986246075094f04172b4, 0xa69a68a67a66a62a60a5da28a24a0b9a88c27e37956e062461e5054d14a22c32b82b5, 0xa67a66a64a62a47a41a32a28a1ea1ca1aa19a17a16a0fa0a9e39cc9cb9ca9c99c89b598d96596395c95a9599589378fb8f98ef88588388288084081c7fc7a66e96386335ea524522327326, 0xa0ea0d9ce85b79f79c79a78b6893011e7, 0xa6ca49a0d9fd9fc9fa9f89ce9b997890a85b8447d17306875681ea17b, 0xa6da49a0e9fd9fc9fa9f89b99787d179e30117b, 0xa6ea0e86c84d8427b079e6b01f71f61f21f11f017b, 0xa6ea6da0e9d39d09cf9ce85a844019017016015, 0xa70a6fa6ea55a54a299a090a86c420018015, 0xa70a6fa6ea0d9d396a85b85a78b7177006fd6fc41d1ed1e7015, 0xa72a70a55a54a0da099a285b78b6ff68f68d68c56a, 0xa73a72a71a6ea6ca0d9d196b96a90a87384c7176ff6fe6fc68f68d558556342340, 0xa73a72a70a6fa55a549a285b79b78b6ff68d56a, 0x8f28e18df88588488287f81e7f77f17ef7ed7eb7d47cb7ca7c276876576375074b6cc57d57b57a47647447347246e46c45e45144d43842e3b838438037f37636c36a26322c127, 0xa768f28e18df87e81e75074f74d45142e3b836c36826322c1fe1251230f8, 0xa768f28df74e4ac11111008e, 0xa77a769bb75074e42e11008e08d, 0xa79a78a77a2d9bb97a93a8df8a45a64ac48748639a10f08e, 0xa78a77a768f28e08df81e75068410e, 0xa7ba78a038e28b789d8867594c842f42e24324208d, 0xa7aa79a77a769bb9a98e28b78a589c68445011110e, 0xa039a988681e75074e45644b4490b4, 0xa7a87e75274c6ba45644b427, 0xa7ba7aa78a76a0389d89c88687e75975175045f43242e]
  | 84 => #[0xa80a7da7ba78a76a039a98e28b788687e81e75975174e4c845f45043224208d, 0xa81a80a7aa79a77a039bb8f288687e74f6cc44a0f50e10de, 0xa7fa7ba7aa78a039a989c88681e75975174f74e74d45f42f0b30b208c, 0xa82a81a7fa7ea6ba2da049b997a93a9378a47cc7666bb5a6487486113, 0xa82a80a7da77a6ba2ea049bb9b993789d7cc7666bb684, 0xa84a82a81a80a7fa79a75a6fa6da6aa69a66a65a63a60a49a48a44a42a41a3da31a2ca28a21a07a05a009ff9f99ea9e69e39cb9c19b89b59b49b19a699298f95d95b95394a94994894394193e93a9399369359339329288f98da8d78d28a388788588484181c81b80e80c8097f87f27cf7ca7c87c37ac79f77175472e6df6db6cb6c55eb5e952651d4e94e34af44f150144, 0xa84a83a75a6aa69a68a67a65a63a62a5ea5da4ba48a45a43a41a32a2ba26a24a21a0aa07a03a01a009fd9e79d19cc9c89b29b09ae9ad9a89a699699398f98e98c98696095895294a94594493a93893591e91d9118da8d78d28a08858848818127cb7ca7c96cb586539460411, 0xa82a81a7ea7da7ca78a6fa6da6ba49a48a46a2da2ba009fe97d97c97994093f93e93c93a93893793393192f9299268e28e18e086380b80778277776a7226cf6bf5a55594b43e73e33e03df3aa3a63a53a239e, 0x9c18876db6da, 0xa56a51a50a4aa39a38a269cd88b88a82b82a7ea7e97e87e57b479065262b6166126114fe4003fc, 0xa75a73a71a6ea5ca55a299a086c421420, 0xa8ba75a73a71a6ea55a549d29a090a87986c85b79e78b018016015, 0xa8ca74a73a70a6ca5c9d49d39d09ce9ba99b86c85c84d84679e79c79a78b71570e70d69068a68968541d3433421e5, 0xa8da8ba74a6fa6ea0d9d49d372741d, 0xa8ea8da8ca6ca5ca54a0ea0d9d49cf99b85c85b85973072f6b0687686359358, 0xa8fa6ea6da0ea0987386b86a85b84c78b7337327317186fe55a3523121f3, 0xa8fa719d496c96b87386b86a84c73373170f70c68a56e55a3cc3953521f3, 0xa8fa8da299d49a179b72756b, 0xa8fa8ea75a6fa5c9ba86c84d79e30117b019017, 0xa93a8ca72a6fa6da6c9d496a8a783c7b27b171771670c7006fc567341, 0xa94a92a8da8ca70a6ea6da6ca29a0d9d49d39d285c727, 0xa93a91a8c9d184484279f79c4211ef1ee019, 0xa96a94a93a8f9ce9ba8bc86a8458427b07337321eb, 0xa94a93a91a8ea8ca75a74a72a6ea6da0ea099ce8bc86b71868c1f5, 0xa98a96a8fa8da8ca75a6fa6ea6da499fd9fc9fa9f89d49b999b9788467d179f, 0xa99a98a97a94a93a90a8fa71a70a6da0986971870f68a42141f41e, 0xa9aa99a97a96a91a8ba75a73a6fa6ea5ca29a0e9d29ba87986984d79e70d68a56942142041f41e, 0xa9ba9aa99a97a948bc87486a8448437323621ef, 0xa9ca9aa97a95a92a91a8da8ba75a74a6fa6ea299d49d29d099b87986c86985c84672870e56b, 0xa9da9ca9aa96a94a92a8ea85a81a7ea77a75a48a43a2ea2ba04a01a009e79b99b69b49a694294194093a93893793193092d91180d80c80b80a8027fe7cc6c46bb5e45e35b51c6, 0xa9ea9da9ba99a98a96a94a90a8ea88a6ea6aa69a68a64a63a62a60a5fa5da28a24a0e9d19cf9ce99299098c98998695294b94a94894794591e91c8447f77f57f47f07ee7d47d37ae7987306366235f152e52d5284b14a24602a7146082, 0xa8aa5ba5aa59a53a51a5082e7b514f14d]
  | 85 => #[0xa9fa9da9ca9ba99a96a94a90a8ea88a85a84a7fa7ba77a6ba6aa68a67a64a5fa2ea2da2ba289d19ce9b69b39b29b09a899399298c98998696095695595395294894686a84581b8188167f87f77f57f47f37f17ef79979576775c63e52a5294b34a32a825525411d11c11b119050, 0xa2f9c09b75f649148f48c, 0xa318108057fd7f95fc5f9, 0xa35a319c48117d97d83fb3fa, 0xa029c39c27ff7f95fb, 0xaa5a029c09be813, 0x78d6936924f9, 0xaa0a57a4ca4aa38a0c9c59548e582d82c7e779062b611503502, 0xa9e9c58288235014ff4d2, 0xaa9aa7a9ea59a38a369c58e582d82b7b85035024fd4fb14e, 0xaa7a9ea56a3ca3ba329cd93b7ea7e8, 0xaa7aa0a9ea59a3ca3ba389cd8e57b87904a8, 0xa9ea3293b81a, 0xaadaaaa9fa9da9ca9ba9aa97a95a94a92a8fa8da8ba85a83a82a7fa7ba77a75a6ba6aa69a67a61a60a5fa5da4ba48a47a46a44a40a3ea37a2ea2da2ca2ba27a23a1fa1da0ba05a01a009fe9fc9f69ea9e69ca9b99b89b59a89a79a699298f98d98c98b98a98798595a95995794b94a94894794593a9369349209098dd8dc8da8d28d08c68c38c28ba89f89d89688e8417ef7ed7eb7e27d57cf7c778e7717696eb6e16cb6c669946932c2d3, 0xaa7a5b93b82778d500, 0xaafaaba5ba56a38a32a0c692, 0xab0aafaaea9e93682381a8197cd4f94d23ff, 0xab0aaeaabaaaaa8aa0a3ca3ba0c9cd95481a7e87e76546272ba, 0xab1ab0aafaaaaa7a9ea8aa5ba5aa51a37a32a2aa26a2588b82e82d59115014f14d, 0xab1ab0aacaabaa9aa0a58a4ca38a3693b8e588c82c8258197e678d69161b503, 0xab2ab0aafaaeaaaaa9aa8aa7aa0a9ea8aa57a53a50a4f9c582e82d82b8267ea7b57b478e, 0xab5ab2ab1aaeaaaaa8aa7a9ea8aa5aa57a3ca3ba39a3882e69661c4a94a514d, 0xab3aa9aa7aa0a5aa57a53a4da3769369265365161b, 0xab0aacaaaaa9a9ea4da3782614b, 0xab8ab2ab0aaeaaaaa9aa8a59a58a57a53a51a4da32a2aa26a259c588c82e82c82b7ea7e57b46526515035024f8, 0xab9ab0aa6a9fa89a31a029c29c16d95f8280, 0xab9ab6aa19c18058017fa77b4c049148d3f6, 0xaa69c48128017d95fb, 0xabcaa69c49c36db6d9, 0xabdabcabaab9ab0aa5aa2a9fa359b76da, 0xabeabdaa5a2fa029c08106d95fa5f75f65c1, 0xabfabaab9ab0aa3a9fa35a34a30a029c39c19c09be7dd7dc7da7be7b37885dc5db5d95d85c85c75c5]
  | 86 => #[0xabbab9ab6aa6aa1a348037dc7d67b35cc5ca, 0xabfabeabdaa5a31a029c05fa5c1, 0xac2abdabcabbab9ab6aa1a9fa898128055f93fb, 0xaa6aa4a35a339c08138047dc77a5cc5c75c6291, 0xac1abdabaab9ab0aa6a9fa029c39c09be9bd9b78037d87d65e25cc, 0xac5abbab9ab6aa18017be77b776775773491490, 0xac6ac5ac4ac3abfabeabcab9ab7ab4ab1ab0aaeaadaaaaa8aa3a8aa5aa58a56a52a50a4ea4da4aa3aa38a37a2a9cd82e8247e97e87e769369265361260f4fc2ba, 0xac2abeabcabbab9ab6aa3aa19c19c09bc8878127fd7755ff5fc2ab, 0xac7ac6ac4ac0ab8ab5aa6a34a30a2f9fd9fb9c49bf8dd7e47da7877795d9, 0xac9ac6ac3a349c39c28048037ff7dc7b377a7755c63f93f83f6, 0xac9ac7ac6ac2ac0abdabaab9ab8ab5ab0aa6aa5aa4a35a34a339fd9fb9c48dd7f97e47db7da, 0xac9ac7ac6ac5ac1abfabdab8ab5aa4aa3a35a34a33a2f9fd9fb9c49c09bf9bc8dd7fd7e477569d5fd2ab2aa, 0xaccacbacaac9ac3ac1abfabeabdaa5aa4a35a34a2fa029c39c09bd8108057d85fa5f95d75d6, 0xacdacbac6ac4ac2ac0abfabeabaab9ab0aa4aa3a9fa33a30a029c49be9bc7fa7887877766d969e5dc4c2, 0xacdacaac7ac6ac4ac3abfabcabbabaab8ab6ab5ab0aa6aa4aa3aa2aa1a9fa89a2fa029fd9fb9c49c19bf8dd8877fd7f97e46db5fd5fc, 0xacdaccacaabeaa69c39c19c09bc7fa7be77a776, 0xad0aca9c29c19c08138048037fa7dd7be7767757743f8, 0xad1acfaceacbac6ac2ac1abbab9ab6aa1a35a34a33a309c39c29b780077b77577477369e69c4c1, 0xad2ad1acfacbac6ac5ac4ac2aa2a2f9c49b78007f977b4bf, 0xad3ad1acfacdaa69c08058007734c049048f48d3f7]
  | _ => #[]

def upper (i : ℕ) : ℕ := ((upperPage (i/32))[i%32]?).getD 0

def pivot (j : ℕ) : ℕ := PackedGauss.pivotWord 12 2772 j (lower j)
end CriticalTensor.Base21NormalData

namespace CriticalTensor.Base21NormalData

open PackedGauss
open CriticalTensor.Base21Normal (column)

private structure Cursor (j : ℕ) : Type where
  ok : BeforeLU 12 column pivot upper j

private def first : Cursor 0 := ⟨beforeLU_zero _ _ _ _⟩

private def forward {j : ℕ} (p : Cursor j) (n : ℕ) (h : windowOK 12 column pivot upper j n=true) : Cursor (j+n) := ⟨extendLU p.ok h⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c48 : Cursor 48 := forward first 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c96 : Cursor 96 := forward c48 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c144 : Cursor 144 := forward c96 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c192 : Cursor 192 := forward c144 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c240 : Cursor 240 := forward c192 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c288 : Cursor 288 := forward c240 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c336 : Cursor 336 := forward c288 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c384 : Cursor 384 := forward c336 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c432 : Cursor 432 := forward c384 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c480 : Cursor 480 := forward c432 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c528 : Cursor 528 := forward c480 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c576 : Cursor 576 := forward c528 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c624 : Cursor 624 := forward c576 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c672 : Cursor 672 := forward c624 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c720 : Cursor 720 := forward c672 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c768 : Cursor 768 := forward c720 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c816 : Cursor 816 := forward c768 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c864 : Cursor 864 := forward c816 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c912 : Cursor 912 := forward c864 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c960 : Cursor 960 := forward c912 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1008 : Cursor 1008 := forward c960 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1056 : Cursor 1056 := forward c1008 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1104 : Cursor 1104 := forward c1056 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1152 : Cursor 1152 := forward c1104 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1200 : Cursor 1200 := forward c1152 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1248 : Cursor 1248 := forward c1200 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1296 : Cursor 1296 := forward c1248 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1344 : Cursor 1344 := forward c1296 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1392 : Cursor 1392 := forward c1344 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1440 : Cursor 1440 := forward c1392 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1488 : Cursor 1488 := forward c1440 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1536 : Cursor 1536 := forward c1488 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1584 : Cursor 1584 := forward c1536 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1632 : Cursor 1632 := forward c1584 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1680 : Cursor 1680 := forward c1632 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1728 : Cursor 1728 := forward c1680 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1776 : Cursor 1776 := forward c1728 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1824 : Cursor 1824 := forward c1776 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1872 : Cursor 1872 := forward c1824 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1920 : Cursor 1920 := forward c1872 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c1968 : Cursor 1968 := forward c1920 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2016 : Cursor 2016 := forward c1968 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2064 : Cursor 2064 := forward c2016 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2112 : Cursor 2112 := forward c2064 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2160 : Cursor 2160 := forward c2112 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2208 : Cursor 2208 := forward c2160 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2256 : Cursor 2256 := forward c2208 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2304 : Cursor 2304 := forward c2256 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2352 : Cursor 2352 := forward c2304 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2400 : Cursor 2400 := forward c2352 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2448 : Cursor 2448 := forward c2400 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2496 : Cursor 2496 := forward c2448 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2544 : Cursor 2544 := forward c2496 48 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2591 : Cursor 2591 := forward c2544 47 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2636 : Cursor 2636 := forward c2591 45 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2681 : Cursor 2681 := forward c2636 45 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2708 : Cursor 2708 := forward c2681 27 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2739 : Cursor 2739 := forward c2708 31 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2768 : Cursor 2768 := forward c2739 29 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 7000000 in
private def c2772 : Cursor 2772 := forward c2768 4 (by decide +kernel)

theorem checked : CriticalTensor.Spans 6 21 22 59 :=
  Base21Normal.spans_of_column_surjective (surjective_of_LU 2772 12 column pivot upper (fun i => c2772.ok i.val i.isLt))

end CriticalTensor.Base21NormalData

namespace CriticalTensor.Base21

theorem spans : CriticalTensor.Spans 6 21 22 59 := Base21NormalData.checked

end CriticalTensor.Base21

namespace CriticalTensor.SixConsecutive

/-- The tangent map spans at the catalogue count for every six-slice consecutive format. -/
theorem spans (m : ℕ) (hm : 6 ≤ m) :
    Spans 6 m (m + 1) (6 * m * (m + 1) ⌈/⌉ (6 + m + (m + 1) - 2)) :=
  spans_of_seed Base21.spans m hm

open Arxiv.«0805.3777» in
/-- On a dense open set, the complex CP rank is exactly the dimension count. -/
theorem generic_rank (m : ℕ) (hm : 6 ≤ m) :
    IsGenericRank [6,m,m + 1] (6 * m * (m + 1) ⌈/⌉ (6 + m + (m + 1) - 2)) :=
  generic_rank_of_seed Base21.spans m hm

open Arxiv.«0805.3777» in
theorem generic_rank_from_twenty (m : ℕ) (hm : 20 ≤ m) :
    IsGenericRank [6,m,m + 1] (3 * m - 4) := by
  simpa only [catalog_den,count_from_twenty m hm] using generic_rank m (by omega)

end CriticalTensor.SixConsecutive
