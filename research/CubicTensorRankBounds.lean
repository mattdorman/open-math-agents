import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-! # Bounds for the maximum CP rank of complex cubic tensors

Every complex tensor of odd side length n ≥ 3 has rank at most n(n+1)/2−1.
In particular the upper bounds at sides five and seven are 14 and 27.
At side four every tensor has rank at most nine, and multiplication in the
exterior algebra on two generators has rank eight. A suspension of any
rectangular tensor increases its rank by two. Iterating it from the exterior
algebra gives explicit tensors of all side lengths n ≥ 4 of rank exactly 2n.

The ambient notion of ordinary tensor rank is the original Holor.cprank.
The finite format results concern the maximum over all complex tensors.
The published four-cube interval is recorded by Atkinson and Lloyd (1980),
p. 21, with attribution to unpublished work of Lloyd. Equations (4.26) and
(4.28) of Bruzda, Friedland and Życzkowski give comparison upper bounds of
15 and 28. The proof uses the Sumi–Miyazaki–Sakata three-slice estimate and
the project's existing square-slice and three-slice formalizations. Their
source credits are retained at the corresponding declarations.

References:
* M. D. Atkinson and S. Lloyd, Bounds on the ranks of some 3-tensors,
  Linear Algebra and its Applications 31 (1980), 19–31.
  https://doi.org/10.1016/0024-3795(80)90202-5
* T. Sumi, M. Miyazaki and T. Sakata, About the maximal rank of 3-tensors
  over the real and the complex number field (2010).
  https://doi.org/10.1007/s10463-010-0294-5
* W. Bruzda, S. Friedland and K. Życzkowski, Rank of a tensor and quantum
  entanglement. https://arxiv.org/abs/1912.06854
-/

namespace MaxCube

/-- Coordinates of a sum of exactly r pure tensors, allowing zero summands. -/
def Decomp (a b c r : ℕ) (T : Fin a → Fin b → Fin c → ℂ) : Prop :=
  ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
    ∀ i j k, T i j k = ∑ t, x t i * (y t j * z t k)

/-- Left multiplication by 1, X, Y and XY in the exterior algebra on two generators.
The second slot gives the output coordinate and the third gives the right input. -/
def E : Fin 4 → Fin 4 → Fin 4 → ℂ :=
  ![(![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]]),
    (![![0,0,0,0], ![1,0,0,0], ![0,0,0,0], ![0,0,1,0]]),
    (![![0,0,0,0], ![0,0,0,0], ![1,0,0,0], ![0,-1,0,0]]),
    (![![0,0,0,0], ![0,0,0,0], ![0,0,0,0], ![1,0,0,0]])]

end MaxCube

namespace MaxCube

/-- A nonzero final slice lets one subtract multiples of that slice from
every preceding slice and delete one summand from a decomposition. -/
theorem drop_last_slice {a b c r : ℕ} {T : Fin (a+1) → Fin b → Fin c → ℂ}
    (h : Decomp (a+1) b c (r+1) T) (nonzero : ∃ j k, T (Fin.last a) j k ≠ 0) :
    ∃ v : Fin a → ℂ, Decomp a b c r
      (fun i j k => T i.castSucc j k + v i*T (Fin.last a) j k) := by
  classical
  obtain ⟨x,y,z,repr⟩ := h
  obtain ⟨j₀,k₀,hn⟩ := nonzero
  obtain ⟨t,ht⟩ : ∃ t : Fin (r+1), x t (Fin.last a)≠0 := by
    by_contra! hz
    apply hn
    simpa [hz] using repr (Fin.last a) j₀ k₀
  let v (i : Fin a) := -x t i.castSucc / x t (Fin.last a)
  have cancel (i : Fin a) : x t i.castSucc + v i*x t (Fin.last a) = 0 := by
    dsimp only [v]
    rw [div_mul_cancel₀ _ ht,add_neg_cancel]
  refine ⟨v, fun u i => x (t.succAbove u) i.castSucc + v i*x (t.succAbove u) (Fin.last a),
    fun u => y (t.succAbove u),fun u => z (t.succAbove u),?_⟩
  intro i j k
  let f (u : Fin (r+1)) := (x u i.castSucc+v i*x u (Fin.last a))*(y u j*z u k)
  calc
    T i.castSucc j k + v i*T (Fin.last a) j k = ∑ u, f u := by
      rw [repr i.castSucc,repr (Fin.last a),Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [f]
      ring
    _ = ∑ u : Fin r, f (t.succAbove u) := by
      rw [Fin.sum_univ_succAbove f t]
      simp only [f,cancel,zero_mul,zero_add]

/-- Eliminating the XY and Y slices of the exterior multiplication tensor
leaves a five-term pencil with the indicated free slice additions. -/
theorem reduce_exterior (h : Decomp 4 4 4 7 E) :
    ∃ a b c d : ℂ, Decomp 2 4 4 5
      ![(fun j k => E 0 j k + a*E 2 j k + b*E 3 j k),
        (fun j k => E 1 j k + c*E 2 j k + d*E 3 j k)] := by
  obtain ⟨v,hv⟩ := drop_last_slice (a:=3) (r:=6) h ⟨3,0,by change (1:ℂ)≠0; exact one_ne_zero⟩
  obtain ⟨w,hw⟩ := drop_last_slice (a:=2) (r:=5) hv
    ⟨2,0,by change (1:ℂ) + v 2*0≠0; simp⟩
  obtain ⟨x,y,z,repr⟩ := hw
  refine ⟨w 0,v 0+w 0*v 2,w 1,v 1+w 1*v 2,x,y,z,?_⟩
  intro i j k
  have combine (u : Fin 2) :
      E u.castSucc.castSucc j k + w u*E 2 j k + (v u.castSucc+w u*v 2)*E 3 j k =
        ∑ t, x t u*(y t j*z t k) := by
    calc
      _ = (E u.castSucc.castSucc j k + v u.castSucc*E 3 j k) +
        w u*(E 2 j k+v 2*E 3 j k) := by ring
      _ = _ := repr u j k
  fin_cases i
  · exact combine 0
  · exact combine 1

end MaxCube

namespace MaxCube

/-- Diagonal multiplication in a basis has no Jordan chain of length two at zero. -/
private lemma diagonal_map {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℂ V]
    (B : Module.Basis ι ℂ V) (f : ι → ℂ) :
    ∃ D : Module.End ℂ V, (∀ i, D (B i)=f i • B i) ∧ ∀ v, D (D v)=0 → D v=0 := by
  classical
  let E := B.equivFun
  let L : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun u i => f i*u i
      map_add' := fun u v => funext fun i => mul_add _ _ _
      map_smul' := fun a u => funext fun i => by
        change f i*(a*u i)=a*(f i*u i)
        ring }
  let D : Module.End ℂ V := E.symm.toLinearMap ∘ₗ L ∘ₗ E.toLinearMap
  have coord (v : V) (i : ι) : E (D v) i=f i*E v i := by
    change E (E.symm (L (E v))) i=_
    rw [E.apply_symm_apply]
    rfl
  have atBasis (i j : ι) : E (B i) j=(if i=j then 1 else 0) := B.repr_self_apply i j
  refine ⟨D,?_,?_⟩
  · intro i
    apply E.injective
    funext j
    rw [coord,map_smul]
    change f j*E (B i) j=f i*E (B i) j
    rw [atBasis]
    by_cases h : i=j <;> simp [h]
  · intro v h
    apply E.injective
    funext i
    have hi := congrFun (congrArg E h) i
    rw [coord,coord,map_zero] at hi
    rw [coord,map_zero]
    change f i*(f i*E v i)=0 at hi
    change f i*E v i=0
    rcases mul_eq_zero.mp hi with hz|hz
    · exact mul_eq_zero_of_left hz _
    · exact hz

/-- A five-term decomposition of the pencil selects four left vectors in the
identity slice as a basis. The remaining right functional cuts out a subspace
on which the second slice agrees with diagonal multiplication in that basis. -/
theorem diagonal_on_hyperplane (N : Matrix (Fin 4) (Fin 4) ℂ)
    (h : Decomp 2 4 4 5 ![(1 : Matrix (Fin 4) (Fin 4) ℂ),N]) :
    ∃ D : Module.End ℂ (Fin 4 → ℂ), ∃ l : Module.Dual ℂ (Fin 4 → ℂ),
      (∀ v, D (D v)=0 → D v=0) ∧ ∀ v, l v=0 → N.mulVec v=D v := by
  classical
  obtain ⟨x,y,z,hT⟩ := h
  let V := Fin 4 → ℂ
  let right (t : Fin 5) : Module.Dual ℂ V := dotProductBilin ℂ ℂ (z t)
  let w (t : Fin 5) : V := x t 0 • y t
  have expand (s : Fin 2) (v : V) :
      ((![1,N] : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ) s).mulVec v =
        ∑ t, (right t v) • (x t s • y t) := by
    funext j
    change (∑ k, ((![1,N] : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ) s j k)*v k)=_
    calc
      _ = ∑ k, (∑ t,x t s*(y t j*z t k))*v k :=
        Finset.sum_congr rfl fun k _ => congrArg (fun a : ℂ => a*v k) (hT s j k)
      _ = _ := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
        apply Finset.sum_congr rfl
        intro t _
        change (∑ k, x t s*(y t j*z t k)*v k)=(∑ k,z t k*v k)*(x t s*y t j)
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have ident (v : V) : v=∑ t, (right t v) • w t := by
    simpa only [Matrix.cons_val_zero,Matrix.one_mulVec,w] using expand 0 v
  have second (v : V) : N.mulVec v=∑ t, (right t v) • (x t 1 • y t) := by
    simpa only [Matrix.cons_val_one,Matrix.cons_val_zero] using expand 1 v
  have spans : ⊤ ≤ Submodule.span ℂ (Set.range w) := by
    intro v _
    rw [ident v]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
  obtain ⟨ι,pick,inj,same,li⟩ := exists_linearIndependent' ℂ w
  let : Finite ι := Finite.of_injective pick inj
  let : Fintype ι := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ V := Module.Basis.mk li (by rw [same]; exact spans)
  have basis_eq (i : ι) : B i=w (pick i) := Module.Basis.mk_apply ..
  have card : Fintype.card ι=4 := by
    rw [← Module.finrank_eq_card_basis B]
    simp [V]
  let chosen := Finset.univ.image pick
  have card_chosen : chosen.card=4 := by
    simpa only [chosen,Finset.card_image_of_injective _ inj,Finset.card_univ] using card
  have card_compl : chosenᶜ.card=1 := by rw [Finset.card_compl,card_chosen]; decide
  obtain ⟨extra,hextra⟩ := Finset.card_eq_one.mp card_compl
  have hit (t : Fin 5) (hne : t≠extra) : ∃ i, pick i=t := by
    have ht : t∈chosen := by
      by_contra hh
      have : t∈chosenᶜ := Finset.mem_compl.mpr hh
      rw [hextra] at this
      exact hne (Finset.mem_singleton.mp this)
    simpa [chosen] using ht
  let slope (i : ι) := x (pick i) 1 / x (pick i) 0
  obtain ⟨D,eigen,hker⟩ := diagonal_map B slope
  have acts (t : Fin 5) (hne : t≠extra) : D (w t)=x t 1 • y t := by
    obtain ⟨i,rfl⟩ := hit t hne
    have hnonzero : x (pick i) 0≠0 := by
      intro hz
      apply li.ne_zero i
      change x (pick i) 0 • y (pick i)=0
      rw [hz,zero_smul]
    rw [← basis_eq i,eigen,basis_eq]
    simp [slope,w,smul_smul,hnonzero]
  refine ⟨D,right extra,hker,?_⟩
  intro v hv
  calc
    N.mulVec v = ∑ t, (right t v) • (x t 1 • y t) := second v
    _ = ∑ t, (right t v) • D (w t) := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases he : t=extra
      · subst t
        simp only [hv,zero_smul]
      · rw [acts t he]
    _ = D (∑ t, (right t v) • w t) := by simp only [map_sum,map_smul]
    _ = D v := congrArg D (ident v).symm

end MaxCube

namespace MaxCube

/-- A square-zero operator with two independent images cannot agree on a
hyperplane with an operator whose kernel equals the kernel of its square. -/
lemma no_diagonal_hyperplane {E : Type*} [AddCommGroup E] [Module ℂ E]
    (N D : E →ₗ[ℂ] E) (l : E →ₗ[ℂ] ℂ) (u v : E)
    (nilpotent : ∀ x, N (N x)=0)
    (independent : ∀ a b : ℂ, a • N u + b • N v=0 → a=0 ∧ b=0)
    (semisimple : ∀ x, D (D x)=0 → D x=0)
    (agree : ∀ x, l x=0 → N x=D x) : False := by
  classical
  have in_kernel (f : E →ₗ[ℂ] ℂ) : ∃ x, f x=0 ∧ N x≠0 := by
    by_cases h : f u=0
    · refine ⟨u,h,?_⟩
      intro hu
      exact one_ne_zero (independent 1 0 (by simp [hu])).1
    · let x := (f v) • u + (-f u) • v
      refine ⟨x,?_,?_⟩
      · simp only [x,map_add,map_smul,smul_eq_mul]
        ring
      · intro hx
        have comb : (f v) • N u + (-f u) • N v=0 := by simpa only [x,map_add,map_smul] using hx
        exact h (neg_eq_zero.mp (independent _ _ comb).2)
  have impossible (y : E) (hy : l y=0) (hy' : l (N y)=0) (hNy : N y≠0) : False := by
    have hD : D (D y)=0 := by rw [← agree y hy,← agree (N y) hy',nilpotent]
    exact hNy ((agree y hy).trans (semisimple y hD))
  by_cases annih : ∀ z, l (N z)=0
  · obtain ⟨x,hx,hNx⟩ := in_kernel l
    exact impossible x hx (annih x) hNx
  · obtain ⟨z,hz⟩ := not_forall.mp annih
    obtain ⟨x,hx,hNx⟩ := in_kernel (l.comp N)
    change l (N x)=0 at hx
    let y := x - (l x / l (N z)) • N z
    have hy : l y=0 := by simp [y,smul_eq_mul,div_mul_cancel₀ _ hz]
    have hNy : N y=N x := by simp [y,nilpotent]
    exact impossible y hy (hNy ▸ hx) (hNy ▸ hNx)

end MaxCube

namespace MaxCube

/-- The first seven products give the scalar term and the individual scalar–radical
cross terms. The final product combines the mixed terms of the alternating coordinate. -/
theorem exterior_upper : Decomp 4 4 4 8 E := by
  let x : Fin 8 → Fin 4 → ℤ :=
    ![![1,0,0,0], ![1,1,0,0], ![0,1,0,0], ![1,0,1,0],
      ![0,0,1,0], ![1,0,0,1], ![0,0,0,1], ![0,1,1,0]]
  let y : Fin 8 → Fin 4 → ℤ :=
    ![![1,-1,-1,-1], ![0,1,0,0], ![0,-1,0,1], ![0,0,1,0],
      ![0,0,-1,-1], ![0,0,0,1], ![0,0,0,-1], ![0,0,0,1]]
  let z : Fin 8 → Fin 4 → ℤ :=
    ![![1,0,0,0], ![1,1,0,0], ![0,1,0,0], ![1,0,1,0],
      ![0,0,1,0], ![1,0,0,1], ![0,0,0,1], ![0,-1,1,0]]
  let d : Fin 4 → Fin 4 → Fin 4 → ℤ :=
    ![(![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]]),
      (![![0,0,0,0], ![1,0,0,0], ![0,0,0,0], ![0,0,1,0]]),
      (![![0,0,0,0], ![0,0,0,0], ![1,0,0,0], ![0,-1,0,0]]),
      (![![0,0,0,0], ![0,0,0,0], ![0,0,0,0], ![1,0,0,0]])]
  have table : ∀ i j k, d i j k = ∑ t,x t i*(y t j*z t k) := by decide +kernel
  have cast_table (i j k : Fin 4) : E i j k = (d i j k : ℂ) := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> first
      | exact (show (0 : ℂ)=((0 : ℤ) : ℂ) by norm_num)
      | exact (show (1 : ℂ)=((1 : ℤ) : ℂ) by norm_num)
      | exact (show (-1 : ℂ)=((-1 : ℤ) : ℂ) by norm_num)
  refine ⟨fun t i => (x t i : ℂ),fun t j => (y t j : ℂ),fun t k => (z t k : ℂ),?_⟩
  intro i j k
  rw [cast_table,table]
  simp only [Int.cast_sum,Int.cast_mul]

end MaxCube

namespace MaxCube.HolorProof

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

lemma eval_holor_sum {ds : List ℕ} {r : ℕ} (u : Fin r → Holor ℂ ds) (j : HolorIndex ds) :
    (∑ i, u i) j = ∑ i, u i j :=
  Finset.sum_apply (M := fun _ : HolorIndex ds => ℂ) j Finset.univ (fun i x => u i x)

end MaxCube.HolorProof

namespace MaxCube

open Arxiv.«0805.3777»

private def splitIndex {n : ℕ} {ds : List ℕ} : HolorIndex (n :: ds) → Fin n × HolorIndex ds
  | ⟨i :: is,h⟩ => (⟨i,(List.forall₂_cons.mp h).1⟩,⟨is,(List.forall₂_cons.mp h).2⟩)
  | ⟨[],h⟩ => nomatch h

/-- Convert three ordinary finite indices into the dimension-list coordinates of a holor. -/
def coordinateHolor {a b c : ℕ} (T : Fin a → Fin b → Fin c → ℂ) : Holor ℂ [a,b,c] :=
  fun q => T (splitIndex q).1 (splitIndex (splitIndex q).2).1 (splitIndex (splitIndex (splitIndex q).2).2).1

private lemma all_indices {a b c : ℕ} (q : HolorIndex [a,b,c]) :
    ∃ (i : Fin a) (j : Fin b) (k : Fin c),
      q=⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩ := by
  obtain ⟨is,h⟩ := q
  cases h with | cons hi h =>
    cases h with | cons hj h =>
      cases h with | cons hk h =>
        cases h
        exact ⟨⟨_,hi⟩,⟨_,hj⟩,⟨_,hk⟩,rfl⟩

theorem coordinateHolor_apply {a b c : ℕ} (T : Fin a → Fin b → Fin c → ℂ)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    coordinateHolor T ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩ = T i j k := rfl

/-- CP rank at most r is exactly a coordinate decomposition with r possibly zero summands. -/
theorem cprank_le_iff_decomp {a b c : ℕ} (T : Fin a → Fin b → Fin c → ℂ) (r : ℕ) :
    (coordinateHolor T).cprank ≤ r ↔ Decomp a b c r T := by
  classical
  constructor
  · intro hr
    obtain ⟨U,simple,sum⟩ := HolorProof.finite_sum_of_simple
      (HolorProof.decomposition_of_rank_bound (coordinateHolor T) r hr)
    choose x y z eq using fun t => HolorProof.simple_coordinates (simple t)
    refine ⟨x,y,z,?_⟩
    intro i j k
    let q : HolorIndex [a,b,c] := ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩
    calc
      T i j k = coordinateHolor T q := rfl
      _ = (∑ t, U t) q := congrFun sum.symm q
      _ = ∑ t, U t q := HolorProof.eval_holor_sum U q
      _ = ∑ t, x t i*(y t j*z t k) := by
        apply Finset.sum_congr rfl
        intro t _
        simpa only [mul_assoc] using eq t i j k
  · rintro ⟨x,y,z,hit⟩
    let X (t : Fin r) (q : HolorIndex [a]) := x t (splitIndex q).1
    let Y (t : Fin r) (q : HolorIndex [b]) := y t (splitIndex q).1
    let Z (t : Fin r) (q : HolorIndex [c]) := z t (splitIndex q).1
    have tensor_eq : coordinateHolor T = ∑ t, Holor.mul (X t) (Holor.mul (Y t) (Z t)) := by
      funext q
      obtain ⟨i,j,k,rfl⟩ := all_indices q
      exact (hit i j k).trans (HolorProof.eval_holor_sum (ds:=[a,b,c])
        (fun t => Holor.mul (X t) (Holor.mul (Y t) (Z t)))
        ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩).symm
    rw [tensor_eq]
    exact Nat.find_min' _ (HolorProof.tensor_sum_rank X Y Z)

/-- The actual 4×4×4 multiplication tensor of the two-generator exterior algebra. -/
def exteriorHolor : Holor ℂ [4,4,4] := coordinateHolor E

theorem exterior_cprank_le_iff (r : ℕ) :
    exteriorHolor.cprank ≤ r ↔ Decomp 4 4 4 r E := cprank_le_iff_decomp E r

theorem exterior_rank_lower (lower : ¬Decomp 4 4 4 7 E) : 8≤exteriorHolor.cprank := by
  have hl : ¬exteriorHolor.cprank≤7 := fun h => lower ((exterior_cprank_le_iff 7).mp h)
  omega

theorem exterior_rank_eight (lower : ¬Decomp 4 4 4 7 E) (upper : Decomp 4 4 4 8 E) :
    exteriorHolor.cprank = 8 :=
  le_antisymm ((exterior_cprank_le_iff 8).mpr upper) (exterior_rank_lower lower)

theorem exterior_max_lower {R : ℕ} (maximum : IsMaxRank [4,4,4] R) (lower : ¬Decomp 4 4 4 7 E) :
    8≤R := (exterior_rank_lower lower).trans (maximum.2 ⟨exteriorHolor,rfl⟩)

/-- Every fixed list of dimensions admits a greatest CP rank, attained by an actual tensor. -/
theorem exists_max_rank (ds : List ℕ) : ∃ R : ℕ, IsMaxRank ds R := by
  classical
  let ranks := (Finset.Iic ds.prod).filter (fun k => ∃ T : Holor ℂ ds, T.cprank=k)
  have mem (T : Holor ℂ ds) : T.cprank ∈ ranks :=
    Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (Holor.cprank_upper_bound T),⟨T,rfl⟩⟩
  have hne : ranks.Nonempty := ⟨_,mem 0⟩
  refine ⟨ranks.max' hne,(Finset.mem_filter.mp (ranks.max'_mem hne)).2,?_⟩
  rintro _ ⟨T,rfl⟩
  exact Finset.le_max' ranks _ (mem T)

end MaxCube

namespace MaxCube

private def rightChange (p q : ℂ) : Module.End ℂ (Fin 4 → ℂ) where
  toFun v := ![v 0 - p*v 2 - q*v 3, v 1 + p*v 3, v 2, v 3]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' x y := by ext i; fin_cases i <;> simp <;> ring

private theorem change_columns {a b c d r : ℕ}
    (L : (Fin c → ℂ) →ₗ[ℂ] (Fin d → ℂ)) {T : Fin a → Fin b → Fin c → ℂ}
    (h : Decomp a b c r T) : Decomp a b d r (fun i j => L (T i j)) := by
  obtain ⟨x,y,z,h⟩ := h
  refine ⟨x,y,fun t => L (z t),?_⟩
  intro i j k
  have eqn : T i j = ∑ t, (x t i * y t j) • z t := by
    ext l
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using h i j l
  change (L (T i j)) k = ∑ t, x t i * (y t j * (L (z t)) k)
  rw [eqn, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

private def normal (s v : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun j k => E 1 j k + s*E 2 j k + v*E 3 j k

private lemma normalize_pair {p q r s : ℂ}
    (h : Decomp 2 4 4 5 ![(fun j k => E 0 j k + p*E 2 j k + q*E 3 j k),
                           (fun j k => E 1 j k + r*E 2 j k + s*E 3 j k)]) :
    Decomp 2 4 4 5 ![(1 : Matrix (Fin 4) (Fin 4) ℂ),normal r (s-p)] := by
  have h' := change_columns (rightChange p q) h
  have ident :
      (fun i j => rightChange p q
          ((![(fun j k => E 0 j k + p*E 2 j k + q*E 3 j k),
              (fun j k => E 1 j k + r*E 2 j k + s*E 3 j k)]) i j)) =
        (![(1 : Matrix (Fin 4) (Fin 4) ℂ),normal r (s-p)]) := by
    funext i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [rightChange, normal, E]
  rw [ident] at h'
  exact h'

private lemma normal_apply (s w : ℂ) (x : Fin 4 → ℂ) :
    (normal s w).mulVec x = ![0, x 0, s*x 0, w*x 0 + x 2 - s*x 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, normal, E]
  ring

theorem exterior_lower : ¬ Decomp 4 4 4 7 E := by
  intro h
  obtain ⟨p,q,r,s,hp⟩ := reduce_exterior h
  obtain ⟨D,l,hd,hl⟩ := diagonal_on_hyperplane (normal r (s-p)) (normalize_pair hp)
  let N := (normal r (s-p)).mulVecLin
  let u : Fin 4 → ℂ := ![1,0,0,0]
  let v : Fin 4 → ℂ := ![0,0,1,0]
  apply no_diagonal_hyperplane N D l u v _ _ hd hl
  · intro x
    change (normal r (s-p)).mulVec ((normal r (s-p)).mulVec x) = 0
    rw [normal_apply,normal_apply]
    ext i
    fin_cases i <;> simp
  · intro α β hab
    change α • (normal r (s-p)).mulVec u + β • (normal r (s-p)).mulVec v = 0 at hab
    rw [normal_apply,normal_apply] at hab
    have a := congrFun hab 1
    have b := congrFun hab 3
    simp [u,v] at a b
    exact ⟨a,by simpa [a] using b⟩

end MaxCube

namespace MaxCube

theorem exterior_exact : exteriorHolor.cprank = 8 :=
  exterior_rank_eight exterior_lower exterior_upper

theorem max_four_cube_lower {R : ℕ} (maximum : Arxiv.«0805.3777».IsMaxRank [4,4,4] R) :
    8 ≤ R := exterior_max_lower maximum exterior_lower

end MaxCube

namespace MaxCube

/-- Preserve the original tensor on the old coordinates and add two unit
entries in the new middle coordinate. -/
def suspend {a b c : ℕ} (i₀ : Fin a) (k₀ : Fin c) (T : Fin a → Fin b → Fin c → ℂ)
    (i : Fin (a+1)) (j : Fin (b+1)) (k : Fin (c+1)) : ℂ :=
  Fin.lastCases
    (Fin.lastCases (Fin.lastCases 0 (fun q => if q=k₀ then 1 else 0) k)
      (fun p => Fin.lastCases (if p=i₀ then 1 else 0) (fun _ => 0) k) i)
    (fun q => Fin.lastCases 0 (fun p => Fin.lastCases 0 (T p q) k) i) j

@[simp] lemma suspend_old {a b c : ℕ} (i₀ : Fin a) (k₀ : Fin c) (T : Fin a → Fin b → Fin c → ℂ)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    suspend i₀ k₀ T i.castSucc j.castSucc k.castSucc = T i j k := by simp [suspend]

@[simp] lemma suspend_last_old {a b c : ℕ} (i₀ : Fin a) (k₀ : Fin c) (T : Fin a → Fin b → Fin c → ℂ)
    (j : Fin b) (k : Fin (c+1)) :
    suspend i₀ k₀ T (Fin.last a) j.castSucc k = 0 := by simp [suspend]

@[simp] lemma suspend_old_old_last {a b c : ℕ} (i₀ : Fin a) (k₀ : Fin c)
    (T : Fin a → Fin b → Fin c → ℂ) (i : Fin a) (j : Fin b) :
    suspend i₀ k₀ T i.castSucc j.castSucc (Fin.last c) = 0 := by simp [suspend]

@[simp] lemma suspend_old_last_old {a b c : ℕ} (i₀ : Fin a) (k₀ : Fin c)
    (T : Fin a → Fin b → Fin c → ℂ) (i : Fin a) (k : Fin c) :
    suspend i₀ k₀ T i.castSucc (Fin.last b) k.castSucc = 0 := by simp [suspend]

@[simp] lemma suspend_old_last_last {a b c : ℕ} (i₀ : Fin a) (k₀ : Fin c)
    (T : Fin a → Fin b → Fin c → ℂ) (i : Fin a) :
    suspend i₀ k₀ T i.castSucc (Fin.last b) (Fin.last c) = if i=i₀ then 1 else 0 := by simp [suspend]

@[simp] lemma suspend_last_last_old {a b c : ℕ} (i₀ : Fin a) (k₀ : Fin c)
    (T : Fin a → Fin b → Fin c → ℂ) (k : Fin c) :
    suspend i₀ k₀ T (Fin.last a) (Fin.last b) k.castSucc = if k=k₀ then 1 else 0 := by simp [suspend]

@[simp] lemma suspend_last_last_last {a b c : ℕ} (i₀ : Fin a) (k₀ : Fin c)
    (T : Fin a → Fin b → Fin c → ℂ) :
    suspend i₀ k₀ T (Fin.last a) (Fin.last b) (Fin.last c) = 0 := by simp [suspend]

end MaxCube

namespace MaxCube

/-- Extend the given pure tensors by zero and append the two new coordinate tensors. -/
lemma suspend_upper {a b c r : ℕ} (i₀ : Fin a) (k₀ : Fin c) {T : Fin a → Fin b → Fin c → ℂ}
    (hT : Decomp a b c r T) : Decomp (a+1) (b+1) (c+1) (r+2) (suspend i₀ k₀ T) := by
  classical
  obtain ⟨x,y,z,h⟩ := hT
  let pad {n : ℕ} (f : Fin n → ℂ) : Fin (n+1) → ℂ := Fin.lastCases 0 f
  let new {n : ℕ} : Fin (n+1) → ℂ := Fin.lastCases 1 (fun _ => 0)
  let unit {n : ℕ} (p : Fin n) : Fin (n+1) → ℂ := pad (fun j => if j=p then 1 else 0)
  let join {D : Type} (f : Fin r → D) (v w : D) : Fin (r+2) → D := Fin.lastCases w (Fin.lastCases v f)
  refine ⟨join (fun t => pad (x t)) new (unit i₀),join (fun t => pad (y t)) new new,
    join (fun t => pad (z t)) (unit k₀) new,?_⟩
  intro i j k
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> cases k using Fin.lastCases <;>
    simp [join,new,unit,pad,h]

end MaxCube

namespace MaxCube

private lemma flip_ends {a b c r : ℕ} {T : Fin a → Fin b → Fin c → ℂ}
    (h : Decomp a b c r T) : Decomp c b a r (fun k j i => T i j k) := by
  obtain ⟨x,y,z,repr⟩ := h
  refine ⟨z,y,x,?_⟩
  intro k j i
  change T i j k = _
  rw [repr i j k]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- The new first slice and the new third slice can each eliminate a
summand. Their additions are confined to the discarded middle coordinate. -/
theorem suspend_lower {a b c r : ℕ} (i₀ : Fin a) (k₀ : Fin c) (T : Fin a → Fin b → Fin c → ℂ)
    (h : Decomp (a+1) (b+1) (c+1) (r+2) (suspend i₀ k₀ T)) : Decomp a b c r T := by
  obtain ⟨v,hv⟩ := drop_last_slice (r:=r+1) h ⟨Fin.last b,k₀.castSucc,by simp⟩
  let U (i : Fin a) (j : Fin (b+1)) (k : Fin (c+1)) :=
    suspend i₀ k₀ T i.castSucc j k + v i*suspend i₀ k₀ T (Fin.last a) j k
  change Decomp a (b+1) (c+1) (r+1) U at hv
  obtain ⟨w,hw⟩ := drop_last_slice (r:=r) (flip_ends hv) ⟨Fin.last b,i₀,by simp [U]⟩
  obtain ⟨x,y,z,repr⟩ := hw
  refine ⟨z,fun t j => y t j.castSucc,x,?_⟩
  intro i j k
  have old := repr k j.castSucc i
  change U i j.castSucc k.castSucc + w k*U i j.castSucc (Fin.last c) = _ at old
  simp only [U,suspend_old,suspend_last_old,suspend_old_old_last,mul_zero,add_zero] at old
  rw [old]
  exact Finset.sum_congr rfl fun t _ => by ring

private lemma decomp_pos {a b c r : ℕ} {T : Fin a → Fin b → Fin c → ℂ}
    (h : Decomp a b c r T) {i j k} (nonzero : T i j k≠0) : 0<r := by
  by_contra! small
  have eq : r=0 := by omega
  subst r
  obtain ⟨_,_,_,repr⟩ := h
  exact nonzero (by simpa using repr i j k)

/-- The two added coordinates require at least two summands even when the
original tensor has rank zero. -/
theorem suspend_two_le {a b c s : ℕ} (i₀ : Fin a) (k₀ : Fin c) (T : Fin a → Fin b → Fin c → ℂ)
    (h : Decomp (a+1) (b+1) (c+1) s (suspend i₀ k₀ T)) : 2 ≤ s := by
  have pos := decomp_pos h (i:=Fin.last a) (j:=Fin.last b) (k:=k₀.castSucc) (by simp)
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  obtain ⟨v,hv⟩ := drop_last_slice h ⟨Fin.last b,k₀.castSucc,by simp⟩
  have p := decomp_pos hv (i:=i₀) (j:=Fin.last b) (k:=Fin.last c) (by simp)
  omega

theorem suspend_extract {a b c s : ℕ} (i₀ : Fin a) (k₀ : Fin c) (T : Fin a → Fin b → Fin c → ℂ)
    (h : Decomp (a+1) (b+1) (c+1) s (suspend i₀ k₀ T)) :
    ∃ r : ℕ, s=r+2 ∧ Decomp a b c r T := by
  have hs := suspend_two_le i₀ k₀ T h
  have eq : s=(s-2)+2 := by omega
  exact ⟨s-2,eq,suspend_lower i₀ k₀ T (eq ▸ h)⟩

end MaxCube

namespace MaxCube

open Arxiv.«0805.3777»

/-- Read an arbitrary rectangular holor on the three canonical finite indices. -/
def readCoordinates {a b c : ℕ} (T : Holor ℂ [a,b,c]) (i : Fin a) (j : Fin b) (k : Fin c) : ℂ :=
  T ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩

theorem coordinateHolor_readCoordinates {a b c : ℕ} (T : Holor ℂ [a,b,c]) :
    coordinateHolor (readCoordinates T) = T := by
  funext ⟨is,hi⟩
  cases hi with | cons hi hj =>
    cases hj with | cons hj hk =>
      cases hk with | cons hk h =>
        cases h
        rfl

/-- Adding the two new unit entries raises CP rank by exactly two. -/
theorem suspend_cprank {a b c : ℕ} (i₀ : Fin a) (k₀ : Fin c) (T : Fin a → Fin b → Fin c → ℂ) :
    (coordinateHolor (suspend i₀ k₀ T)).cprank = (coordinateHolor T).cprank+2 := by
  let S := suspend i₀ k₀ T
  have high : (coordinateHolor S).cprank ≤ (coordinateHolor T).cprank+2 :=
    (cprank_le_iff_decomp S _).mpr (suspend_upper i₀ k₀ ((cprank_le_iff_decomp T _).mp le_rfl))
  have decomp : Decomp (a+1) (b+1) (c+1) (coordinateHolor S).cprank S :=
    (cprank_le_iff_decomp S _).mp le_rfl
  obtain ⟨r,hr,small⟩ := suspend_extract i₀ k₀ T decomp
  have low := (cprank_le_iff_decomp T r).mpr small
  change (coordinateHolor S).cprank=(coordinateHolor T).cprank+2
  omega

/-- The same operation on catalogue holors takes one additional coordinate in every factor. -/
def suspendHolor {a b c : ℕ} (i₀ : Fin a) (k₀ : Fin c) (T : Holor ℂ [a,b,c]) :
    Holor ℂ [a+1,b+1,c+1] := coordinateHolor (suspend i₀ k₀ (readCoordinates T))

theorem suspendHolor_cprank {a b c : ℕ} (i₀ : Fin a) (k₀ : Fin c) (T : Holor ℂ [a,b,c]) :
    (suspendHolor i₀ k₀ T).cprank=T.cprank+2 := by
  rw [suspendHolor,suspend_cprank,coordinateHolor_readCoordinates]

/-- The dimension-four seed is exterior multiplication. At each subsequent
step both anchor indices are the first coordinate. -/
def exteriorFamily : (k : ℕ) → Fin (k+4) → Fin (k+4) → Fin (k+4) → ℂ
  | 0 => E
  | k+1 => suspend (0 : Fin (k+4)) (0 : Fin (k+4)) (exteriorFamily k)

theorem exteriorFamily_cprank (k : ℕ) : (coordinateHolor (exteriorFamily k)).cprank = 2*(k+4) := by
  induction k with
  | zero => exact exterior_exact
  | succ k ih =>
    change (coordinateHolor (suspend (0 : Fin (k+4)) (0 : Fin (k+4)) (exteriorFamily k))).cprank = _
    rw [suspend_cprank,ih]
    omega

/-- An explicit holor of order n for every n at least four. -/
def exteriorFamilyHolor (n : ℕ) (hn : 4≤n) : Holor ℂ [n,n,n] :=
  cast (congrArg (fun d => Holor ℂ [d,d,d]) (Nat.sub_add_cancel hn))
    (coordinateHolor (exteriorFamily (n-4)))

private lemma cprank_cast {m n : ℕ} (h : m=n) (T : Holor ℂ [m,m,m]) :
    (cast (congrArg (fun d => Holor ℂ [d,d,d]) h) T).cprank = T.cprank := by
  subst n
  rfl

theorem exteriorFamilyHolor_cprank (n : ℕ) (hn : 4≤n) :
    (exteriorFamilyHolor n hn).cprank=2*n := by
  exact (cprank_cast (Nat.sub_add_cancel hn) _).trans
    ((exteriorFamily_cprank (n-4)).trans (congrArg (fun k => 2*k) (Nat.sub_add_cancel hn)))

theorem cube_has_rank_twice_side (n : ℕ) (hn : 4≤n) :
    ∃ T : Holor ℂ [n,n,n], T.cprank=2*n := ⟨exteriorFamilyHolor n hn,exteriorFamilyHolor_cprank n hn⟩

/-- Suspending a greatest-rank tensor gains two ranks in the next cubic format. -/
theorem max_cube_step {n R S : ℕ} (hn : 0<n) (old : IsMaxRank [n,n,n] R)
    (next : IsMaxRank [n+1,n+1,n+1] S) : R+2≤S := by
  obtain ⟨T,hT⟩ := old.1
  change T.cprank=R at hT
  let anchor : Fin n := ⟨0,hn⟩
  have bound : (suspendHolor anchor anchor T).cprank ≤ S := next.2 ⟨_,rfl⟩
  rwa [suspendHolor_cprank,hT] at bound

/-- The lower bound on maximum rank accumulates over any number of cubic steps. -/
theorem max_cube_steps (n k : ℕ) {R S : ℕ} (hn : 0<n) (old : IsMaxRank [n,n,n] R)
    (next : IsMaxRank [n+k,n+k,n+k] S) : R+2*k ≤ S := by
  induction k generalizing S with
  | zero => simpa only [Nat.add_zero,Nat.mul_zero] using next.2 old.1
  | succ k ih =>
    obtain ⟨M,hM⟩ := exists_max_rank [n+k,n+k,n+k]
    have lower := ih hM
    have more := max_cube_step (show 0<n+k by omega) hM next
    omega

theorem max_cube_lower_twice_side {n R : ℕ} (hn : 4≤n) (maximum : IsMaxRank [n,n,n] R) : 2*n≤R := by
  have bound : (exteriorFamilyHolor n hn).cprank≤R := maximum.2 ⟨_,rfl⟩
  rwa [exteriorFamilyHolor_cprank] at bound

end MaxCube

namespace MaxCube.UpperNine

open Polynomial Module

/-- A separable characteristic polynomial supplies four independent eigenvectors. -/
private lemma spectral_basis (C : Matrix (Fin 4) (Fin 4) ℂ) (hs : C.charpoly.Separable) :
    ∃ b : Basis (Fin 4) ℂ (Fin 4 → ℂ), ∃ μ : Fin 4 → ℂ,
      ∀ t, C.mulVec (b t)=μ t • b t := by
  classical
  let S := C.charpoly.roots.toFinset
  have card : S.card = 4 := by
    rw [show S=C.charpoly.roots.toFinset from rfl,Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs),
      IsAlgClosed.card_roots_eq_natDegree,Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin]
  let e : Fin 4 ≃ S := Fintype.equivOfCardEq (by simpa using card.symm)
  let μ (t : Fin 4) : ℂ := (e t).val
  have hμ (t : Fin 4) : Module.End.HasEigenvalue C.mulVecLin (μ t) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,Matrix.charpoly_mulVecLin]
    apply (Polynomial.mem_roots C.charpoly_monic.ne_zero).mp
    exact Multiset.mem_toFinset.mp (e t).property
  choose v hv using fun i => (hμ i).exists_hasEigenvector
  have inj : Function.Injective μ := Subtype.val_injective.comp e.injective
  have li := Module.End.eigenvectors_linearIndependent' C.mulVecLin μ inj v hv
  let b := basisOfLinearIndependentOfCardEqFinrank li (by simp)
  refine ⟨b,μ,?_⟩
  intro t
  have hb : b t=v t := by exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank li _) t
  rw [hb]
  exact Module.End.mem_eigenspace_iff.mp (hv t).1

/-- An invertible first matrix and a simple spectrum of the associated pencil
give a decomposition with four terms and common left and right vectors. -/
theorem pencil_four_of_separable (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hA : A.det≠0) (hs : (A.adjugate*B).charpoly.Separable) :
    Decomp 2 4 4 4 ![A,B] := by
  classical
  let C := A.adjugate*B
  obtain ⟨b,μ,heig⟩ := spectral_basis C hs
  let W (t : Fin 4) := A.mulVec (b t)
  let z (t j : Fin 4) := b.repr (Pi.single j 1) t
  have ac : A*C=A.det • B := by
    rw [show C=A.adjugate*B from rfl,← Matrix.mul_assoc,Matrix.mul_adjugate,Matrix.smul_mul,Matrix.one_mul]
  have Bact (t : Fin 4) : B.mulVec (b t) = (A.det⁻¹*μ t) • W t := by
    have h : A.det • B.mulVec (b t) = μ t • W t := calc
      _ = (A*C).mulVec (b t) := by rw [ac,Matrix.smul_mulVec]
      _ = A.mulVec (C.mulVec (b t)) := (Matrix.mulVec_mulVec ..).symm
      _ = _ := by rw [heig,Matrix.mulVec_smul]
    have h' := congrArg (fun v : Fin 4 → ℂ => A.det⁻¹ • v) h
    simpa only [smul_smul,inv_mul_cancel₀ hA,one_smul] using h'
  have columns (M : Matrix (Fin 4) (Fin 4) ℂ) (j : Fin 4) :
      (∑ t,z t j • M.mulVec (b t)) = M.col j := by
    have hh := congrArg M.mulVecLin (b.sum_repr (Pi.single j 1))
    simpa only [map_sum,map_smul,Matrix.mulVecLin_apply,Matrix.mulVec_single_one,z] using hh
  refine ⟨fun t => ![1,A.det⁻¹*μ t],W,z,?_⟩
  intro s i j
  have cases : s=0 ∨ s=1 := by omega
  rcases cases with rfl|rfl
  · change A i j = ∑ t,1*(W t i*z t j)
    have hh := congrFun (columns A j).symm i
    change A i j = (∑ t,z t j • A.mulVec (b t)) i at hh
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hh
    rw [hh]
    apply Finset.sum_congr rfl
    intro t _
    change z t j*W t i = 1*(W t i*z t j)
    ring
  · change B i j = ∑ t,(A.det⁻¹*μ t)*(W t i*z t j)
    have hh := congrFun (columns B j).symm i
    change B i j = (∑ t,z t j • B.mulVec (b t)) i at hh
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hh
    rw [hh]
    apply Finset.sum_congr rfl
    intro t _
    rw [Bact]
    change z t j*((A.det⁻¹*μ t)*W t i)=(A.det⁻¹*μ t)*(W t i*z t j)
    ring


end MaxCube.UpperNine

namespace MaxCube.UpperNine

open Polynomial

/-- This fixed-degree resultant detects an invertible first slice and four
distinct generalized eigenvalues without introducing an inverse matrix. -/
noncomputable def pencilTest {K : Type*} [CommRing K] (A B : Matrix (Fin 4) (Fin 4) K) : K :=
  let f := (A.adjugate*B).charpoly
  A.det * f.resultant f.derivative 4 3

lemma pencilTest_ne_zero (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    pencilTest A B≠0 ↔ A.det≠0 ∧ (A.adjugate*B).charpoly.Separable := by
  let f := (A.adjugate*B).charpoly
  have h4 : f.natDegree=4 := by rw [show f=(A.adjugate*B).charpoly from rfl,Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin]
  have h3 : f.derivative.natDegree=3 := by rw [Polynomial.natDegree_derivative,h4]
  have H := Polynomial.isUnit_resultant_iff_isCoprime (f:=f) (g:=f.derivative) (A.adjugate*B).charpoly_monic
  change IsUnit (f.resultant f.derivative f.natDegree f.derivative.natDegree) ↔ _ at H
  rw [h4,h3,isUnit_iff_ne_zero] at H
  change A.det * f.resultant f.derivative 4 3 ≠ 0 ↔ A.det ≠ 0 ∧ f.Separable
  rw [ne_eq,mul_eq_zero,not_or,Polynomial.separable_def]
  exact and_congr_right fun _ => H

private lemma map_pencilTest {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A B : Matrix (Fin 4) (Fin 4) R) :
    φ (pencilTest A B)=pencilTest (A.map φ) (B.map φ) := by
  have hA : A.adjugate.map φ=(A.map φ).adjugate := φ.map_adjugate A
  have hD : (A.adjugate*B).map φ=(A.map φ).adjugate*B.map φ := by rw [Matrix.map_mul,hA]
  have hc := Matrix.charpoly_map (A.adjugate*B) φ
  rw [hD] at hc
  unfold pencilTest
  rw [map_mul,← Polynomial.resultant_map_map,← Polynomial.derivative_map,← hc,
    RingHom.map_det,RingHom.mapMatrix_apply]

def slice {R : Type*} [CommRing R] (T : Fin 4 → Matrix (Fin 4) (Fin 4) R) (u : Fin 4 → R) :
    Matrix (Fin 4) (Fin 4) R := fun i j => ∑ t,u t*T t i j

/-- If one regular simple-spectrum pencil occurs in the slice span, an
invertible slice change gives two disjoint regular simple-spectrum pencils. -/
lemma two_good_pairs (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (u v : Fin 4 → ℂ) (good : pencilTest (slice T u) (slice T v) ≠ 0) :
    ∃ U : Matrix (Fin 4) (Fin 4) ℂ, U.det ≠ 0 ∧
      pencilTest (slice T (U 0)) (slice T (U 1)) ≠ 0 ∧
      pencilTest (slice T (U 2)) (slice T (U 3)) ≠ 0 := by
  classical
  let V := Fin 4 × Fin 4
  let W := MvPolynomial V ℂ
  let C : Matrix (Fin 4) (Fin 4) W := fun i j => MvPolynomial.X (i,j)
  let A (i : Fin 4) := slice (fun t => (T t).map (MvPolynomial.C : ℂ →+* W)) (C i)
  let val (p : V → ℂ) : Matrix (Fin 4) (Fin 4) ℂ := fun i j => p (i,j)
  have mat (p : V → ℂ) : C.map (MvPolynomial.eval p)=val p := by
    ext i j
    change MvPolynomial.eval p (MvPolynomial.X (i,j))=p (i,j)
    exact MvPolynomial.eval_X (i,j)
  have sl (p : V → ℂ) (i : Fin 4) : (A i).map (MvPolynomial.eval p)=slice T (val p i) := by
    ext j k
    simp [A,slice,val,C,Matrix.map_apply]
  have det_ne : C.det≠0 := by
    let p : V → ℂ := fun s => (1 : Matrix (Fin 4) (Fin 4) ℂ) s.1 s.2
    have hone : val p=1 := rfl
    have he : MvPolynomial.eval p C.det=1 := by rw [RingHom.map_det,RingHom.mapMatrix_apply,mat,hone,Matrix.det_one]
    intro h
    rw [h,map_zero] at he
    exact zero_ne_one he
  have pair_ne (i j : Fin 4) (hij : i≠j) : pencilTest (A i) (A j) ≠ 0 := by
    let p : V → ℂ := fun s => if s.1=i then u s.2 else v s.2
    have pi₁ : val p i=u := by funext t; simp [val,p]
    have pi₂ : val p j=v := by funext t; simp [val,p,Ne.symm hij]
    intro h
    have he := congrArg (MvPolynomial.eval p) h
    rw [map_pencilTest,sl,sl,pi₁,pi₂,map_zero] at he
    exact good he
  have nz : C.det*pencilTest (A 0) (A 1)*pencilTest (A 2) (A 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero det_ne (pair_ne _ _ (by decide))) (pair_ne _ _ (by decide))
  obtain ⟨p,hp⟩ : ∃ p : V → ℂ, MvPolynomial.eval p (C.det*pencilTest (A 0) (A 1)*pencilTest (A 2) (A 3)) ≠ 0 := by
    by_contra! hn
    exact nz (MvPolynomial.funext fun p => by rw [hn p,map_zero])
  rw [map_mul,map_mul,map_pencilTest,map_pencilTest,sl,sl,sl,sl,RingHom.map_det,RingHom.mapMatrix_apply,mat] at hp
  exact ⟨val p,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).2,(mul_ne_zero_iff.mp hp).2⟩

end MaxCube.UpperNine

namespace MaxCube.UpperNine

/-- A nonsingular first-axis change only changes the first factors of the
rank-one tensors in the decomposition. -/
private lemma undo_slice_change {r : ℕ} (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : U.det ≠ 0)
    (h : Decomp 4 4 4 r (fun t => slice T (U t))) : Decomp 4 4 4 r T := by
  classical
  obtain ⟨x,y,z,hs⟩ := h
  refine ⟨fun t => U⁻¹.mulVec (x t),y,z,?_⟩
  intro i j k
  have recover : (∑ q,U⁻¹ i q*slice T (U q) j k)=T i j k := by
    change (U⁻¹.mulVec (U.mulVec (fun q => T q j k))) i=T i j k
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul U (isUnit_iff_ne_zero.mpr hU),Matrix.one_mulVec]
  calc
    _ = ∑ q,U⁻¹ i q*(∑ t,x t q*(y t j*z t k)) := by
      rw [← recover]
      exact Finset.sum_congr rfl fun q _ => congrArg (fun a : ℂ => U⁻¹ i q*a) (hs q j k)
    _ = _ := by
      simp only [Finset.mul_sum,Matrix.mulVec,dotProduct,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro q _
      ring

private lemma join_pencils (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (L : Decomp 2 4 4 4 ![T 0,T 1]) (R : Decomp 2 4 4 4 ![T 2,T 3]) :
    Decomp 4 4 4 8 T := by
  obtain ⟨a,b,c,ha⟩ := L
  obtain ⟨d,e,f,hd⟩ := R
  let rows : (Fin 2 ⊕ Fin 2) ≃ Fin 4 := finSumFinEquiv
  let terms : (Fin 4 ⊕ Fin 4) ≃ Fin 8 := finSumFinEquiv
  let x (t : Fin 4 ⊕ Fin 4) (i : Fin 4) := t.elim
    (fun q => (rows.symm i).elim (a q) (fun _ => 0))
    (fun q => (rows.symm i).elim (fun _ => 0) (d q))
  refine ⟨fun t => x (terms.symm t),fun t => (terms.symm t).elim b e,fun t => (terms.symm t).elim c f,?_⟩
  intro i j k
  let F (q : Fin 4 ⊕ Fin 4) := x q i*((q.elim b e) j*(q.elim c f) k)
  change T i j k=∑ t : Fin 8,F (terms.symm t)
  rw [terms.symm.sum_comp F,Fintype.sum_sum_type]
  obtain ⟨s,rfl⟩ := rows.surjective i
  rcases s with s|s
  · simp only [F,x,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,zero_mul,Finset.sum_const_zero,add_zero]
    have hh : (![T 0,T 1] : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ) s=T (rows (.inl s)) := by
      rcases (show s=0 ∨ s=1 by omega) with rfl|rfl <;> rfl
    exact (congrFun (congrFun hh j) k).symm.trans (ha s j k)
  · simp only [F,x,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,zero_mul,Finset.sum_const_zero,zero_add]
    have hh : (![T 2,T 3] : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ) s=T (rows (.inr s)) := by
      rcases (show s=0 ∨ s=1 by omega) with rfl|rfl <;> rfl
    exact (congrFun (congrFun hh j) k).symm.trans (hd s j k)

/-- Four complex slices have tensor rank at most eight as soon as a pair of
their linear combinations gives a regular pencil with four distinct roots. -/
theorem eight_of_separable_pencil (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (u v : Fin 4 → ℂ) (hinv : (slice T u).det ≠ 0)
    (hsep : ((slice T u).adjugate * slice T v).charpoly.Separable) : Decomp 4 4 4 8 T := by
  obtain ⟨U,hU,h₁,h₂⟩ := two_good_pairs T u v ((pencilTest_ne_zero _ _).mpr ⟨hinv,hsep⟩)
  apply undo_slice_change T U hU
  apply join_pencils
  · obtain ⟨ha,hs⟩ := (pencilTest_ne_zero _ _).mp h₁
    exact pencil_four_of_separable _ _ ha hs
  · obtain ⟨ha,hs⟩ := (pencilTest_ne_zero _ _).mp h₂
    exact pencil_four_of_separable _ _ ha hs

/-- A single rank-one correction followed by an eight-term pencil decomposition. -/
theorem nine_of_rank_one_correction (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (x y z u v : Fin 4 → ℂ) :
    let S : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun t i j => T t i j-x t*(y i*z j)
    (slice S u).det ≠ 0 → ((slice S u).adjugate*slice S v).charpoly.Separable →
      Decomp 4 4 4 9 T := by
  intro S hA hs
  obtain ⟨a,b,c,h⟩ := eight_of_separable_pencil S u v hA hs
  refine ⟨Fin.snoc a x,Fin.snoc b y,Fin.snoc c z,?_⟩
  intro i j k
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,← h]
  change T i j k=T i j k-x i*(y j*z k)+x i*(y j*z k)
  ring

/-- Every counterexample to the rank-nine bound would retain a singular first
slice or a repeated eigenvalue for every pure correction and every pencil. -/
theorem obstruction_to_nine (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (h : ¬Decomp 4 4 4 9 T)
    (x y z u v : Fin 4 → ℂ) :
    let S : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun t i j => T t i j-x t*(y i*z j)
    (slice S u).det=0 ∨ ¬((slice S u).adjugate*slice S v).charpoly.Separable := by
  intro S
  by_contra! hn
  exact h (nine_of_rank_one_correction T x y z u v hn.1 hn.2)

end MaxCube.UpperNine

namespace MaxCube.PencilBridge

open Polynomial

/-- The coefficient of the top possible degree of det(XA-B) is det A. -/
theorem top_coefficient {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    ((X : ℂ[X]) • A.map C - B.map C).det.coeff (Fintype.card n) = A.det := by
  have hm : (-B).map (C : ℂ →+* ℂ[X]) = -(B.map C) := by ext i j; simp
  rw [sub_eq_add_neg, ← hm]
  exact coeff_det_X_add_C_card A (-B)

/-- A linear square matrix pencil cannot exceed its matrix size in degree. -/
theorem pencil_degree_le {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    ((X : ℂ[X]) • A.map C - B.map C).det.natDegree ≤ Fintype.card n := by
  have hm : (-B).map (C : ℂ →+* ℂ[X]) = -(B.map C) := by ext i j; simp
  rw [sub_eq_add_neg, ← hm]
  exact natDegree_det_X_add_C_le A (-B)

/-- In size four, full pencil degree is equivalent to an invertible leading matrix. -/
theorem quartic_iff (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    ((X : ℂ[X]) • A.map C - B.map C).det.natDegree = 4 ↔ A.det ≠ 0 := by
  let P := ((X : ℂ[X]) • A.map C - B.map C).det
  have hc : P.coeff 4 = A.det := by simpa only [P, Fintype.card_fin] using top_coefficient A B
  change P.natDegree=4 ↔ _
  constructor
  · intro hd
    have hz : P ≠ 0 := by intro h; simp [h] at hd
    rw [← hc, ← hd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hz
  · intro ha
    have hle : P.natDegree ≤ 4 := by simpa only [P, Fintype.card_fin] using pencil_degree_le A B
    exact le_antisymm hle (le_natDegree_of_ne_zero (hc.trans_ne ha))

private lemma eval_pencil {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) (z : ℂ) :
    (((X : ℂ[X]) • A.map C - B.map C).det).eval z = (z • A - B).det := by
  change evalRingHom z _ = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- The four distinct roots of the pencil determinant scale by det A to
four distinct roots of the adjugate pencil's characteristic polynomial. -/
theorem spectral_of_pencil (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : ((X : ℂ[X]) • A.map C - B.map C).det.natDegree = 4)
    (hs : ((X : ℂ[X]) • A.map C - B.map C).det.Separable) :
    A.det ≠ 0 ∧ (A.adjugate*B).charpoly.Separable := by
  classical
  let P := ((X : ℂ[X]) • A.map C - B.map C).det
  let H := A.adjugate*B
  change P.natDegree=4 at hd
  change P.Separable at hs
  have hP : P ≠ 0 := by intro h; simp [h] at hd
  have hA := (quartic_iff A B).mp hd
  refine ⟨hA,?_⟩
  have matrix_identity (z : ℂ) :
      Matrix.scalar (Fin 4) (A.det*z) - H = A.adjugate*(z • A-B) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.adjugate_mul, smul_smul, Matrix.smul_one_eq_diagonal]
    simp [Matrix.scalar_apply, H, mul_comm]
  let S := P.roots.toFinset
  have count : S.card=4 := by
    rw [show S=P.roots.toFinset from rfl, Multiset.toFinset_card_of_nodup (nodup_roots hs),
      IsAlgClosed.card_roots_eq_natDegree, hd]
  have subset : S.image (fun z => A.det*z) ⊆ H.charpoly.roots.toFinset := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    have hpz : P.eval z = 0 := (mem_roots hP).mp (Multiset.mem_toFinset.mp hz)
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots (Matrix.charpoly_monic H).ne_zero).mpr
    change H.charpoly.eval (A.det*z) = 0
    rw [Matrix.eval_charpoly, matrix_identity, Matrix.det_mul, ← eval_pencil]
    exact mul_eq_zero.mpr (.inr hpz)
  change H.charpoly.Separable
  apply (nodup_roots_iff_of_splits (Matrix.charpoly_monic H).ne_zero (IsAlgClosed.splits _)).mp
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  apply le_antisymm (Multiset.toFinset_card_le _)
  rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hi : Function.Injective (fun z : ℂ => A.det*z) := fun _ _ h => mul_left_cancel₀ hA h
  calc
    4 = S.card := count.symm
    _ = (S.image (fun z => A.det*z)).card := (Finset.card_image_of_injective _ hi).symm
    _ ≤ _ := Finset.card_le_card subset

/-- An affine rank-one change of the pencil changes just its two matrix
coefficients, with opposite signs in the constant slice. -/
theorem affine_update (A B : Matrix (Fin 4) (Fin 4) ℂ) (u v : Fin 4 → ℂ) (s b : ℂ) :
    (X : ℂ[X]) • A.map C - B.map C + (C s*X+C b) • (Matrix.vecMulVec u v).map C =
      (X : ℂ[X]) • (A+s • Matrix.vecMulVec u v).map C - (B-b • Matrix.vecMulVec u v).map C := by
  apply Matrix.ext
  intro i j
  simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- A rank-one affine correction with separable quartic determinant bounds
the rank of a tensor whose first two coordinate slices give the pencil. -/
theorem nine_of_separable_update (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (u v : Fin 4 → ℂ) (s b : ℂ)
    (hd : ((X : ℂ[X]) • (T 0).map C - (T 1).map C +
      (C s*X+C b) • (Matrix.vecMulVec u v).map C).det.natDegree = 4)
    (hs : ((X : ℂ[X]) • (T 0).map C - (T 1).map C +
      (C s*X+C b) • (Matrix.vecMulVec u v).map C).det.Separable) :
    Decomp 4 4 4 9 T := by
  rw [affine_update] at hd hs
  obtain ⟨ha,hb⟩ := spectral_of_pencil _ _ hd hs
  let x : Fin 4 → ℂ := ![-s,b,0,0]
  let S : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun t i j => T t i j-x t*(u i*v j)
  let e (l t : Fin 4) : ℂ := if t=l then 1 else 0
  have select (l : Fin 4) : MaxCube.UpperNine.slice S (e l) = S l := by
    ext i j
    simp [MaxCube.UpperNine.slice,e,ite_mul]
  have h₀ : S 0=T 0+s • Matrix.vecMulVec u v := by
    ext i j
    simp [S,x,Matrix.vecMulVec,smul_eq_mul]
  have h₁ : S 1=T 1-b • Matrix.vecMulVec u v := by
    ext i j
    simp [S,x,Matrix.vecMulVec,smul_eq_mul]
  apply MaxCube.UpperNine.nine_of_rank_one_correction T x u v (e 0) (e 1)
  · change (MaxCube.UpperNine.slice S (e 0)).det ≠ 0
    rwa [select,h₀]
  · change ((MaxCube.UpperNine.slice S (e 0)).adjugate*MaxCube.UpperNine.slice S (e 1)).charpoly.Separable
    rwa [select,select,h₀,h₁]

end MaxCube.PencilBridge

namespace MaxCube.Multiaffine

/-- Each perturbation variable occurs at most linearly. A square divisor can
therefore contain none of those variables. -/
theorem constant_of_square_dvd {σ R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (F G : MvPolynomial σ R) (hF : F≠0) (multi : ∀ i : σ, F.degreeOf i≤1)
    (divides : G*G ∣ F) : G=MvPolynomial.C (G.coeff 0) := by
  classical
  obtain ⟨H,eq⟩ := divides
  have nzG : G≠0 := by rintro rfl; simp [eq] at hF
  have nzH : H≠0 := by rintro rfl; simp [eq] at hF
  have zero (i : σ) : G.degreeOf i=0 := by
    have h := multi i
    rw [eq,MvPolynomial.degreeOf_mul_eq (mul_ne_zero nzG nzG) nzH,
      MvPolynomial.degreeOf_mul_eq nzG nzG] at h
    omega
  apply MvPolynomial.vars_eq_empty_iff_eq_C.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  exact fun i hin => (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hin) (zero i)

/-- A common square divisor of the coefficients is the only obstruction to
squarefreeness of a multiaffine polynomial over a domain. -/
theorem squarefree_of_scalar_squares {σ R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (F : MvPolynomial σ R) (hF : F≠0) (multi : ∀ i : σ, F.degreeOf i≤1)
    (scalars : ∀ p : R, (∀ d : σ →₀ ℕ, p^2 ∣ F.coeff d) → IsUnit p) : Squarefree F := by
  classical
  intro G div
  have constant := constant_of_square_dvd F G hF multi div
  obtain ⟨H,eq⟩ := div
  let p := G.coeff 0
  have product : F=MvPolynomial.C (p^2)*H := by
    change F=MvPolynomial.C ((G.coeff 0)^2)*H
    calc
      F=G*G*H := eq
      _=(MvPolynomial.C (G.coeff 0)*MvPolynomial.C (G.coeff 0))*H :=
        congrArg (fun t => t*t*H) constant
      _=_ := by rw [map_pow,pow_two]
  have coefficients (d : σ →₀ ℕ) : p^2 ∣ F.coeff d :=
    ⟨H.coeff d,by rw [product,MvPolynomial.coeff_C_mul]⟩
  rw [constant]
  exact (scalars p coefficients).map MvPolynomial.C

/-- Over an algebraically closed field, test the coefficients for a squared
linear factor at each scalar point of the pencil. -/
theorem squarefree_of_coefficients {σ K : Type*} [Field K] [IsAlgClosed K]
    (F : MvPolynomial σ (Polynomial K)) (hF : F≠0) (multi : ∀ i : σ, F.degreeOf i≤1)
    (roots : ∀ a : K, ∃ d : σ →₀ ℕ, ¬(Polynomial.X-Polynomial.C a)^2 ∣ F.coeff d) :
    Squarefree F := by
  apply squarefree_of_scalar_squares F hF multi
  intro p all
  by_contra not_unit
  have degree : p.degree ≠ 0 := fun h => not_unit (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_root p degree
  obtain ⟨d,ndvd⟩ := roots a
  exact ndvd ((pow_dvd_pow_of_dvd (Polynomial.dvd_iff_isRoot.mpr ha) 2).trans (all d))

/-- A nonvanishing cofactor supplies a coefficient test even at the origin,
where the universal update contributes a single factor X. -/
theorem not_sq_dvd_X_mul {K : Type*} [Field K] (a : K) (p : Polynomial K) (hp : p.eval a≠0) :
    ¬(Polynomial.X-Polynomial.C a)^2 ∣ Polynomial.X*p := by
  rintro ⟨q,hq⟩
  by_cases zero : a=0
  · subst a
    simp only [Polynomial.C_0,sub_zero,pow_two,mul_assoc] at hq
    have h := mul_left_cancel₀ (Polynomial.X_ne_zero (R:=K)) hq
    apply hp
    rw [h,Polynomial.eval_mul,Polynomial.eval_X,zero_mul]
  · have he := congrArg (Polynomial.eval a) hq
    simp [zero,hp] at he

theorem squarefree_of_X_cofactors {σ K : Type*} [Field K] [IsAlgClosed K]
    (F : MvPolynomial σ (Polynomial K)) (multi : ∀ i : σ, F.degreeOf i≤1)
    (cofactor : ∀ a : K, ∃ (d : σ →₀ ℕ) (p : Polynomial K),
      F.coeff d=Polynomial.X*p ∧ p.eval a≠0) : Squarefree F := by
  have roots (a : K) : ∃ d : σ →₀ ℕ, ¬(Polynomial.X-Polynomial.C a)^2 ∣ F.coeff d := by
    obtain ⟨d,p,coeff,nonzero⟩ := cofactor a
    exact ⟨d,coeff ▸ not_sq_dvd_X_mul a p nonzero⟩
  apply squarefree_of_coefficients F _ multi roots
  rintro rfl
  obtain ⟨d,ndvd⟩ := roots 0
  exact ndvd (by simp)

end MaxCube.Multiaffine

namespace MaxCube.SquarefreeSpecialize

/-- Localization preserves radical elements, since it commutes with the radical of a principal ideal. -/
private lemma radical_localization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] {f : R} (hf : IsRadical f) : IsRadical (algebraMap R S f) := by
  let J : Ideal R := Ideal.span {f}
  have hJ : J.IsRadical := isRadical_iff_span_singleton.mp hf
  have hmap : J.map (algebraMap R S) = Ideal.span {algebraMap R S f} := by
    rw [show J=Ideal.span {f} from rfl,Ideal.map_span,Set.image_singleton]
  apply isRadical_iff_span_singleton.mpr
  rw [← hmap]
  apply Ideal.radical_eq_iff.mp
  rw [← IsLocalization.map_radical M S,hJ.radical]

/-- Parameter-only factors become units in the coefficient fraction field. -/
private lemma fraction_separable {σ : Type*} (G : Polynomial (MvPolynomial σ ℂ)) (hs : Squarefree G) :
    (G.map (algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ)))).Separable := by
  classical
  let R := MvPolynomial σ ℂ
  let K := FractionRing R
  let A := Polynomial R
  let S := Polynomial K
  let _ : Algebra A S := Polynomial.algebra R K
  let L := (nonZeroDivisors R).map (Polynomial.C : R →+* A)
  let _ : IsLocalization L S := Polynomial.isLocalization (nonZeroDivisors R) K
  let φ := algebraMap R K
  have inj : Function.Injective φ := IsFractionRing.injective R K
  have hn : G.map φ ≠ 0 := by
    intro hz
    exact hs.ne_zero ((Polynomial.map_injective φ inj) (hz.trans (Polynomial.map_zero φ).symm))
  have hr : IsRadical (algebraMap A S G) := radical_localization L hs.isRadical
  exact PerfectField.separable_iff_squarefree.mpr (hr.squarefree hn)

private lemma eval_resultant {R S : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing S] [IsDomain S] [CharZero S] (G : Polynomial R) (φ : R →+* S)
    (hd : (G.map φ).natDegree=G.natDegree) :
    φ (G.resultant G.derivative) = (G.map φ).resultant (G.map φ).derivative := by
  have hder : (G.map φ).derivative.natDegree = G.derivative.natDegree := by simp only [Polynomial.natDegree_derivative,hd]
  change φ (G.resultant G.derivative G.natDegree G.derivative.natDegree) =
    (G.map φ).resultant (G.map φ).derivative (G.map φ).natDegree (G.map φ).derivative.natDegree
  rw [hd,hder,Polynomial.derivative_map,Polynomial.resultant_map_map]

/-- A squarefree univariate polynomial in algebraically independent parameters over the complex
numbers admits a complex specialization preserving degree and separability. -/
lemma specialize {σ : Type*} (G : Polynomial (MvPolynomial σ ℂ)) (hs : Squarefree G) :
    ∃ v : σ → ℂ, (G.map (MvPolynomial.eval v)).natDegree=G.natDegree ∧
      (G.map (MvPolynomial.eval v)).Separable := by
  classical
  let R := MvPolynomial σ ℂ
  let K := FractionRing R
  let φ := algebraMap R K
  have inj : Function.Injective φ := IsFractionRing.injective R K
  have hr : G.resultant G.derivative ≠ 0 := by
    intro hz
    have hd := Polynomial.natDegree_map_eq_of_injective (p:=G) inj
    have h := eval_resultant G φ hd
    rw [hz,map_zero] at h
    exact Polynomial.resultant_ne_zero _ _ (fraction_separable G hs) h.symm
  have hp : G.leadingCoeff * G.resultant G.derivative ≠ 0 := mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hs.ne_zero) hr
  obtain ⟨v,hv⟩ : ∃ v : σ → ℂ, MvPolynomial.eval v (G.leadingCoeff*G.resultant G.derivative) ≠ 0 := by
    by_contra! H
    apply hp
    apply MvPolynomial.funext
    intro v
    simpa only [map_zero] using H v
  rw [map_mul] at hv
  have hl := (mul_ne_zero_iff.mp hv).1
  have hd := Polynomial.natDegree_map_of_leadingCoeff_ne_zero (MvPolynomial.eval v) hl
  refine ⟨v,hd,?_⟩
  change IsCoprime (G.map (MvPolynomial.eval v)) (G.map (MvPolynomial.eval v)).derivative
  by_contra hbad
  have hn : G.map (MvPolynomial.eval v) ≠ 0 := by
    intro hz
    have hm := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (MvPolynomial.eval v) hl
    rw [hz,Polynomial.leadingCoeff_zero] at hm
    exact hl hm.symm
  have hb := Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hn,hbad⟩
  exact (mul_ne_zero_iff.mp hv).2 ((eval_resultant G (MvPolynomial.eval v) hd).trans hb)

end MaxCube.SquarefreeSpecialize

namespace MaxCube.SquarefreeSpecialize

/-- A globally squarefree polynomial in the perturbations and the pencil variable has
an evaluation of the perturbations that preserves its degree in the pencil variable
and has no repeated roots. -/
lemma of_mv {σ : Type*} (F : MvPolynomial σ (Polynomial ℂ)) (hF : Squarefree F) {n : ℕ}
    (hn : (MvPolynomial.eval₂Hom (Polynomial.mapRingHom (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ))
      (fun i : σ => Polynomial.C (MvPolynomial.X i : MvPolynomial σ ℂ)) F).natDegree=n) :
    ∃ v : σ → ℂ, (MvPolynomial.eval (fun i => Polynomial.C (v i)) F).natDegree=n ∧
      (MvPolynomial.eval (fun i => Polynomial.C (v i)) F).Separable := by
  classical
  let R := MvPolynomial σ ℂ
  let β : MvPolynomial σ (Polynomial ℂ) →+* Polynomial R :=
    MvPolynomial.eval₂Hom (Polynomial.mapRingHom (MvPolynomial.C : ℂ →+* R))
      (fun i => Polynomial.C (MvPolynomial.X i : R))
  let ψ : Polynomial R →+* MvPolynomial σ (Polynomial ℂ) :=
    Polynomial.eval₂RingHom (MvPolynomial.map (Polynomial.C : ℂ →+* Polynomial ℂ)) (MvPolynomial.C Polynomial.X)
  have leftC : ψ.comp (Polynomial.mapRingHom (MvPolynomial.C : ℂ →+* R)) = MvPolynomial.C := by
    apply Polynomial.ringHom_ext
    · intro z; simp [ψ]; exact MvPolynomial.map_C _ _
    · simp [ψ]
  have left : ψ.comp β=RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simpa only [RingHom.comp_apply,β,MvPolynomial.eval₂Hom_C,RingHom.id_apply] using DFunLike.congr_fun leftC z
    · intro i; simp [β,ψ]; exact MvPolynomial.map_X _ _
  have rightC : β.comp (MvPolynomial.map (Polynomial.C : ℂ →+* Polynomial ℂ)) = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro z; simp [β]
    · intro i; simp [β]
  have right : β.comp ψ=RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro z
      simpa [ψ] using DFunLike.congr_fun rightC z
    · simp [β,ψ]
  have hs : Squarefree (β F) := by
    intro h hh
    have hi : ψ (β F)=F := DFunLike.congr_fun left F
    have hd : ψ h * ψ h ∣ F := by simpa only [map_mul,hi] using! map_dvd ψ hh
    have hu := (hF (ψ h) hd).map β
    exact (show β (ψ h)=h from DFunLike.congr_fun right h) ▸ hu
  obtain ⟨v,hd,hsep⟩ := specialize (β F) hs
  have base : (MvPolynomial.eval v).comp (MvPolynomial.C : ℂ →+* R) = RingHom.id ℂ := by ext z; simp
  have comm : (Polynomial.mapRingHom (MvPolynomial.eval v)).comp β = MvPolynomial.eval (fun i => Polynomial.C (v i)) := by
    apply MvPolynomial.ringHom_ext
    · intro z; simp [β,base]
    · intro i; simp [β]
  have he : (β F).map (MvPolynomial.eval v) = MvPolynomial.eval (fun i => Polynomial.C (v i)) F :=
    DFunLike.congr_fun comm F
  exact ⟨v,he ▸ hd.trans hn,he ▸ hsep⟩

end MaxCube.SquarefreeSpecialize

namespace MaxCube.MinrankAdj

open Module

/-- Rank at least three forces a nonzero cofactor. Three independent range
vectors give a compression of a product through A to a 3 by 3 identity.
Multiplicativity of the adjugate transfers its nonvanishing back to A. -/
theorem adjugate_ne_zero (A : Matrix (Fin 4) (Fin 4) ℂ) (hr : 3≤A.rank) : A.adjugate≠0 := by
  classical
  let W := LinearMap.range A.mulVecLin
  let b := Module.finBasis ℂ W
  let e (i : Fin 3) : Fin (Module.finrank ℂ W) := i.castLE hr
  obtain ⟨ret,hret⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  have retr (v : W) : ret (v : Fin 4 → ℂ)=v := DFunLike.congr_fun hret v
  choose u hu using fun i : Fin 3 => (b (e i)).property
  let Q : Matrix (Fin 4) (Fin 4) ℂ := fun i j => Fin.lastCases 0 (fun t => u t i) j
  let L : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) :=
    LinearMap.pi (Fin.lastCases 0 (fun i => (b.coord (e i)).comp ret))
  let P := LinearMap.toMatrix' L
  have qc (j : Fin 3) : Q.col j.castSucc = u j := by
    funext k
    change Fin.lastCases (motive:=fun _ : Fin 4 => ℂ) 0 (fun t => u t k) j.castSucc=u j k
    rw [Fin.lastCases_castSucc]
  have minor : (P*A*Q).submatrix Fin.castSucc Fin.castSucc = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext i j
    change ((P*A).mulVec (Q.col j.castSucc)) i.castSucc = _
    rw [qc,←Matrix.mulVec_mulVec]
    have y : A.mulVec (u j)=(b (e j) : Fin 4 → ℂ) := hu j
    rw [y]
    change ((LinearMap.toMatrix' L).mulVec (b (e j))) i.castSucc = _
    rw [LinearMap.toMatrix'_mulVec]
    simp only [L,LinearMap.pi_apply,Fin.lastCases_castSucc,LinearMap.comp_apply,retr]
    rw [Basis.coord_apply,Basis.repr_self_apply,Matrix.one_apply]
    by_cases eq : i=j
    · subst j
      simp
    · have ne : e j≠e i := by
        intro h
        apply eq
        apply Fin.ext
        exact (congrArg Fin.val h).symm
      simp [eq,ne]
  intro h
  have zero : (P*A*Q).adjugate = 0 := by
    rw [Matrix.adjugate_mul_distrib,Matrix.adjugate_mul_distrib,h,zero_mul,Matrix.mul_zero]
  have entry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M (Fin.last 3) (Fin.last 3)) zero
  change (P*A*Q).adjugate (Fin.last 3) (Fin.last 3)=0 at entry
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,Fin.succAbove_last,minor,Matrix.det_one] at entry
  norm_num [Fin.last] at entry

end MaxCube.MinrankAdj

namespace MaxCube.MinrankAdj

open Polynomial

/-- The signed complementary 3 by 3 determinant has degree at most three
and its cubic coefficient is the same cofactor of the leading slice. -/
theorem entry_bounds (A B : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    let M := (X : ℂ[X]) • A.map C - B.map C
    (X*M.adjugate i j).natDegree ≤ 4 ∧ (X*M.adjugate i j).coeff 4=A.adjugate i j := by
  intro M
  let U := A.submatrix j.succAbove i.succAbove
  let V := -(B.submatrix j.succAbove i.succAbove)
  let N := (X : ℂ[X]) • U.map C + V.map C
  let s := (-1:ℂ)^(j.val+i.val)
  have sub : M.submatrix j.succAbove i.succAbove=N := by
    ext u v
    simp [M,U,V,N,Matrix.smul_apply,Matrix.map_apply,Matrix.submatrix_apply,sub_eq_add_neg]
  have sign : (-1:ℂ[X])^(j.val+i.val)=C s := by simp [s]
  have cofac : M.adjugate i j=C s*N.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix,sub,sign]
  have low : N.det.natDegree≤3 := by
    simpa only [Fintype.card_fin] using Polynomial.natDegree_det_X_add_C_le U V
  have top : N.det.coeff 3=U.det := by
    simpa only [Fintype.card_fin] using Polynomial.coeff_det_X_add_C_card U V
  rw [cofac]
  constructor
  · have con : (C s*N.det).natDegree ≤ (C s).natDegree + N.det.natDegree := Polynomial.natDegree_mul_le
    have hi : (X*(C s*N.det)).natDegree ≤ (X:ℂ[X]).natDegree + (C s*N.det).natDegree := Polynomial.natDegree_mul_le
    simp only [Polynomial.natDegree_C,Polynomial.natDegree_X,zero_add] at con hi
    omega
  · calc
      (X*(C s*N.det)).coeff 4 = (C s*N.det).coeff 3 := Polynomial.coeff_X_mul _ 3
      _ = s*U.det := by rw [Polynomial.coeff_C_mul,top]
      _ = A.adjugate i j := (Matrix.adjugate_fin_succ_eq_det_submatrix A i j).symm

private lemma nonzero_cofactor (A : Matrix (Fin 4) (Fin 4) ℂ) (h : 3≤A.rank) :
    ∃ i j, A.adjugate i j≠0 := by
  by_contra! empty
  exact adjugate_ne_zero A h (Matrix.ext empty)

theorem leading_nonzero (A B : Matrix (Fin 4) (Fin 4) ℂ) (hr : 3≤A.rank) :
    let M := (X : ℂ[X]) • A.map C - B.map C
    ∃ i j, (X*M.adjugate i j).coeff 4 ≠ 0 := by
  intro M
  obtain ⟨i,j,h⟩ := nonzero_cofactor A hr
  exact ⟨i,j,(entry_bounds A B i j).2.trans_ne h⟩

/-- At a nonzero parameter a nonzero cofactor is already a nonzero value.
At zero, the single factor X has multiplicity exactly one for that entry. -/
theorem local_multiplicity (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (finiteRank : ∀ α : ℂ, 3≤(α • A-B).rank) (α : ℂ) :
    let M := (X : ℂ[X]) • A.map C - B.map C
    ∃ i j : Fin 4, ¬(X-C α)^2 ∣ X*M.adjugate i j := by
  intro M
  let ev := Polynomial.evalRingHom α
  have val : ev.mapMatrix M = α • A-B := by
    ext i j
    simp [M,ev,RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.smul_apply]
    exact mul_comm _ _
  have val_adj (i j : Fin 4) : Polynomial.eval α (M.adjugate i j)=(α • A-B).adjugate i j := by
    have he : ev.mapMatrix M.adjugate = (α • A-B).adjugate := (ev.map_adjugate M).trans (congrArg Matrix.adjugate val)
    exact congrArg (fun L : Matrix (Fin 4) (Fin 4) ℂ => L i j) he
  obtain ⟨i,j,h⟩ := nonzero_cofactor (α • A-B) (finiteRank α)
  refine ⟨i,j,?_⟩
  by_cases zero : α=0
  · subst α
    intro hd
    have hd' : (X:ℂ[X])^2 ∣ X*M.adjugate i j := by simpa using hd
    obtain ⟨d,eq⟩ := hd'
    rw [pow_two,mul_assoc] at eq
    have eq' : M.adjugate i j=X*d := mul_left_cancel₀ Polynomial.X_ne_zero eq
    apply h
    rw [←val_adj,eq']
    simp
  · rintro ⟨d,eq⟩
    have evd := congrArg (Polynomial.eval α) eq
    simp only [Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_pow,Polynomial.eval_sub,
      Polynomial.eval_C,sub_self,zero_pow (by decide : 2≠0),zero_mul,val_adj] at evd
    exact (mul_ne_zero zero h) evd

end MaxCube.MinrankAdj

namespace MaxCube.DetUpdate

/-- The rank-one determinant identity, without any invertibility hypothesis.
After replacing row r by v, adding multiples of v to the other rows preserves
the determinant. Multilinearity in row r then gives its cofactor contribution. -/
theorem det_add_outer {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (u v : n → R) :
    (A + Matrix.vecMulVec u v).det = A.det + ∑ i,∑ j, u i*v j*A.adjugate j i := by
  classical
  let mat (s : Finset n) : Matrix n n R := fun i j => if i∈s then A i j+u i*v j else A i j
  have empty : mat ∅=A := by ext i j; simp [mat]
  have insertRow (s : Finset n) (i : n) (hi : i∉s) :
      mat (insert i s) = (mat s).updateRow i (mat s i + u i • v) := by
    ext j k
    by_cases hj : j=i
    · subst j
      rw [Matrix.updateRow_self]
      simp [mat,hi]
    · rw [Matrix.updateRow_ne hj]
      simp [mat,hj]
  have clear (r : n) (s : Finset n) (hr : r∉s) :
      ((mat s).updateRow r v).det = (A.updateRow r v).det := by
    induction s using Finset.induction_on with
    | empty => rw [empty]
    | @insert i s hi ih =>
      have hir : i≠r := by intro e; exact hr (e ▸ Finset.mem_insert_self _ _)
      have hrs : r∉s := fun h => hr (Finset.mem_insert_of_mem h)
      let M := (mat s).updateRow r v
      have swap : (mat (insert i s)).updateRow r v = M.updateRow i (M i+u i • M r) := by
        rw [insertRow s i hi]
        ext j k
        by_cases hj : j=i
        · subst j
          simp [M,hir]
        · by_cases h' : j=r
          · subst j
            simp [M,Ne.symm hir]
          · simp [M,hj,h']
      rw [swap,Matrix.det_updateRow_add_smul_self M hir,ih hrs]
  have cofactor (i : n) : (A.updateRow i v).det = ∑ j,v j*A.adjugate j i := by
    rw [Matrix.det_eq_sum_mul_adjugate_row (A.updateRow i v) i]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.updateRow_self,Matrix.adjugate_apply,Matrix.adjugate_apply]
    congr 2
    ext k l
    by_cases hk : k=i <;> simp [hk]
  have expansion (s : Finset n) : (mat s).det = A.det+∑ i∈s,∑ j,u i*v j*A.adjugate j i := by
    induction s using Finset.induction_on with
    | empty => simp [empty]
    | @insert i s hi ih =>
      rw [insertRow s i hi,Matrix.det_updateRow_add,Matrix.updateRow_eq_self,Matrix.det_updateRow_smul,
        clear i s hi,cofactor,ih,Finset.sum_insert hi,Finset.mul_sum]
      simp only [mul_assoc]
      abel
  have all : mat Finset.univ=A+Matrix.vecMulVec u v := by ext i j; simp [mat,Matrix.vecMulVec_apply]
  rw [← all]
  exact expansion Finset.univ

end MaxCube.DetUpdate

namespace MaxCube.DetUpdate

open Polynomial

def left (i : Fin 4) : Fin 8 := (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8) (.inl i)
def right (j : Fin 4) : Fin 8 := (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8) (.inr j)

def params (u v : Fin 4 → ℂ) (k : Fin 8) : ℂ :=
  ((finSumFinEquiv.symm k : Fin 4 ⊕ Fin 4)).elim u v

@[simp] lemma params_left (u v : Fin 4 → ℂ) (i : Fin 4) : params u v (left i) = u i := by
  simp [params,left]

@[simp] lemma params_right (u v : Fin 4 → ℂ) (j : Fin 4) : params u v (right j) = v j := by
  simp [params,right]

noncomputable def pencil (A B : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) (Polynomial ℂ) :=
  (Polynomial.X : Polynomial ℂ) • A.map (Polynomial.C : ℂ →+* Polynomial ℂ) - B.map Polynomial.C

noncomputable def exponent (i j : Fin 4) : Fin 8 →₀ ℕ :=
  Finsupp.single (left i) 1 + Finsupp.single (right j) 1

private lemma exp_left (i j k : Fin 4) : exponent i j (left k) = if i=k then 1 else 0 := by
  simp [exponent,Finsupp.single_apply,left,right]
private lemma exp_right (i j k : Fin 4) : exponent i j (right k) = if j=k then 1 else 0 := by
  simp [exponent,Finsupp.single_apply,left,right]

lemma exponent_ne_zero (i j : Fin 4) : exponent i j≠0 := by
  intro h
  have he := congrArg (fun m : Fin 8 →₀ ℕ => m (left i)) h
  simp [exp_left] at he

lemma exponent_eq_iff (i j k l : Fin 4) : exponent i j=exponent k l ↔ i=k ∧ j=l := by
  constructor
  · intro h
    have hu := congrArg (fun m : Fin 8 →₀ ℕ => m (left i)) h
    have hv := congrArg (fun m : Fin 8 →₀ ℕ => m (right j)) h
    simp only [exp_left,exp_right] at hu hv
    constructor
    · by_contra hki
      simp [Ne.symm hki] at hu
    · by_contra hlj
      simp [Ne.symm hlj] at hv
  · rintro ⟨rfl,rfl⟩
    rfl

noncomputable def F (A B : Matrix (Fin 4) (Fin 4) ℂ) : MvPolynomial (Fin 8) (Polynomial ℂ) :=
  MvPolynomial.C (pencil A B).det +
    ∑ i,∑ j,MvPolynomial.monomial (exponent i j) (Polynomial.X * (pencil A B).adjugate j i)

lemma coeff_F (A B : Matrix (Fin 4) (Fin 4) ℂ) (m : Fin 8 →₀ ℕ) :
    (F A B).coeff m = (if 0=m then (pencil A B).det else 0) +
      ∑ i,∑ j, if exponent i j=m then Polynomial.X*(pencil A B).adjugate j i else 0 := by
  simp only [F,MvPolynomial.coeff_add,MvPolynomial.coeff_C,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]

lemma coeff_zero (A B : Matrix (Fin 4) (Fin 4) ℂ) : (F A B).coeff 0 = (pencil A B).det := by
  simp [coeff_F,exponent_ne_zero]

lemma coeff_cross (A B : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    (F A B).coeff (exponent i j) = Polynomial.X*(pencil A B).adjugate j i := by
  simp [coeff_F,Ne.symm (exponent_ne_zero i j),exponent_eq_iff,ite_and,Finset.sum_ite_irrel]

lemma support_shape (A B : Matrix (Fin 4) (Fin 4) ℂ) (m : Fin 8 →₀ ℕ) (h : (F A B).coeff m≠0) :
    m=0 ∨ ∃ i j, m=exponent i j := by
  by_contra! hn
  apply h
  simp [coeff_F,Ne.symm hn.1,fun i j => Ne.symm (hn.2 i j)]

lemma degreeOf_le_one (A B : Matrix (Fin 4) (Fin 4) ℂ) (q : Fin 8) :
    (F A B).degreeOf q ≤ 1 := by
  have hb (i j : Fin 4) : exponent i j q≤1 := by
    obtain ⟨k,rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8).surjective q
    rcases k with k|k
    · change exponent i j (left k)≤1
      rw [exp_left]; split <;> decide
    · change exponent i j (right k)≤1
      rw [exp_right]; split <;> decide
  unfold F
  apply (MvPolynomial.degreeOf_add_le _ _ _).trans
  apply max_le
  · simp
  · apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro i _
    apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro j _
    by_cases hz : Polynomial.X*(pencil A B).adjugate j i=0
    · simp [hz]
    · rw [MvPolynomial.degreeOf_monomial_eq _ _ hz]
      exact hb i j

private lemma monomial_form (i j : Fin 4) (p : Polynomial ℂ) :
    MvPolynomial.monomial (exponent i j) p =
      MvPolynomial.C p*(MvPolynomial.X (left i)*MvPolynomial.X (right j)) := by
  change MvPolynomial.monomial (exponent i j) p =
    MvPolynomial.monomial 0 p*(MvPolynomial.monomial (Finsupp.single (left i) 1) 1 *
      MvPolynomial.monomial (Finsupp.single (right j) 1) 1)
  rw [MvPolynomial.monomial_mul,MvPolynomial.monomial_mul]
  simp only [zero_add,mul_one,exponent]

lemma eval_F (A B : Matrix (Fin 4) (Fin 4) ℂ) (s : Fin 8 → Polynomial ℂ) :
    MvPolynomial.eval s (F A B) = (pencil A B).det +
      ∑ i,∑ j,(Polynomial.X*(pencil A B).adjugate j i)*(s (left i)*s (right j)) := by
  simp [F,monomial_form]

/-- Substituting u and v in the eight parameter positions gives the determinant
of t (A + u vᵀ) - B, including when the original pencil is singular. -/
theorem specialize (A B : Matrix (Fin 4) (Fin 4) ℂ) (u v : Fin 4 → ℂ) :
    MvPolynomial.eval (fun q => Polynomial.C (params u v q)) (F A B) =
      (pencil (A+Matrix.vecMulVec u v) B).det := by
  have hmat : pencil (A+Matrix.vecMulVec u v) B =
      pencil A B + Matrix.vecMulVec (fun i => Polynomial.X*Polynomial.C (u i)) (fun j => Polynomial.C (v j)) := by
    apply Matrix.ext
    intro i j
    change Polynomial.X*Polynomial.C (A i j+u i*v j)-Polynomial.C (B i j) =
      Polynomial.X*Polynomial.C (A i j)-Polynomial.C (B i j)+(Polynomial.X*Polynomial.C (u i))*Polynomial.C (v j)
    rw [map_add,map_mul]
    ring
  rw [eval_F,hmat,det_add_outer]
  apply congrArg (fun x => (pencil A B).det+x)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [params_left,params_right]
  ring

end MaxCube.DetUpdate

namespace MaxCube.DetUpdate

lemma params_eta (s : Fin 8 → ℂ) :
    params (fun i => s (left i)) (fun j => s (right j)) = s := by
  funext q
  obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8).surjective q
  rcases i with i|j
  · exact params_left _ _ i
  · exact params_right _ _ j

lemma specialize_at (A B : Matrix (Fin 4) (Fin 4) ℂ) (s : Fin 8 → ℂ) :
    MvPolynomial.eval (fun q => Polynomial.C (s q)) (F A B) =
      (pencil (A+Matrix.vecMulVec (fun i => s (left i)) (fun j => s (right j))) B).det := by
  simpa only [params_eta] using specialize A B (fun i => s (left i)) (fun j => s (right j))

end MaxCube.DetUpdate

namespace MaxCube.ParamDegree

open Polynomial

/-- Reorder the parameter variables and the scalar variable of a pencil. -/
private noncomputable abbrev swap {σ : Type*} (F : MvPolynomial σ (Polynomial ℂ)) :=
  MvPolynomial.eval₂Hom (Polynomial.mapRingHom (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ))
    (fun i : σ => Polynomial.C (MvPolynomial.X i : MvPolynomial σ ℂ)) F

theorem coeff_swap {σ : Type*} (F : MvPolynomial σ (Polynomial ℂ)) (m : σ →₀ ℕ) (n : ℕ) :
    ((swap F).coeff n).coeff m = (F.coeff m).coeff n := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial d p =>
    have prod : d.prod (fun i k => Polynomial.C (MvPolynomial.X i : MvPolynomial σ ℂ) ^ k) =
        Polynomial.C (MvPolynomial.monomial d 1 : MvPolynomial σ ℂ) := by
      rw [← MvPolynomial.prod_X_pow_eq_monomial]
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [swap, MvPolynomial.eval₂Hom_monomial, prod, Polynomial.coeff_mul_C]
    change ((p.map MvPolynomial.C).coeff n * MvPolynomial.monomial d 1).coeff m = _
    rw [Polynomial.coeff_map, MvPolynomial.C_mul_monomial, mul_one]
    by_cases h : d = m <;> simp [h]
  | add f g hf hg =>
    simpa only [swap, map_add, Polynomial.coeff_add, MvPolynomial.coeff_add] using congrArg₂ (·+·) hf hg

/-- A polynomial has exact scalar degree n if every parameter coefficient
has degree at most n and at least one has a nonzero coefficient at n. -/
theorem degree_of_coefficients {σ : Type*} (F : MvPolynomial σ (Polynomial ℂ)) (n : ℕ)
    (bound : ∀ m, (F.coeff m).natDegree ≤ n) (attain : ∃ m, (F.coeff m).coeff n ≠ 0) :
    (MvPolynomial.eval₂Hom (Polynomial.mapRingHom (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ))
      (fun i : σ => Polynomial.C (MvPolynomial.X i : MvPolynomial σ ℂ)) F).natDegree = n := by
  change (swap F).natDegree = n
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    apply MvPolynomial.ext
    intro m
    rw [coeff_swap, MvPolynomial.coeff_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (bound m) hk)
  · obtain ⟨m,hm⟩ := attain
    apply Polynomial.le_natDegree_of_ne_zero
    intro h
    apply hm
    rw [← coeff_swap, h, MvPolynomial.coeff_zero]

end MaxCube.ParamDegree

namespace MaxCube

open Polynomial DetUpdate

/-- A projective pencil with no matrix of rank below three can acquire
four distinct eigenvalues after one rank-one change of its leading matrix. -/
theorem regularize_four_pencil (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hA : 3 ≤ A.rank) (line : ∀ α : ℂ, 3 ≤ (α • A - B).rank) :
    ∃ u v : Fin 4 → ℂ, (pencil (A + Matrix.vecMulVec u v) B).det.natDegree = 4 ∧
      (pencil (A + Matrix.vecMulVec u v) B).det.Separable := by
  classical
  have bound (m : Fin 8 →₀ ℕ) : ((F A B).coeff m).natDegree ≤ 4 := by
    by_cases zero : (F A B).coeff m = 0
    · simp [zero]
    rcases support_shape A B m zero with rfl | ⟨i,j,rfl⟩
    · rw [coeff_zero]
      have related : pencil A B = (X : ℂ[X]) • A.map C + (-B).map C := by
        ext i j
        simp [pencil, sub_eq_add_neg]
      rw [related]
      simpa only [Fintype.card_fin] using Polynomial.natDegree_det_X_add_C_le A (-B)
    · rw [coeff_cross]
      exact (MinrankAdj.entry_bounds A B j i).1
  obtain ⟨i,j,hij⟩ := MinrankAdj.leading_nonzero A B hA
  have top : ((F A B).coeff (exponent j i)).coeff 4 ≠ 0 := by
    rw [coeff_cross]
    exact hij
  have hn := ParamDegree.degree_of_coefficients (F A B) 4 bound ⟨exponent j i,top⟩
  have notzero : F A B ≠ 0 := by
    intro he
    simp [he] at top
  have square : Squarefree (F A B) := by
    apply Multiaffine.squarefree_of_coefficients _ notzero (degreeOf_le_one A B)
    intro α
    obtain ⟨j,k,h⟩ := MinrankAdj.local_multiplicity A B line α
    exact ⟨exponent k j, by rw [coeff_cross]; exact h⟩
  obtain ⟨s,degree,separable⟩ := SquarefreeSpecialize.of_mv (F A B) square (n:=4) hn
  have evaluate := DetUpdate.specialize_at A B s
  exact ⟨fun l => s (left l),fun l => s (right l),evaluate ▸ degree,evaluate ▸ separable⟩

theorem nine_of_minrank_pencil (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hA : 3 ≤ (T 0).rank) (line : ∀ α : ℂ, 3 ≤ (α • T 0 - T 1).rank) : Decomp 4 4 4 9 T := by
  obtain ⟨u,v,degree,separable⟩ := regularize_four_pencil (T 0) (T 1) hA line
  apply PencilBridge.nine_of_separable_update T u v 1 0
  · rw [PencilBridge.affine_update, one_smul, zero_smul, sub_zero]
    exact degree
  · rw [PencilBridge.affine_update, one_smul, zero_smul, sub_zero]
    exact separable

end MaxCube

-- Problem: Generic and maximal rank of 3-tensors — cprank le of three slices
-- Upstream: formal-conjectures FormalConjectures/Arxiv/0805.3777/TensorRank.lean:291 (declaration Arxiv.«0805.3777».cprank_le_of_three_slices)
-- Credit: @ivillar
--
-- Proof. Every complex n x n x 3 tensor has rank at most 2n - 1 (Sumi, Miyazaki, Sakata,
-- Ann. Inst. Statist. Math. 62 (2010), Theorem 4.5; arXiv 0806.4048). We follow the structure of
-- their induction, on the level of the span of the three slices (CP3.Cov): pick a nonzero
-- singular matrix in the span, bring it to a 0/1 diagonal form, and split into cases.
-- * A nonzero entry in the zero block, or a column of the zero block with independent fibres:
--   their Lemma 4.3 (perturb by diagonal matrices so that the remaining pencil has distinct
--   eigenvalues). The analytic perturbation argument is replaced by an algebraic one: indices
--   are added one at a time, and h + x F is separable for all but finitely many x when F is
--   separable (CP3.fel, CP3.osl, CP3.osl_all); distinct eigenvalues give a diagonalisation
--   (CP3.nice_of_good). Their Lemma 4.4 is replaced by an explicit elementary conjugation.
-- * A zero row (or column) in the zero block, or only rank-one fibres: peel rows and columns
--   and use the induction hypothesis.
--
-- Reuse and credit: the section Bridge (holor indices, slices, rank-one holors, and the passage
-- from a cover by rank-one matrices to a CP-rank bound) is adapted from the Bridge section of
-- proofs/Arxiv.0805.3777.isMaxRank_three_three_five_bounds.lean (merged in PR 2438, credited to
-- DomTheDeveloper), which is itself a port of the work of Kenta Kitamura,
-- https://github.com/KitaKen1/mrank-3-3-5-lean (Apache License 2.0). Everything else is new.

namespace CP3

open Matrix Polynomial

theorem sep_iff (f : ℂ[X]) :
    f.Separable ↔ ∀ a : ℂ, f.eval a ≠ 0 ∨ (derivative f).eval a ≠ 0 := by
  rw [separable_def, isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  simp only [coe_aeval_eq_eval]

theorem fel (F h : ℂ[X]) (hF : F.Separable) :
    {x : ℂ | ¬ (h + C x * F).Separable}.Finite := by
  set W := F * derivative h - derivative F * h with hWdef
  have hF0 : F ≠ 0 := hF.ne_zero
  by_cases hW : W = 0
  · have hdvd : F ∣ h := by
      have h1 : F ∣ h * derivative F := ⟨derivative h, by linear_combination (-1 : ℂ[X]) * hW⟩
      exact ((separable_def F).mp hF).dvd_of_dvd_mul_right h1
    obtain ⟨g, rfl⟩ := hdvd
    have hg : derivative g = 0 := by
      have h2 : F * F * derivative g = 0 := by
        rw [hWdef, derivative_mul] at hW
        linear_combination hW
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd (mul_self_eq_zero.mp h3) hF0
      · exact h3
    have hgC := eq_C_of_derivative_eq_zero hg
    apply (Set.finite_singleton (-(g.coeff 0))).subset
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [Set.mem_singleton_iff]
    by_contra hne
    apply hx
    have : F * g + C x * F = F * C (g.coeff 0 + x) := by
      rw [hgC]; simp only [coeff_C_zero, C_add]; ring
    rw [this]
    refine hF.mul_unit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_))
    intro h0; apply hne; linear_combination h0
  · let φ : ℂ → ℂ := fun a => if F.eval a ≠ 0 then -(h.eval a / F.eval a)
      else -((derivative h).eval a / (derivative F).eval a)
    apply ((W.roots.toFinset.finite_toSet).image φ).subset
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rw [sep_iff] at hx
    push Not at hx
    obtain ⟨a, ha1, ha2⟩ := hx
    simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add, eval_add,
      eval_mul, eval_C] at ha1 ha2
    refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [mem_roots hW, IsRoot, hWdef]
      simp only [eval_sub, eval_mul]
      linear_combination (eval a F) * ha2 - (eval a (derivative F)) * ha1
    · simp only [φ]
      by_cases hFa : F.eval a ≠ 0
      · rw [if_pos hFa, neg_eq_iff_eq_neg, div_eq_iff hFa]; linear_combination ha1
      · rw [if_neg hFa]
        push Not at hFa
        have hF' : (derivative F).eval a ≠ 0 := by
          rcases (sep_iff F).mp hF a with h4 | h4
          · exact absurd hFa h4
          · exact h4
        rw [neg_eq_iff_eq_neg, div_eq_iff hF']; linear_combination ha2

/-- determinant is affine in the bottom-right corner entry -/
theorem det_add_corner {R : Type*} [CommRing R] (k : ℕ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (a : R) : (M + diagonal (Pi.single (Fin.last k) a)).det
      = M.det + a * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_row _ (Fin.last k), det_succ_row M (Fin.last k)]
  simp_rw [Fin.succAbove_last]
  have hsub : ∀ j : Fin (k + 1), ((M + diagonal (Pi.single (Fin.last k) a)).submatrix
      Fin.castSucc j.succAbove) = M.submatrix Fin.castSucc j.succAbove := by
    intro j; ext r c
    simp [diagonal_apply, Fin.castSucc_ne_last]
  simp_rw [hsub]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have h1 : ∀ j : Fin k, (M + diagonal (Pi.single (Fin.last k) a)) (Fin.last k) j.castSucc
      = M (Fin.last k) j.castSucc := by
    intro j; simp [(Fin.castSucc_ne_last j).symm]
  have h2 : (M + diagonal (Pi.single (Fin.last k) a)) (Fin.last k) (Fin.last k)
      = M (Fin.last k) (Fin.last k) + a := by simp
  simp_rw [h1, h2, Fin.succAbove_last]
  have : ((-1 : R) ^ ((Fin.last k : ℕ) + (Fin.last k : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]; simp
  rw [this]
  ring


/-- the pencil polynomial `det (X U + V)` -/
noncomputable def penPoly {n : Type*} [Fintype n] [DecidableEq n] (U V : Matrix n n ℂ) : ℂ[X] :=
  ((X : ℂ[X]) • U.map C + V.map C).det

/-- a pencil with invertible first member and `n` distinct generalized eigenvalues -/
def Good {n : Type*} [Fintype n] [DecidableEq n] (U V : Matrix n n ℂ) : Prop :=
  U.det ≠ 0 ∧ (penPoly U V).Separable

theorem exists_eval_ne_zero {p : ℂ[X]} (hp : p ≠ 0) : ∃ a : ℂ, p.eval a ≠ 0 := by
  obtain ⟨a, ha⟩ := (p.roots.toFinset.finite_toSet).exists_notMem
  refine ⟨a, fun h0 => ha ?_⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  exact (mem_roots hp).mpr h0

theorem osl (k : ℕ) (U V : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (h : Good (U.submatrix Fin.castSucc Fin.castSucc) (V.submatrix Fin.castSucc Fin.castSucc)) :
    ∃ x y : ℂ, Good (U + diagonal (Pi.single (Fin.last k) x))
      (V + diagonal (Pi.single (Fin.last k) y)) := by
  set Ub := U.submatrix Fin.castSucc Fin.castSucc
  set Vb := V.submatrix Fin.castSucc Fin.castSucc
  set pb := penPoly Ub Vb with hpb
  have hpb0 : pb ≠ 0 := h.2.ne_zero
  obtain ⟨a, ha⟩ := exists_eval_ne_zero hpb0
  have hcop : IsCoprime (X - C a) pb := by
    rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
    intro b
    simp only [coe_aeval_eq_eval, eval_sub, eval_X, eval_C]
    by_cases hb : b = a
    · right; rw [hb]; exact ha
    · left; exact sub_ne_zero.mpr hb
  set F := (X - C a) * pb with hF
  have hFs : F.Separable := (separable_X_sub_C (R := ℂ) (x := a)).mul h.2 hcop
  have hpen : ∀ x : ℂ, penPoly (U + diagonal (Pi.single (Fin.last k) x))
      (V + diagonal (Pi.single (Fin.last k) (-a * x))) = penPoly U V + C x * F := by
    intro x
    unfold penPoly
    have e1 : (X : ℂ[X]) • (U + diagonal (Pi.single (Fin.last k) x)).map C
        + (V + diagonal (Pi.single (Fin.last k) (-a * x))).map C
        = ((X : ℂ[X]) • U.map C + V.map C) + diagonal (Pi.single (Fin.last k) (C x * (X - C a))) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, diagonal_apply,
        smul_eq_mul]
      by_cases hij : i = j
      · subst hij
        by_cases hi : i = Fin.last k
        · subst hi; simp only [if_true, Pi.single_eq_same, map_add, map_mul, map_neg]; ring
        · simp [Pi.single_eq_of_ne hi]
      · simp [hij]
    rw [e1, det_add_corner]
    have e2 : ((X : ℂ[X]) • U.map C + V.map C).submatrix Fin.castSucc Fin.castSucc
        = (X : ℂ[X]) • Ub.map C + Vb.map C := by
      ext i j; simp [Ub, Vb]
    rw [e2, hF, hpb]
    unfold penPoly
    ring
  have hdet : ∀ x : ℂ, (U + diagonal (Pi.single (Fin.last k) x)).det = U.det + x * Ub.det :=
    fun x => det_add_corner k U x
  have hfin := fel F (penPoly U V) hFs
  have hfin2 : {x : ℂ | U.det + x * Ub.det = 0}.Finite := by
    apply (Set.finite_singleton (-(U.det / Ub.det))).subset
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [Set.mem_singleton_iff]
    rw [eq_neg_iff_add_eq_zero, add_div_eq_mul_add_div _ _ h.1, div_eq_zero_iff]
    left; linear_combination hx
  obtain ⟨x, hx⟩ := (hfin.union hfin2).exists_notMem
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hx
  refine ⟨x, -a * x, ?_, ?_⟩
  · rw [hdet]; exact hx.2
  · rw [hpen]; exact hx.1

theorem osl_all (s : ℕ) : ∀ (n : ℕ) (hs : s ≤ n) (U V : Matrix (Fin n) (Fin n) ℂ),
    Good (U.submatrix (Fin.castLE hs) (Fin.castLE hs)) (V.submatrix (Fin.castLE hs) (Fin.castLE hs))
    → ∃ d₁ d₂ : Fin n → ℂ, (∀ i : Fin n, (i : ℕ) < s → d₁ i = 0 ∧ d₂ i = 0)
      ∧ Good (U + diagonal d₁) (V + diagonal d₂) := by
  intro n
  induction n with
  | zero =>
    intro hs U V h
    obtain rfl : s = 0 := by omega
    refine ⟨0, 0, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
    have hU : U + diagonal (0 : Fin 0 → ℂ) = U.submatrix (Fin.castLE hs) (Fin.castLE hs) :=
      Subsingleton.elim _ _
    have hV : V + diagonal (0 : Fin 0 → ℂ) = V.submatrix (Fin.castLE hs) (Fin.castLE hs) :=
      Subsingleton.elim _ _
    rw [hU, hV]; exact h
  | succ k ih =>
    intro hs U V h
    by_cases hsk : s = k + 1
    · subst hsk
      refine ⟨0, 0, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
      have e : ∀ W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
          W.submatrix (Fin.castLE hs) (Fin.castLE hs) = W + diagonal 0 := by
        intro W; ext i j; simp
      rw [e U, e V] at h; exact h
    · have hs' : s ≤ k := by omega
      obtain ⟨e₁, e₂, he, hg⟩ := ih hs' (U.submatrix Fin.castSucc Fin.castSucc)
        (V.submatrix Fin.castSucc Fin.castSucc) (by
          have e : ∀ W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
              (W.submatrix Fin.castSucc Fin.castSucc).submatrix (Fin.castLE hs') (Fin.castLE hs')
              = W.submatrix (Fin.castLE hs) (Fin.castLE hs) := by
            intro W; ext i j; simp
          rw [e U, e V]; exact h)
      have e3 : ∀ (W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (e : Fin k → ℂ),
          (W + diagonal (Fin.snoc e 0)).submatrix Fin.castSucc Fin.castSucc
            = W.submatrix Fin.castSucc Fin.castSucc + diagonal e := by
        intro W e; ext i j
        simp only [submatrix_apply, Matrix.add_apply, diagonal_apply, Fin.castSucc_inj,
          Fin.snoc_castSucc]
      obtain ⟨x, y, hxy⟩ := osl k (U + diagonal (Fin.snoc e₁ 0))
        (V + diagonal (Fin.snoc e₂ 0)) (by rw [e3, e3]; exact hg)
      refine ⟨Fin.snoc e₁ 0 + Pi.single (Fin.last k) x, Fin.snoc e₂ 0 + Pi.single (Fin.last k) y,
        ?_, ?_⟩
      · intro i hi
        have hne : i ≠ Fin.last k := by
          intro h0; rw [h0, Fin.val_last] at hi; omega
        obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hne
        have hi' : (i' : ℕ) < s := by simpa using hi
        rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne,
          Fin.snoc_castSucc, Fin.snoc_castSucc, (he i' hi').1, (he i' hi').2]
        simp
      · have key : ∀ (W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (f g : Fin (k + 1) → ℂ),
            W + diagonal (f + g) = W + diagonal f + diagonal g := by
          intro W f g; rw [add_assoc, diagonal_add]; rfl
        rw [key, key]; exact hxy

theorem core1 (U V : Matrix (Fin 1) (Fin 1) ℂ) (h : U 0 0 ≠ 0) : Good U V := by
  refine ⟨by rw [det_unique]; exact h, ?_⟩
  unfold penPoly
  rw [det_unique]
  have : ((X : ℂ[X]) • U.map C + V.map C) default default = C (U 0 0) * (X + C (V 0 0 / U 0 0)) := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [mul_add, ← C_mul, mul_div_cancel₀ _ h]
    simp only [Fin.default_eq_zero]; ring
  rw [this]
  exact Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr h)) (separable_X_add_C _)

theorem lin_sep {α β : ℂ} (h : α ≠ 0) : (X * C α + C β).Separable := by
  have : X * C α + C β = C α * (X + C (β / α)) := by
    rw [mul_add, ← C_mul, mul_div_cancel₀ _ h]; ring
  rw [this]
  exact Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr h)) (separable_X_add_C _)

theorem core2 (U V : Matrix (Fin 2) (Fin 2) ℂ) (h11 : U 1 1 = 0) (h11' : V 1 1 = 0)
    (h1 : U 0 1 * U 1 0 ≠ 0) (h2 : U 0 1 * V 1 0 ≠ V 0 1 * U 1 0) : Good U V := by
  refine ⟨by rw [det_fin_two, h11]; simpa using h1, ?_⟩
  have hα : U 0 1 ≠ 0 := left_ne_zero_of_mul h1
  have hβ : U 1 0 ≠ 0 := right_ne_zero_of_mul h1
  unfold penPoly
  rw [det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, h11, h11',
    map_zero, mul_zero, add_zero, zero_sub]
  rw [neg_eq_neg_one_mul, ← C_1, ← C_neg]
  refine Separable.unit_mul (isUnit_C.mpr (by norm_num)) ((lin_sep hα).mul (lin_sep hβ) ?_)
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  intro a
  simp only [coe_aeval_eq_eval, eval_add, eval_mul, eval_X, eval_C]
  by_contra hc
  push Not at hc
  apply h2
  linear_combination (U 0 1) * hc.2 - (U 1 0) * hc.1

theorem outer_sum {k : ℕ} (M W : Matrix (Fin k) (Fin k) ℂ) (hW : W.det ≠ 0) :
    M = ∑ l, vecMulVec (M *ᵥ fun i => W i l) (W⁻¹ l) := by
  have h1 : M = M * W * W⁻¹ := by
    rw [Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hW), Matrix.mul_one]
  ext i j
  conv_lhs => rw [h1]
  simp only [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply, mulVec, dotProduct,
    Finset.sum_mul]

theorem nice_of_good {k : ℕ} (U V : Matrix (Fin k) (Fin k) ℂ) (h : Good U V) :
    ∃ (x y : Fin k → Fin k → ℂ) (c : Fin k → ℂ),
      U = ∑ l, vecMulVec (x l) (y l) ∧ V = ∑ l, c l • vecMulVec (x l) (y l) := by
  set p := penPoly U V with hp
  have hp0 : p ≠ 0 := h.2.ne_zero
  have hdeg : p.natDegree = k := by
    apply le_antisymm
    · have := natDegree_det_X_add_C_le U V
      simp only [Fintype.card_fin] at this
      rw [hp, penPoly]; exact this
    · apply le_natDegree_of_ne_zero
      have := coeff_det_X_add_C_card U V
      simp only [Fintype.card_fin] at this
      rw [hp, penPoly, this]; exact h.1
  have hcard : p.roots.card = k := by
    rw [← hdeg]; exact splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hnd : p.roots.Nodup := nodup_roots h.2
  have hfc : p.roots.toFinset.card = k := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  let μ : Fin k → ℂ := fun l => (p.roots.toFinset.equivFin.symm (Fin.cast hfc.symm l) : ℂ)
  have hμinj : Function.Injective μ := by
    intro a b hab
    have := Subtype.val_injective hab
    exact Fin.cast_injective _ (p.roots.toFinset.equivFin.symm.injective this)
  have hμroot : ∀ l, p.eval (μ l) = 0 := by
    intro l
    have hm : μ l ∈ p.roots.toFinset := (p.roots.toFinset.equivFin.symm _).2
    rw [Multiset.mem_toFinset, mem_roots hp0] at hm
    exact hm
  have hdet : ∀ l, (μ l • U + V).det = 0 := by
    intro l
    rw [← hμroot l, hp, penPoly, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X, eval_C]
  choose v hv0 hv using fun l => exists_mulVec_eq_zero_iff.mpr (hdet l)
  have hUu : IsUnit U := (isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr h.1)
  have hVv : ∀ l, V *ᵥ v l = (-(μ l)) • (U *ᵥ v l) := by
    intro l
    have := hv l
    rw [add_mulVec, smul_mulVec] at this
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact this
  have heig : ∀ l, Module.End.HasEigenvector (toLin' (U⁻¹ * V)) (-(μ l)) (v l) := by
    intro l
    refine ⟨?_, hv0 l⟩
    rw [Module.End.mem_eigenspace_iff, toLin'_apply, ← mulVec_mulVec, hVv l, mulVec_smul,
      mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det U).mp hUu), one_mulVec]
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (toLin' (U⁻¹ * V)) (fun l => -(μ l))
      (neg_injective.comp hμinj) v heig
  let W : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun i l => v l i
  have hWcol : W.col = v := by ext l i; rfl
  have hW : IsUnit W := (linearIndependent_cols_iff_isUnit (K := ℂ)).mp (by rw [hWcol]; exact hli)
  have hWd : W.det ≠ 0 := ((isUnit_iff_isUnit_det W).mp hW).ne_zero
  have hcol : ∀ l, (fun i => W i l) = v l := fun l => rfl
  refine ⟨fun l => U *ᵥ v l, fun l => W⁻¹ l, fun l => -(μ l), ?_, ?_⟩
  · conv_lhs => rw [outer_sum U W hWd]
    simp only [hcol]
  · conv_lhs => rw [outer_sum V W hWd]
    simp only [hcol, hVv, smul_vecMulVec]


/- ### Coverings of matrix spaces by rank-one matrices -/

/-- `M` has rank at most one -/
def IsR1 {ι κ : Type*} (M : Matrix ι κ ℂ) : Prop := ∃ (a : ι → ℂ) (b : κ → ℂ), M = vecMulVec a b

/-- `S` lies in the span of at most `r` matrices of rank at most one -/
def Cov {ι κ : Type*} (S : Submodule ℂ (Matrix ι κ ℂ)) (r : ℕ) : Prop :=
  ∃ s : Finset (Matrix ι κ ℂ), s.card ≤ r ∧ (∀ M ∈ s, IsR1 M) ∧ S ≤ Submodule.span ℂ (s : Set _)

section CovAPI

variable {ι κ ι' κ' : Type*}

theorem Cov.mono {S S' : Submodule ℂ (Matrix ι κ ℂ)} {r : ℕ} (h : S' ≤ S) (hS : Cov S r) :
    Cov S' r := by
  obtain ⟨s, hs, h1, h2⟩ := hS
  exact ⟨s, hs, h1, h.trans h2⟩

theorem Cov.mono_r {S : Submodule ℂ (Matrix ι κ ℂ)} {r r' : ℕ} (h : r ≤ r') (hS : Cov S r) :
    Cov S r' := by
  obtain ⟨s, hs, h1, h2⟩ := hS
  exact ⟨s, hs.trans h, h1, h2⟩

theorem Cov.sup {S₁ S₂ : Submodule ℂ (Matrix ι κ ℂ)} {r₁ r₂ : ℕ} (h₁ : Cov S₁ r₁)
    (h₂ : Cov S₂ r₂) : Cov (S₁ ⊔ S₂) (r₁ + r₂) := by
  classical
  obtain ⟨s, hs, hs1, hs2⟩ := h₁
  obtain ⟨t, ht, ht1, ht2⟩ := h₂
  refine ⟨s ∪ t, (Finset.card_union_le _ _).trans (by omega), ?_, ?_⟩
  · intro M hM
    rcases Finset.mem_union.mp hM with h | h
    · exact hs1 M h
    · exact ht1 M h
  · refine sup_le (hs2.trans (Submodule.span_mono ?_)) (ht2.trans (Submodule.span_mono ?_))
    · intro x hx; simp only [Finset.coe_union]; exact Or.inl hx
    · intro x hx; simp only [Finset.coe_union]; exact Or.inr hx

theorem Cov.map {S : Submodule ℂ (Matrix ι κ ℂ)} {r : ℕ}
    (f : Matrix ι κ ℂ →ₗ[ℂ] Matrix ι' κ' ℂ) (hf : ∀ M, IsR1 M → IsR1 (f M)) (hS : Cov S r) :
    Cov (S.map f) r := by
  classical
  obtain ⟨s, hs, h1, h2⟩ := hS
  refine ⟨s.image f, Finset.card_image_le.trans hs, ?_, ?_⟩
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hM
    exact hf N (h1 N hN)
  · refine (Submodule.map_mono h2).trans ?_
    rw [Submodule.map_span, Finset.coe_image]

theorem cov_family {β : Type*} [Fintype β] (x : β → ι → ℂ) (y : β → κ → ℂ) :
    Cov (Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l))) (Fintype.card β) := by
  classical
  refine ⟨Finset.univ.image fun l => vecMulVec (x l) (y l), Finset.card_image_le, ?_, ?_⟩
  · intro M hM
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hM
    exact ⟨x l, y l, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨l, rfl⟩
    simp

/-- the span of three matrices -/
def sp3 (A B C : Matrix ι κ ℂ) : Submodule ℂ (Matrix ι κ ℂ) :=
  Submodule.span ℂ ({A, B, C} : Set (Matrix ι κ ℂ))

theorem sp3_map (f : Matrix ι κ ℂ →ₗ[ℂ] Matrix ι' κ' ℂ) (A B C : Matrix ι κ ℂ) :
    (sp3 A B C).map f = sp3 (f A) (f B) (f C) := by
  rw [sp3, sp3, Submodule.map_span]
  congr 1
  simp [Set.image_insert_eq]

theorem sp3_le {A B C : Matrix ι κ ℂ} {S : Submodule ℂ (Matrix ι κ ℂ)} (hA : A ∈ S) (hB : B ∈ S)
    (hC : C ∈ S) : sp3 A B C ≤ S := by
  rw [sp3, Submodule.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

theorem mem_sp3_1 (A B C : Matrix ι κ ℂ) : A ∈ sp3 A B C := Submodule.subset_span (by simp)
theorem mem_sp3_2 (A B C : Matrix ι κ ℂ) : B ∈ sp3 A B C := Submodule.subset_span (by simp)
theorem mem_sp3_3 (A B C : Matrix ι κ ℂ) : C ∈ sp3 A B C := Submodule.subset_span (by simp)

theorem cov_transfer {A B C : Matrix ι κ ℂ} {r : ℕ} (f : Matrix ι κ ℂ →ₗ[ℂ] Matrix ι' κ' ℂ)
    (g : Matrix ι' κ' ℂ →ₗ[ℂ] Matrix ι κ ℂ) (hg : ∀ M, IsR1 M → IsR1 (g M))
    (hA : g (f A) = A) (hB : g (f B) = B) (hC : g (f C) = C)
    (h : Cov (sp3 (f A) (f B) (f C)) r) : Cov (sp3 A B C) r := by
  have := h.map g hg
  rwa [sp3_map, hA, hB, hC] at this

end CovAPI

/-- `M ↦ P * M * Q` as a linear map -/
def lrMul {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] (P : Matrix ι' ι ℂ) (Q : Matrix κ κ' ℂ) :
    Matrix ι κ ℂ →ₗ[ℂ] Matrix ι' κ' ℂ where
  toFun M := P * M * Q
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem lrMul_apply {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] (P : Matrix ι' ι ℂ)
    (Q : Matrix κ κ' ℂ) (M : Matrix ι κ ℂ) : lrMul P Q M = P * M * Q := rfl

theorem isR1_lrMul {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] (P : Matrix ι' ι ℂ)
    (Q : Matrix κ κ' ℂ) (M : Matrix ι κ ℂ) (h : IsR1 M) : IsR1 (lrMul P Q M) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨P *ᵥ a, b ᵥ* Q, by
    show P * vecMulVec a b * Q = _
    rw [mul_vecMulVec, vecMulVec_mul]⟩

/-- reindexing (submatrix by functions) as a linear map -/
def subL {ι κ ι' κ' : Type*} (e : ι' → ι) (f : κ' → κ) :
    Matrix ι κ ℂ →ₗ[ℂ] Matrix ι' κ' ℂ where
  toFun M := M.submatrix e f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem subL_apply {ι κ ι' κ' : Type*} (e : ι' → ι) (f : κ' → κ) (M : Matrix ι κ ℂ) :
    subL e f M = M.submatrix e f := rfl

theorem isR1_subL {ι κ ι' κ' : Type*} (e : ι' → ι) (f : κ' → κ) (M : Matrix ι κ ℂ)
    (h : IsR1 M) : IsR1 (subL e f M) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨a ∘ e, b ∘ f, rfl⟩

/-- transposition as a linear map -/
def trL {ι κ : Type*} : Matrix ι κ ℂ →ₗ[ℂ] Matrix κ ι ℂ where
  toFun M := Mᵀ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem trL_apply {ι κ : Type*} (M : Matrix ι κ ℂ) : trL M = Mᵀ := rfl

theorem isR1_trL {ι κ : Type*} (M : Matrix ι κ ℂ) (h : IsR1 M) : IsR1 (trL M) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨b, a, by ext i j; exact mul_comm _ _⟩

/-- extension by zero from a pair of subtypes -/
def extL {ι κ : Type*} (p : ι → Prop) (q : κ → Prop) [DecidablePred p] [DecidablePred q] :
    Matrix {x // p x} {y // q y} ℂ →ₗ[ℂ] Matrix ι κ ℂ where
  toFun M := Matrix.of fun i j => if h : p i ∧ q j then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  map_add' X Y := by ext i j; by_cases h : p i ∧ q j <;> simp [h]
  map_smul' c X := by ext i j; by_cases h : p i ∧ q j <;> simp [h]

theorem isR1_extL {ι κ : Type*} (p : ι → Prop) (q : κ → Prop) [DecidablePred p] [DecidablePred q]
    (M : Matrix {x // p x} {y // q y} ℂ) (h : IsR1 M) : IsR1 (extL p q M) := by
  obtain ⟨a, b, rfl⟩ := h
  refine ⟨fun i => if h : p i then a ⟨i, h⟩ else 0, fun j => if h : q j then b ⟨j, h⟩ else 0, ?_⟩
  ext i j
  simp only [extL, LinearMap.coe_mk, AddHom.coe_mk, vecMulVec_apply, Matrix.of_apply]
  by_cases hi : p i <;> by_cases hj : q j <;> simp [hi, hj]

/-- compression: a triple supported on `p × q` is covered if its compression is -/
theorem cov_compress {ι κ : Type*} (p : ι → Prop) (q : κ → Prop) [DecidablePred p]
    [DecidablePred q] {A B C : Matrix ι κ ℂ} {r : ℕ}
    (hA : ∀ i j, A i j ≠ 0 → p i ∧ q j) (hB : ∀ i j, B i j ≠ 0 → p i ∧ q j)
    (hC : ∀ i j, C i j ≠ 0 → p i ∧ q j)
    (h : Cov (sp3 (subL Subtype.val Subtype.val A : Matrix {x // p x} {y // q y} ℂ)
      (subL Subtype.val Subtype.val B) (subL Subtype.val Subtype.val C)) r) :
    Cov (sp3 A B C) r := by
  have key : ∀ M : Matrix ι κ ℂ, (∀ i j, M i j ≠ 0 → p i ∧ q j) →
      extL p q (subL Subtype.val Subtype.val M) = M := by
    intro M hM
    ext i j
    simp only [extL, subL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
    split_ifs with hij
    · rfl
    · by_contra hne; exact hij (hM i j (Ne.symm hne))
  exact cov_transfer _ (extL p q) (isR1_extL p q) (key A hA) (key B hB) (key C hC) h

/- ### The perturbation lemma (SMS10, Lemma 4.3) -/

theorem diag_sum {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) :
    diagonal d = ∑ l, d l • vecMulVec (Pi.single l 1) (Pi.single l 1) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul, diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : i = l
    · subst hl; simp [Ne.symm hij]
    · simp [hl]

theorem L43Fin {n s : ℕ} (hs : s ≤ n) (D : Fin n → ℂ) (B C : Matrix (Fin n) (Fin n) ℂ)
    (j0 : Fin n) (hj0 : (j0 : ℕ) < s) (hD : D j0 = 0)
    (hgood : Good (B.submatrix (Fin.castLE hs) (Fin.castLE hs))
      (C.submatrix (Fin.castLE hs) (Fin.castLE hs))) :
    Cov (sp3 (diagonal D) B C) (2 * n - 1) := by
  classical
  obtain ⟨d₁, d₂, hd, hg⟩ := osl_all s n hs B C hgood
  obtain ⟨x, y, c, hB, hC⟩ := nice_of_good _ _ hg
  let E : Fin n → Matrix (Fin n) (Fin n) ℂ := fun l => vecMulVec (Pi.single l 1) (Pi.single l 1)
  let T₁ : Finset (Matrix (Fin n) (Fin n) ℂ) := (Finset.univ.erase j0).image E
  let T₂ : Finset (Matrix (Fin n) (Fin n) ℂ) := Finset.univ.image fun l => vecMulVec (x l) (y l)
  have hT₁ : T₁.card ≤ n - 1 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hT₂ : T₂.card ≤ n := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
  have hn : 1 ≤ n := by have := j0.2; omega
  refine ⟨T₁ ∪ T₂, (Finset.card_union_le _ _).trans (by omega), ?_, ?_⟩
  · intro M hM
    rcases Finset.mem_union.mp hM with h | h
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h
      exact ⟨_, _, rfl⟩
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h
      exact ⟨_, _, rfl⟩
  · set W := Submodule.span ℂ ((T₁ ∪ T₂ : Finset _) : Set (Matrix (Fin n) (Fin n) ℂ))
    have hdiag : ∀ d : Fin n → ℂ, d j0 = 0 → diagonal d ∈ W := by
      intro d hd0
      rw [diag_sum, ← Finset.sum_erase Finset.univ (a := j0) (by simp [hd0])]
      apply Submodule.sum_mem
      intro l hl
      apply Submodule.smul_mem
      apply Submodule.subset_span
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      left
      exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
    have hnice : ∀ c' : Fin n → ℂ, ∑ l, c' l • vecMulVec (x l) (y l) ∈ W := by
      intro c'
      apply Submodule.sum_mem
      intro l _
      apply Submodule.smul_mem
      apply Submodule.subset_span
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      right
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
    apply sp3_le (hdiag D hD)
    · have : B = (B + diagonal d₁) - diagonal d₁ := by abel
      rw [this, hB]
      refine W.sub_mem ?_ (hdiag d₁ (hd j0 hj0).1)
      simpa using hnice 1
    · have : C = (C + diagonal d₂) - diagonal d₂ := by abel
      rw [this, hC]
      exact W.sub_mem (hnice c) (hdiag d₂ (hd j0 hj0).2)

theorem exists_equiv_core {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (core : Fin s → ι)
    (hcore : Function.Injective core) (hs : s ≤ Fintype.card ι) :
    ∃ e : ι ≃ Fin (Fintype.card ι), ∀ a, e (core a) = Fin.castLE hs a := by
  classical
  let p : ι → Prop := fun x => x ∈ Set.range core
  let e₁ : {x // p x} ≃ Fin s := (Equiv.ofInjective core hcore).symm
  have hc1 : Fintype.card {x // p x} = s := by rw [Fintype.card_congr e₁, Fintype.card_fin]
  have hc : Fintype.card {x // ¬ p x} = Fintype.card ι - s := by
    rw [Fintype.card_subtype_compl, hc1]
  let e₂ : {x // ¬ p x} ≃ Fin (Fintype.card ι - s) := Fintype.equivFinOfCardEq hc
  let e : ι ≃ Fin (Fintype.card ι) := (Equiv.sumCompl p).symm.trans ((Equiv.sumCongr e₁ e₂).trans
    (finSumFinEquiv.trans (finCongr (by omega))))
  refine ⟨e, fun a => ?_⟩
  have hp : p (core a) := ⟨a, rfl⟩
  simp only [e, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hp, Equiv.sumCongr_apply,
    Sum.map_inl, finSumFinEquiv_apply_left]
  ext
  have h1 : (Equiv.ofInjective core hcore).symm ⟨core a, hp⟩ = a :=
    Equiv.ofInjective_symm_apply hcore a
  simp [e₁, h1]

theorem L43 {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (core : Fin s → ι)
    (hcore : Function.Injective core) (D : ι → ℂ) (B C : Matrix ι ι ℂ) (j0 : Fin s)
    (hD : D (core j0) = 0) (hgood : Good (B.submatrix core core) (C.submatrix core core)) :
    Cov (sp3 (diagonal D) B C) (2 * Fintype.card ι - 1) := by
  have hs : s ≤ Fintype.card ι := by
    simpa using Fintype.card_le_of_injective core hcore
  obtain ⟨e, he⟩ := exists_equiv_core s core hcore hs
  have he' : ∀ a, e.symm (Fin.castLE hs a) = core a := by
    intro a; rw [← he a, Equiv.symm_apply_apply]
  have hgg : ∀ M : Matrix ι ι ℂ, subL e e (subL e.symm e.symm M) = M := by
    intro M; ext i j; simp [subL_apply]
  refine cov_transfer (subL e.symm e.symm) (subL e e) (isR1_subL e e) (hgg _) (hgg _) (hgg _) ?_
  have hdg : subL e.symm e.symm (diagonal D) = diagonal (D ∘ e.symm) := by
    ext i j; simp [subL_apply, diagonal_apply]
  rw [hdg]
  have hsub : ∀ M : Matrix ι ι ℂ, (subL e.symm e.symm M).submatrix (Fin.castLE hs) (Fin.castLE hs)
      = M.submatrix core core := by
    intro M; ext i j; simp [subL_apply, he']
  refine L43Fin hs (D ∘ e.symm) _ _ (Fin.castLE hs j0) (by simp) (by simp [he', hD]) ?_
  rw [hsub, hsub]; exact hgood

/- ### The case analysis -/

/-- the inductive statement -/
def Pn (n : ℕ) : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ],
    Fintype.card ι = n → Fintype.card κ = n → ∀ A B C : Matrix ι κ ℂ, Cov (sp3 A B C) (2 * n - 1)

theorem cov_pair {ι κ : Type*} (a₁ a₂ : ι → ℂ) (b₁ b₂ : κ → ℂ) :
    Cov (Submodule.span ℂ ({vecMulVec a₁ b₁, vecMulVec a₂ b₂} : Set (Matrix ι κ ℂ))) 2 := by
  have := cov_family (fun l : Fin 2 => ![a₁, a₂] l) (fun l : Fin 2 => ![b₁, b₂] l)
  rw [Fintype.card_fin] at this
  refine this.mono (Submodule.span_mono ?_)
  intro M hM
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem card_ne_sub {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι) :
    Fintype.card {x // x ≠ j} = Fintype.card ι - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- (a): a nonzero entry in the zero block of `diagonal D` -/
theorem stepA {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℂ) (B C : Matrix ι ι ℂ) (i j : ι)
    (hi : D i = 0) (hj : D j = 0) (hB : B i j ≠ 0) :
    Cov (sp3 (diagonal D) B C) (2 * Fintype.card ι - 1) := by
  set σ := Equiv.swap i j
  have hgg : ∀ M : Matrix ι ι ℂ, subL id σ (subL id σ M) = M := by
    intro M; ext a b; simp [subL_apply, σ]
  refine cov_transfer (subL id σ) (subL id σ) (isR1_subL id σ) (hgg _) (hgg _) (hgg _) ?_
  have hdg : subL id σ (diagonal D) = diagonal D := by
    ext a b
    simp only [subL_apply, submatrix_apply, id, diagonal_apply, σ]
    by_cases hb1 : b = i
    · subst hb1; rw [Equiv.swap_apply_left]
      by_cases ha : a = j
      · subst ha; simp [hj]
      · by_cases hab : a = b
        · subst hab; simp [hi]
        · simp [ha, hab]
    · by_cases hb2 : b = j
      · subst hb2; rw [Equiv.swap_apply_right]
        by_cases ha : a = i
        · subst ha; simp [hi]
        · by_cases hab : a = b
          · subst hab; simp [hj]
          · simp [ha, hab]
      · rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2]
  rw [hdg]
  refine L43 1 (fun _ => i) (fun a b _ => Subsingleton.elim a b) D _ _ 0 hi (core1 _ _ ?_)
  simp only [subL_apply, submatrix_apply, id, σ, Equiv.swap_apply_left]
  exact hB

/-- (z): row `j` vanishes; peel column `j` at cost two -/
theorem stepZ {n : ℕ} (hn : 2 ≤ n) (IH : Pn (n - 1)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = n) (D : ι → ℂ) (B C : Matrix ι ι ℂ) (j : ι) (hj : D j = 0)
    (hrow : ∀ l, B j l = 0 ∧ C j l = 0) : Cov (sp3 (diagonal D) B C) (2 * n - 1) := by
  classical
  set RB := vecMulVec (fun i => B i j) (Pi.single j (1 : ℂ))
  set RC := vecMulVec (fun i => C i j) (Pi.single j (1 : ℂ))
  have h1 := cov_pair (fun i => B i j) (fun i => C i j) (Pi.single j (1 : ℂ)) (Pi.single j 1)
  have hsupp : ∀ M : Matrix ι ι ℂ, (∀ l, M j l = 0) → ∀ a b,
      (M - vecMulVec (fun i => M i j) (Pi.single j (1 : ℂ))) a b ≠ 0 → a ≠ j ∧ b ≠ j := by
    intro M hM a b hab
    simp only [Matrix.sub_apply, vecMulVec_apply, Pi.single_apply] at hab
    constructor
    · rintro rfl; apply hab; simp [hM]
    · rintro rfl; apply hab; simp
  have h2 : Cov (sp3 (diagonal D) (B - RB) (C - RC)) (2 * (n - 1) - 1) := by
    apply cov_compress (fun x => x ≠ j) (fun x => x ≠ j)
    · intro a b hab
      simp only [diagonal_apply] at hab
      split_ifs at hab with h
      · subst h; exact ⟨fun h' => hab (h' ▸ hj), fun h' => hab (h' ▸ hj)⟩
      · exact absurd rfl hab
    · exact hsupp B (fun l => (hrow l).1)
    · exact hsupp C (fun l => (hrow l).2)
    · exact IH _ _ (by rw [card_ne_sub, hι]) (by rw [card_ne_sub, hι]) _ _ _
  refine ((h1.sup h2).mono ?_).mono_r (by omega)
  apply sp3_le
  · exact Submodule.mem_sup_right (mem_sp3_1 _ _ _)
  · have h := Submodule.add_mem_sup
      (Submodule.subset_span (by simp [RB]) : RB ∈ Submodule.span ℂ ({RB, RC} : Set _))
      (mem_sp3_2 (diagonal D) (B - RB) (C - RC))
    simpa using h
  · have h := Submodule.add_mem_sup
      (Submodule.subset_span (by simp [RC]) : RC ∈ Submodule.span ℂ ({RB, RC} : Set _))
      (mem_sp3_3 (diagonal D) (B - RB) (C - RC))
    simpa using h

theorem sp3_swap {ι κ : Type*} (A B C : Matrix ι κ ℂ) : sp3 A B C = sp3 A C B := by
  unfold sp3; congr 1; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

theorem stepB_core {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℂ) (X Y : Matrix ι ι ℂ)
    (p j : ι) (hpj : p ≠ j) (hj : D j = 0) (hX : X j j = 0) (hY : Y j j = 0)
    (h1 : X p j * X j p ≠ 0) (h2 : X p j * Y j p ≠ Y p j * X j p) :
    Cov (sp3 (diagonal D) X Y) (2 * Fintype.card ι - 1) := by
  have hinj : Function.Injective ![p, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [Ne.symm hpj]
  exact L43 2 ![p, j] hinj D X Y 1 (by simpa using hj)
    (core2 _ _ (by simpa using hX) (by simpa using hY) (by simpa using h1) (by simpa using h2))

theorem stepB_pair {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℂ) (B C : Matrix ι ι ℂ)
    (p j : ι) (hpj : p ≠ j) (hj : D j = 0) (hB : B j j = 0) (hC : C j j = 0)
    (hdet : C p j * B j p ≠ B p j * C j p) :
    Cov (sp3 (diagonal D) B C) (2 * Fintype.card ι - 1) := by
  by_cases hc1 : B p j * B j p ≠ 0
  · exact stepB_core D B C p j hpj hj hB hC hc1 (fun h => hdet (by linear_combination -h))
  by_cases hc2 : C p j * C j p ≠ 0
  · rw [sp3_swap]
    exact stepB_core D C B p j hpj hj hC hB hc2 hdet
  push Not at hc1 hc2
  have hmono : sp3 (diagonal D) B C ≤ sp3 (diagonal D) (B + C) C := by
    apply sp3_le (mem_sp3_1 _ _ _) _ (mem_sp3_3 _ _ _)
    have := Submodule.sub_mem _ (mem_sp3_2 (diagonal D) (B + C) C) (mem_sp3_3 (diagonal D) (B + C) C)
    simpa using this
  refine Cov.mono hmono (stepB_core D (B + C) C p j hpj hj (by simp [hB, hC]) hC ?_ ?_)
  · simp only [Matrix.add_apply]
    rcases mul_eq_zero.mp hc1 with h | h <;> rcases mul_eq_zero.mp hc2 with h' | h'
    · rw [h, h'] at hdet; simp at hdet
    · rw [h, h', zero_add, add_zero]
      exact mul_ne_zero (left_ne_zero_of_mul (by rw [h] at hdet; simpa using hdet))
        (right_ne_zero_of_mul (by rw [h] at hdet; simpa using hdet))
    · rw [h, h', add_zero, zero_add]
      have : B p j * C j p ≠ 0 := by rw [h] at hdet; simpa [eq_comm] using hdet
      exact this
    · rw [h, h'] at hdet; simp at hdet
  · simp only [Matrix.add_apply]
    intro h
    apply hdet
    linear_combination -h

theorem conj_apply {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (t : ℂ) (p q : ι)
    (a b : ι) :
    ((1 + t • single p q (1 : ℂ)) * M * (1 - t • single p q (1 : ℂ))) a b
      = M a b + t * (if a = p then M q b else 0) - t * (if b = q then M a p else 0)
        - t * t * (if a = p then (if b = q then M q p else 0) else 0) := by
  have e1 : ∀ (N : Matrix ι ι ℂ) (a b : ι), (single p q (1 : ℂ) * N) a b
      = if a = p then N q b else 0 := by
    intro N a b
    by_cases ha : a = p
    · subst ha; simp [single_mul_apply_same]
    · simp [single_mul_apply_of_ne (1 : ℂ) p q a b ha N, ha]
  have e2 : ∀ (N : Matrix ι ι ℂ) (a b : ι), (N * single p q (1 : ℂ)) a b
      = if b = q then N a p else 0 := by
    intro N a b
    by_cases hb : b = q
    · subst hb; simp [mul_single_apply_same]
    · simp [mul_single_apply_of_ne (1 : ℂ) p q a b hb N, hb]
  have hexp : (1 + t • single p q (1 : ℂ)) * M * (1 - t • single p q (1 : ℂ))
      = M + t • (single p q 1 * M) - t • (M * single p q 1)
        - (t * t) • (single p q 1 * (M * single p q 1)) := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc]
    module
  rw [hexp]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e1, e2]

theorem stepB {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℂ) (hD01 : ∀ i, D i = 0 ∨ D i = 1)
    (B C : Matrix ι ι ℂ) (hZZ : ∀ a b, D a = 0 → D b = 0 → B a b = 0 ∧ C a b = 0) (j : ι)
    (hj : D j = 0) (hind : ∀ c₁ c₂ : ℂ, (∀ i, c₁ * B i j + c₂ * C i j = 0) → c₁ = 0 ∧ c₂ = 0)
    (p : ι) (hp : B j p ≠ 0 ∨ C j p ≠ 0) :
    Cov (sp3 (diagonal D) B C) (2 * Fintype.card ι - 1) := by
  have hDp : D p = 1 := by
    rcases hD01 p with h | h
    · exfalso
      obtain ⟨h1, h2⟩ := hZZ j p hj h
      rcases hp with h3 | h3
      · exact h3 h1
      · exact h3 h2
    · exact h
  have hpj : p ≠ j := by
    intro h; rw [h, hj] at hDp; norm_num at hDp
  set w : ι → ℂ := fun i => B j p * C i j - C j p * B i j with hw
  have hwex : ∃ q, w q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hind (-C j p) (B j p) (fun i => by
      have := hcon i; simp only [hw] at this; linear_combination this)
    rcases hp with h3 | h3
    · exact h3 h2
    · exact h3 (neg_eq_zero.mp h1)
  obtain ⟨t, q, hqp, htq, hwt⟩ : ∃ (t : ℂ) (q : ι), q ≠ p ∧ (t = 0 ∨ (D q = 1 ∧ q ≠ j)) ∧
      w p + t * w q ≠ 0 := by
    by_cases hwp : w p ≠ 0
    · exact ⟨0, j, Ne.symm hpj, Or.inl rfl, by simpa using hwp⟩
    push Not at hwp
    obtain ⟨q, hq⟩ := hwex
    have hqp : q ≠ p := fun h => hq (h ▸ hwp)
    have hDq : D q = 1 := by
      rcases hD01 q with h | h
      · exfalso; apply hq
        simp only [hw, (hZZ q j h hj).1, (hZZ q j h hj).2, mul_zero, sub_zero]
      · exact h
    have hqj : q ≠ j := fun h => by rw [h, hj] at hDq; norm_num at hDq
    exact ⟨1, q, hqp, Or.inr ⟨hDq, hqj⟩, by rw [hwp]; simpa using hq⟩
  set E := single p q (1 : ℂ)
  have hEE : E * E = 0 := single_mul_single_of_ne (1 : ℂ) p q p hqp 1
  set G := 1 + t • E
  set Gi := 1 - t • E
  have hGGi : G * Gi = 1 := by
    simp only [G, Gi, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hEE, smul_zero]
    abel
  have hGiG : Gi * G = 1 := by
    simp only [G, Gi, Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hEE, smul_zero]
    abel
  have hgg : ∀ M : Matrix ι ι ℂ, lrMul Gi G (lrMul G Gi M) = M := by
    intro M
    simp only [lrMul_apply]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul, Matrix.mul_assoc, hGiG,
      Matrix.mul_one]
  refine cov_transfer (lrMul G Gi) (lrMul Gi G) (isR1_lrMul Gi G) (hgg _) (hgg _) (hgg _) ?_
  have hcomm : t • E * diagonal D = diagonal D * (t • E) := by
    ext a b
    simp only [Matrix.smul_apply, smul_eq_mul, E,
      mul_diagonal, diagonal_mul, single_apply]
    rcases htq with h | ⟨h, _⟩
    · simp [h]
    · by_cases hab : p = a ∧ q = b
      · obtain ⟨rfl, rfl⟩ := hab; simp [hDp, h]
      · simp [hab]
  have hGD : G * diagonal D = diagonal D * G := by
    simp only [G, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hcomm]
  have hdg : lrMul G Gi (diagonal D) = diagonal D := by
    rw [lrMul_apply, hGD, Matrix.mul_assoc, hGGi, Matrix.mul_one]
  rw [hdg]
  have hq' : t * (if j = q then (1 : ℂ) else 0) = 0 := by
    rcases htq with h | ⟨_, h⟩
    · simp [h]
    · simp [Ne.symm h]
  have entry : ∀ M : Matrix ι ι ℂ, lrMul G Gi M p j = M p j + t * M q j ∧
      lrMul G Gi M j p = M j p ∧ lrMul G Gi M j j = M j j := by
    intro M
    simp only [lrMul_apply, G, Gi, E, conj_apply]
    refine ⟨?_, ?_, ?_⟩
    · rcases htq with h | ⟨_, h⟩
      · simp [h]
      · simp [Ne.symm h]
    · simp [Ne.symm hpj, Ne.symm hqp]
    · rcases htq with h | ⟨_, h⟩
      · simp [h, Ne.symm hpj]
      · simp [Ne.symm h, Ne.symm hpj]
  obtain ⟨b1, b2, b3⟩ := entry B
  obtain ⟨c1, c2, c3⟩ := entry C
  refine stepB_pair D _ _ p j hpj hj (by rw [b3]; exact (hZZ j j hj hj).1)
    (by rw [c3]; exact (hZZ j j hj hj).2) ?_
  rw [b1, b2, c1, c2]
  intro h
  apply hwt
  simp only [hw]
  linear_combination h

/-- (c): every column and row of the zero block is a rank-one fibre; peel them all -/
theorem stepC {n : ℕ} (IH : ∀ m < n, Pn m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = n) (D : ι → ℂ) (hz : ∃ i, D i = 0) (hnz : ∃ i, D i ≠ 0)
    (B C : Matrix ι ι ℂ) (hZZ : ∀ a b, D a = 0 → D b = 0 → B a b = 0 ∧ C a b = 0)
    (v : ι → ι → ℂ) (cv₁ cv₂ : ι → ℂ)
    (hv : ∀ j, D j = 0 → ∀ i, B i j = cv₁ j * v j i ∧ C i j = cv₂ j * v j i)
    (w : ι → ι → ℂ) (cw₁ cw₂ : ι → ℂ)
    (hw : ∀ i, D i = 0 → ∀ l, B i l = cw₁ i * w i l ∧ C i l = cw₂ i * w i l) :
    Cov (sp3 (diagonal D) B C) (2 * n - 1) := by
  classical
  set Zf := Finset.univ.filter (fun j => D j = 0) with hZf
  let colR : ι → Matrix ι ι ℂ := fun j => vecMulVec (v j) (Pi.single j 1)
  let rowR : ι → Matrix ι ι ℂ := fun i => vecMulVec (Pi.single i 1) (w i)
  set T := Zf.image colR ∪ Zf.image rowR with hT
  have hTc : Cov (Submodule.span ℂ (T : Set (Matrix ι ι ℂ))) (2 * Zf.card) := by
    refine ⟨T, (Finset.card_union_le _ _).trans ?_, ?_, le_rfl⟩
    · have h1 := Finset.card_image_le (s := Zf) (f := colR)
      have h2 := Finset.card_image_le (s := Zf) (f := rowR)
      omega
    · intro M hM
      rcases Finset.mem_union.mp hM with h | h
      · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h; exact ⟨_, _, rfl⟩
      · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h; exact ⟨_, _, rfl⟩
  let mask : Matrix ι ι ℂ → Matrix ι ι ℂ := fun M => Matrix.of fun a b =>
    if D a ≠ 0 ∧ D b ≠ 0 then M a b else 0
  have hdec : ∀ (M : Matrix ι ι ℂ) (c₁ c₂ : ι → ℂ),
      (∀ j, D j = 0 → ∀ i, M i j = c₁ j * v j i) → (∀ i, D i = 0 → ∀ l, M i l = c₂ i * w i l) →
      (∀ a b, D a = 0 → D b = 0 → M a b = 0) →
      M - mask M = ∑ j ∈ Zf, c₁ j • colR j + ∑ i ∈ Zf, c₂ i • rowR i := by
    intro M c₁ c₂ h1 h2 h3
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, colR, rowR, vecMulVec_apply, Pi.single_apply, mask, Matrix.of_apply,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp only [hZf, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases ha : D a = 0 <;> by_cases hb : D b = 0
    · have e1 := h1 b hb a
      have e2 := h2 a ha b
      have e3 := h3 a b ha hb
      simp [ha, hb, h3 a b ha hb]
      linear_combination e1 + e2 - 2 * e3
    · simp [ha, hb, h2 a ha b]
    · simp [ha, hb, h1 b hb a]
    · simp [ha, hb]
  have hmem : ∀ (c₁ c₂ : ι → ℂ), ∑ j ∈ Zf, c₁ j • colR j + ∑ i ∈ Zf, c₂ i • rowR i ∈
      Submodule.span ℂ (T : Set (Matrix ι ι ℂ)) := by
    intro c₁ c₂
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
    · apply Submodule.subset_span
      simp only [hT, Finset.coe_union, Set.mem_union, Finset.mem_coe]
      exact Or.inl (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    · apply Submodule.subset_span
      simp only [hT, Finset.coe_union, Set.mem_union, Finset.mem_coe]
      exact Or.inr (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hBd := hdec B cv₁ cw₁ (fun j hj i => (hv j hj i).1) (fun i hi l => (hw i hi l).1)
    (fun a b ha hb => (hZZ a b ha hb).1)
  have hCd := hdec C cv₂ cw₂ (fun j hj i => (hv j hj i).2) (fun i hi l => (hw i hi l).2)
    (fun a b ha hb => (hZZ a b ha hb).2)
  -- sizes
  have hZc : Fintype.card {x // D x = 0} = Zf.card := by
    rw [Fintype.card_subtype]
  have hNc : Fintype.card {x // D x ≠ 0} = n - Zf.card := by
    rw [← hι, ← hZc]; exact Fintype.card_subtype_compl _
  have hZpos : 1 ≤ Zf.card := by
    obtain ⟨i, hi⟩ := hz
    exact Finset.card_pos.mpr ⟨i, by simp [hZf, hi]⟩
  have hNpos : 1 ≤ Fintype.card {x // D x ≠ 0} := by
    obtain ⟨i, hi⟩ := hnz
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  have hZle : Zf.card ≤ n := by
    rw [← hι]; exact Finset.card_le_univ _
  have h2 : Cov (sp3 (diagonal D) (mask B) (mask C)) (2 * (n - Zf.card) - 1) := by
    apply cov_compress (fun x => D x ≠ 0) (fun x => D x ≠ 0)
    · intro a b hab
      simp only [diagonal_apply] at hab
      split_ifs at hab with h
      · subst h; exact ⟨hab, hab⟩
      · exact absurd rfl hab
    · intro a b hab
      simp only [mask, Matrix.of_apply] at hab
      split_ifs at hab with h
      · exact h
      · exact absurd rfl hab
    · intro a b hab
      simp only [mask, Matrix.of_apply] at hab
      split_ifs at hab with h
      · exact h
      · exact absurd rfl hab
    · exact IH _ (by omega) _ _ hNc hNc _ _ _
  refine ((hTc.sup h2).mono ?_).mono_r (by omega)
  apply sp3_le
  · exact Submodule.mem_sup_right (mem_sp3_1 _ _ _)
  · have h := Submodule.add_mem_sup (hmem cv₁ cw₁) (mem_sp3_2 (diagonal D) (mask B) (mask C))
    rw [← hBd] at h; simpa using h
  · have h := Submodule.add_mem_sup (hmem cv₂ cw₂) (mem_sp3_3 (diagonal D) (mask B) (mask C))
    rw [← hCd] at h; simpa using h

theorem dep_vec {ι : Type} (x y : ι → ℂ)
    (h : ¬ ∀ c₁ c₂ : ℂ, (∀ i, c₁ * x i + c₂ * y i = 0) → c₁ = 0 ∧ c₂ = 0) :
    ∃ (v : ι → ℂ) (a b : ℂ), ∀ i, x i = a * v i ∧ y i = b * v i := by
  push Not at h
  obtain ⟨c₁, c₂, hc, hne⟩ := h
  by_cases hc2 : c₂ = 0
  · have hc1 : c₁ ≠ 0 := fun h => hne h hc2
    refine ⟨y, 0, 1, fun i => ⟨?_, by ring⟩⟩
    have := hc i
    rw [hc2, zero_mul, add_zero] at this
    rw [zero_mul]
    exact (mul_eq_zero.mp this).resolve_left hc1
  · refine ⟨x, 1, -(c₁ / c₂), fun i => ⟨by ring, ?_⟩⟩
    have := hc i
    field_simp
    linear_combination this

theorem trL_diag {ι : Type} [DecidableEq ι] (D : ι → ℂ) : trL (diagonal D) = diagonal D := by
  rw [trL_apply, diagonal_transpose]

theorem cov_transpose {ι : Type} [Fintype ι] [DecidableEq ι] {D : ι → ℂ} {B C : Matrix ι ι ℂ}
    {r : ℕ} (h : Cov (sp3 (diagonal D) Bᵀ Cᵀ) r) : Cov (sp3 (diagonal D) B C) r := by
  refine cov_transfer trL trL isR1_trL (by simp [trL_apply]) (by simp [trL_apply])
    (by simp [trL_apply]) ?_
  rw [trL_diag]; exact h

theorem core_step {n : ℕ} (IH : ∀ m < n, Pn m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = n) (D : ι → ℂ) (hD01 : ∀ i, D i = 0 ∨ D i = 1) (hz : ∃ i, D i = 0)
    (hnz : ∃ i, D i = 1) (B C : Matrix ι ι ℂ) : Cov (sp3 (diagonal D) B C) (2 * n - 1) := by
  obtain ⟨i₀, hi₀⟩ := hz
  obtain ⟨i₁, hi₁⟩ := hnz
  have hn2 : 2 ≤ n := by
    rw [← hι]
    have : 1 < Fintype.card ι := Fintype.one_lt_card_iff.mpr ⟨i₀, i₁, fun h => by
      rw [h, hi₁] at hi₀; norm_num at hi₀⟩
    omega
  have hnz' : ∃ i, D i ≠ 0 := ⟨i₁, by rw [hi₁]; norm_num⟩
  by_cases ha : ∃ i j, D i = 0 ∧ D j = 0 ∧ (B i j ≠ 0 ∨ C i j ≠ 0)
  · obtain ⟨i, j, hi, hj, hB | hC⟩ := ha
    · rw [← hι]; exact stepA D B C i j hi hj hB
    · rw [← hι, sp3_swap]; exact stepA D C B i j hi hj hC
  have hZZ : ∀ a b, D a = 0 → D b = 0 → B a b = 0 ∧ C a b = 0 := by
    intro a b hA hB'
    by_contra hc
    apply ha
    refine ⟨a, b, hA, hB', ?_⟩
    by_contra hc'
    push Not at hc'
    exact hc hc'
  have IH1 : Pn (n - 1) := IH _ (by omega)
  by_cases hzr : ∃ j, D j = 0 ∧ ∀ l, B j l = 0 ∧ C j l = 0
  · obtain ⟨j, hj, hrow⟩ := hzr
    exact stepZ hn2 IH1 hι D B C j hj hrow
  by_cases hzc : ∃ j, D j = 0 ∧ ∀ l, B l j = 0 ∧ C l j = 0
  · obtain ⟨j, hj, hcol⟩ := hzc
    exact cov_transpose (stepZ hn2 IH1 hι D Bᵀ Cᵀ j hj (fun l => hcol l))
  by_cases hbc : ∃ j, D j = 0 ∧
      ∀ c₁ c₂ : ℂ, (∀ i, c₁ * B i j + c₂ * C i j = 0) → c₁ = 0 ∧ c₂ = 0
  · obtain ⟨j, hj, hind⟩ := hbc
    have : ∃ l, B j l ≠ 0 ∨ C j l ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hzr ⟨j, hj, hcon⟩
    obtain ⟨l, hl⟩ := this
    rw [← hι]
    exact stepB D hD01 B C hZZ j hj hind l hl
  by_cases hbr : ∃ j, D j = 0 ∧
      ∀ c₁ c₂ : ℂ, (∀ i, c₁ * B j i + c₂ * C j i = 0) → c₁ = 0 ∧ c₂ = 0
  · obtain ⟨j, hj, hind⟩ := hbr
    have : ∃ l, B l j ≠ 0 ∨ C l j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hzc ⟨j, hj, hcon⟩
    obtain ⟨l, hl⟩ := this
    rw [← hι]
    refine cov_transpose (stepB D hD01 Bᵀ Cᵀ (fun a b ha hb => ?_) j hj (fun c₁ c₂ h => hind c₁ c₂ h) l hl)
    exact ⟨(hZZ b a hb ha).1, (hZZ b a hb ha).2⟩
  have hcolv : ∀ j, ∃ (v : ι → ℂ) (a b : ℂ), D j = 0 → ∀ i, B i j = a * v i ∧ C i j = b * v i := by
    intro j
    by_cases hj : D j = 0
    · obtain ⟨v, a, b, h⟩ := dep_vec (fun i => B i j) (fun i => C i j) (fun h => hbc ⟨j, hj, h⟩)
      exact ⟨v, a, b, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h hj⟩
  have hrowv : ∀ i, ∃ (w : ι → ℂ) (a b : ℂ), D i = 0 → ∀ l, B i l = a * w l ∧ C i l = b * w l := by
    intro i
    by_cases hi : D i = 0
    · obtain ⟨w, a, b, h⟩ := dep_vec (fun l => B i l) (fun l => C i l) (fun h => hbr ⟨i, hi, h⟩)
      exact ⟨w, a, b, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h hi⟩
  choose v cv₁ cv₂ hv using hcolv
  choose w cw₁ cw₂ hw using hrowv
  exact stepC IH hι D ⟨i₀, hi₀⟩ hnz' B C hZZ v cv₁ cv₂ hv w cw₁ cw₂ hw

theorem sing_comb {ι : Type} [Fintype ι] [DecidableEq ι] (M₁ M₂ : Matrix ι ι ℂ)
    (hn : 0 < Fintype.card ι) :
    ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ (c₁ • M₁ + c₂ • M₂).det = 0 := by
  by_cases h : M₂.det = 0
  · exact ⟨0, 1, Or.inr one_ne_zero, by simpa using h⟩
  have : Nonempty ι := Fintype.card_pos_iff.mp hn
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (toLin' (M₂⁻¹ * M₁))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨1, -μ, Or.inl one_ne_zero, ?_⟩
  apply exists_mulVec_eq_zero_iff.mp
  refine ⟨v, hv.2, ?_⟩
  have h1 := hv.apply_eq_smul
  rw [toLin'_apply, ← mulVec_mulVec] at h1
  have h2 : M₁ *ᵥ v = μ • (M₂ *ᵥ v) := by
    have := congrArg (fun x => M₂ *ᵥ x) h1
    simp only [mulVec_mulVec, mulVec_smul] at this
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h), Matrix.one_mul] at this
    exact this
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_smul, h2, neg_smul, add_neg_cancel]

theorem normal_form {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    ∃ P Q : Matrix ι ι ℂ, IsUnit P.det ∧ IsUnit Q.det ∧ ∃ D : ι → ℂ, (∀ i, D i = 0 ∨ D i = 1) ∧
      P * A * Q = diagonal D := by
  obtain ⟨L, L', D₀, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal A
  let s : ι → ℂ := fun i => if D₀ i = 0 then 1 else (D₀ i)⁻¹
  have hunit : ∀ L : List (TransvectionStruct ι ℂ), IsUnit (L.map TransvectionStruct.toMatrix).prod := by
    intro L
    apply List.prod_isUnit
    intro m hm
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hm
    exact (isUnit_iff_isUnit_det _).mpr (by rw [TransvectionStruct.det]; exact isUnit_one)
  refine ⟨diagonal s * (L.map TransvectionStruct.toMatrix).prod, (L'.map TransvectionStruct.toMatrix).prod,
    ?_, (isUnit_iff_isUnit_det _).mp (hunit L'), fun i => s i * D₀ i, ?_, ?_⟩
  · rw [det_mul]
    refine IsUnit.mul ?_ ((isUnit_iff_isUnit_det _).mp (hunit L))
    rw [det_diagonal]
    refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    simp only [s]
    split_ifs with h0
    · exact one_ne_zero
    · exact inv_ne_zero h0
  · intro i
    simp only [s]
    split_ifs with h0
    · left; simp [h0]
    · right; exact inv_mul_cancel₀ h0
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ A, h, diagonal_mul_diagonal]

theorem cov_single {ι κ : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι κ ℂ) :
    Cov (Submodule.span ℂ {M}) (Fintype.card ι) := by
  refine (cov_family (fun i => Pi.single i (1 : ℂ)) (fun i => M i)).mono ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  have : M = ∑ i, vecMulVec (Pi.single i (1 : ℂ)) (M i) := by
    ext a b
    simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply]
  have hsum : ∑ i, vecMulVec (Pi.single i (1 : ℂ)) (M i) ∈ Submodule.span ℂ
      (Set.range fun i => vecMulVec (Pi.single i (1 : ℂ)) (M i)) :=
    Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, rfl⟩
  rw [← this] at hsum
  exact hsum

theorem pencil_span {ι κ : Type} (M₁ M₂ : Matrix ι κ ℂ) (c₁ c₂ : ℂ) (hc : c₁ ≠ 0 ∨ c₂ ≠ 0) :
    ∃ M, M₁ ∈ Submodule.span ℂ ({c₁ • M₁ + c₂ • M₂, M} : Set (Matrix ι κ ℂ)) ∧
      M₂ ∈ Submodule.span ℂ ({c₁ • M₁ + c₂ • M₂, M} : Set (Matrix ι κ ℂ)) := by
  set S := Submodule.span ℂ ({c₁ • M₁ + c₂ • M₂, M₂} : Set (Matrix ι κ ℂ))
  by_cases h1 : c₁ ≠ 0
  · refine ⟨M₂, ?_, Submodule.subset_span (by simp)⟩
    have hA : c₁ • M₁ + c₂ • M₂ ∈ S := Submodule.subset_span (by simp)
    have hB : M₂ ∈ S := Submodule.subset_span (by simp)
    have := S.smul_mem c₁⁻¹ (S.sub_mem hA (S.smul_mem c₂ hB))
    rwa [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ h1, one_smul] at this
  · push Not at h1
    have h2 : c₂ ≠ 0 := hc.resolve_left (by simpa using h1)
    refine ⟨M₁, Submodule.subset_span (by simp), ?_⟩
    have hA : c₁ • M₁ + c₂ • M₂ ∈ Submodule.span ℂ ({c₁ • M₁ + c₂ • M₂, M₁} : Set _) :=
      Submodule.subset_span (by simp)
    convert Submodule.smul_mem _ c₂⁻¹ hA using 1
    rw [h1, zero_smul, zero_add, smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem span_pair_le {ι κ : Type} {X Y : Matrix ι κ ℂ} {S : Submodule ℂ (Matrix ι κ ℂ)}
    (hX : X ∈ S) (hY : Y ∈ S) : Submodule.span ℂ ({X, Y} : Set (Matrix ι κ ℂ)) ≤ S := by
  rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hX, hY⟩

theorem reduce3 {ι : Type} [Fintype ι] [DecidableEq ι] (A₁ A₂ A₃ : Matrix ι ι ℂ)
    (hn : 0 < Fintype.card ι) :
    (∃ N : Matrix ι ι ℂ, sp3 A₁ A₂ A₃ ≤ Submodule.span ℂ {N}) ∨
      ∃ A B C : Matrix ι ι ℂ, A.det = 0 ∧ A ≠ 0 ∧ sp3 A₁ A₂ A₃ ≤ sp3 A B C := by
  obtain ⟨c₁, c₂, hc, hdet⟩ := sing_comb A₁ A₂ hn
  obtain ⟨M, h1, h2⟩ := pencil_span A₁ A₂ c₁ c₂ hc
  by_cases hA : c₁ • A₁ + c₂ • A₂ = 0
  · rw [hA] at h1 h2
    have hsM : Submodule.span ℂ ({0, M} : Set (Matrix ι ι ℂ)) ≤ Submodule.span ℂ {M} :=
      span_pair_le (Submodule.zero_mem _) (Submodule.subset_span (by simp))
    obtain ⟨d₁, d₂, hd, hdet'⟩ := sing_comb A₃ M hn
    obtain ⟨M', g1, g2⟩ := pencil_span A₃ M d₁ d₂ hd
    by_cases hA' : d₁ • A₃ + d₂ • M = 0
    · left
      rw [hA'] at g1 g2
      have hs' : Submodule.span ℂ ({0, M'} : Set (Matrix ι ι ℂ)) ≤ Submodule.span ℂ {M'} :=
        span_pair_le (Submodule.zero_mem _) (Submodule.subset_span (by simp))
      have hM : M ∈ Submodule.span ℂ {M'} := hs' g2
      have hMM : Submodule.span ℂ {M} ≤ Submodule.span ℂ {M'} := by
        rw [Submodule.span_le, Set.singleton_subset_iff]; exact hM
      exact ⟨M', sp3_le (hMM (hsM h1)) (hMM (hsM h2)) (hs' g1)⟩
    · right
      refine ⟨d₁ • A₃ + d₂ • M, M', 0, hdet', hA', ?_⟩
      have hP : Submodule.span ℂ ({d₁ • A₃ + d₂ • M, M'} : Set (Matrix ι ι ℂ)) ≤
          sp3 (d₁ • A₃ + d₂ • M) M' 0 := span_pair_le (mem_sp3_1 _ _ _) (mem_sp3_2 _ _ _)
      have hMM : Submodule.span ℂ {M} ≤ sp3 (d₁ • A₃ + d₂ • M) M' 0 := by
        rw [Submodule.span_le, Set.singleton_subset_iff]; exact hP g2
      exact sp3_le (hMM (hsM h1)) (hMM (hsM h2)) (hP g1)
  · right
    refine ⟨c₁ • A₁ + c₂ • A₂, M, A₃, hdet, hA, ?_⟩
    have hP : Submodule.span ℂ ({c₁ • A₁ + c₂ • A₂, M} : Set (Matrix ι ι ℂ)) ≤
        sp3 (c₁ • A₁ + c₂ • A₂) M A₃ := span_pair_le (mem_sp3_1 _ _ _) (mem_sp3_2 _ _ _)
    exact sp3_le (hP h1) (hP h2) (mem_sp3_3 _ _ _)

theorem sq_main {n : ℕ} (IH : ∀ m < n, Pn m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = n) (A₁ A₂ A₃ : Matrix ι ι ℂ) : Cov (sp3 A₁ A₂ A₃) (2 * n - 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp (hι.trans h0)
    refine ⟨∅, by simp, by simp, ?_⟩
    intro x _
    have : x = 0 := by ext i; exact (IsEmpty.false i).elim
    rw [this]; exact Submodule.zero_mem _
  rcases reduce3 A₁ A₂ A₃ (by omega) with ⟨N, hN⟩ | ⟨A, B, C, hdet, hA0, hS⟩
  · exact ((cov_single N).mono hN).mono_r (by omega)
  refine Cov.mono hS ?_
  obtain ⟨P, Q, hP, hQ, D, hD01, hPAQ⟩ := normal_form A
  have hgg : ∀ M : Matrix ι ι ℂ, lrMul P⁻¹ Q⁻¹ (lrMul P Q M) = M := by
    intro M
    simp only [lrMul_apply]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hP, Matrix.one_mul,
      Matrix.mul_assoc, mul_nonsing_inv _ hQ, Matrix.mul_one]
  refine cov_transfer (lrMul P Q) (lrMul P⁻¹ Q⁻¹) (isR1_lrMul _ _) (hgg _) (hgg _) (hgg _) ?_
  rw [lrMul_apply P Q A, hPAQ]
  have hz : ∃ i, D i = 0 := by
    have : (diagonal D).det = 0 := by rw [← hPAQ, det_mul, det_mul, hdet]; ring
    rw [det_diagonal, Finset.prod_eq_zero_iff] at this
    obtain ⟨i, -, hi⟩ := this
    exact ⟨i, hi⟩
  have hnz : ∃ i, D i = 1 := by
    by_contra hcon
    push Not at hcon
    have hD0 : diagonal D = 0 := by
      ext i j
      rcases hD01 i with h | h
      · simp [diagonal_apply, h]
      · exact absurd h (hcon i)
    apply hA0
    rw [← hgg A, lrMul_apply P Q A, hPAQ, hD0, lrMul_apply, Matrix.mul_zero, Matrix.zero_mul]
  exact core_step IH hι D hD01 hz hnz _ _

theorem main (n : ℕ) : Pn n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro ι κ _ _ _ _ hι hκ A B C
    have e : κ ≃ ι := Fintype.equivOfCardEq (by rw [hκ, hι])
    have hgg : ∀ M : Matrix ι κ ℂ, subL id e (subL id e.symm M) = M := by
      intro M; ext i j; simp [subL_apply]
    exact cov_transfer (subL id e.symm) (subL id e) (isR1_subL id e) (hgg _) (hgg _) (hgg _)
      (sq_main IH hι _ _ _)

/- ### From holors to slices (adapted from the `Bridge` section of
`proofs/Arxiv.0805.3777.isMaxRank_three_three_five_bounds.lean`) -/

section Bridge

variable {n : ℕ}

/-- The index `(i, j, k)` of an `n × n × 3` holor. -/
def ix (i j : Fin n) (k : Fin 3) : HolorIndex [n, n, 3] :=
  ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩

theorem ix_surjective (t : HolorIndex [n, n, 3]) : ∃ i j k, t = ix i j k := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha h =>
    cases h with
    | cons hb h =>
      cases h with
      | cons hc h =>
        cases h
        exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl⟩

/-- entry `(i, j, k)` -/
def ev (T : Holor ℂ [n, n, 3]) (i j : Fin n) (k : Fin 3) : ℂ := T (ix i j k)

theorem holor_ext {T T' : Holor ℂ [n, n, 3]} (h : ∀ i j k, ev T i j k = ev T' i j k) :
    T = T' := by
  funext t
  obtain ⟨i, j, k, rfl⟩ := ix_surjective t
  exact h i j k

theorem ev_add (T T' : Holor ℂ [n, n, 3]) (i j : Fin n) (k : Fin 3) :
    ev (T + T') i j k = ev T i j k + ev T' i j k := rfl

theorem ev_sum {β : Type*} (s : Finset β) (f : β → Holor ℂ [n, n, 3]) (i j : Fin n) (k : Fin 3) :
    ev (∑ l ∈ s, f l) i j k = ∑ l ∈ s, ev (f l) i j k := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ih]

/-- the `k`-th slice -/
def slice (T : Holor ℂ [n, n, 3]) (k : Fin 3) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ev T i j k

theorem headI_lt {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : t.1.headI < d := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha _ => exact ha

/-- The first coordinate of a holor index. -/
def idxHead {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : Fin d :=
  ⟨t.1.headI, headI_lt t⟩

/-- A vector as a one-dimensional holor. -/
def vec {m : ℕ} (u : Fin m → ℂ) : Holor ℂ [m] := fun t => u (idxHead t)

/-- The scalar holor `1`. -/
def one0 : Holor ℂ [] := fun _ => 1

/-- The rank-one holor `u ⊗ v ⊗ w`. -/
def r1 (u v : Fin n → ℂ) (w : Fin 3 → ℂ) : Holor ℂ [n, n, 3] :=
  Holor.mul (vec u) (Holor.mul (vec v) (Holor.mul (vec w) one0))

theorem ev_r1 (u v : Fin n → ℂ) (w : Fin 3 → ℂ) (i j : Fin n) (k : Fin 3) :
    ev (r1 u v w) i j k = u i * v j * w k := by
  show u i * (v j * (w k * 1)) = _
  ring

theorem cprankMax1_r1 (u v : Fin n → ℂ) (w : Fin 3 → ℂ) : Holor.CPRankMax1 (r1 u v w) :=
  .cons _ _ (.cons _ _ (.cons _ _ (.nil _)))

theorem cprank_le_of_cprankMax {ds : List ℕ} {x : Holor ℂ ds} {m : ℕ}
    (h : Holor.CPRankMax m x) : x.cprank ≤ m :=
  @Nat.find_min' (fun m => Holor.CPRankMax m x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩ m h

theorem cprank_le_of_cov (T : Holor ℂ [n, n, 3]) (r : ℕ)
    (h : Cov (sp3 (slice T 0) (slice T 1) (slice T 2)) r) : T.cprank ≤ r := by
  classical
  obtain ⟨s, hs, hr1, hS⟩ := h
  have hk : ∀ k : Fin 3, slice T k ∈ Submodule.span ℂ (s : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    intro k
    fin_cases k
    · exact hS (mem_sp3_1 _ _ _)
    · exact hS (mem_sp3_2 _ _ _)
    · exact hS (mem_sp3_3 _ _ _)
  choose c hc using fun k => Submodule.mem_span_finset.mp (hk k)
  have hab : ∀ M : s, ∃ (a b : Fin n → ℂ), M.1 = vecMulVec a b := fun M => hr1 M.1 M.2
  choose a b hab using hab
  have hT : T = ∑ M : s, r1 (a M) (b M) (fun k => c k M.1) := by
    refine holor_ext fun i j k => ?_
    rw [ev_sum]
    have h1 : ev T i j k = slice T k i j := rfl
    rw [h1, ← (hc k).2, Matrix.sum_apply, ← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [ev_r1, Matrix.smul_apply, hab M, vecMulVec_apply, smul_eq_mul]
    ring
  have hr := Holor.cprankMax_sum (n := 1) Finset.univ
    (fun M : s => r1 (a M) (b M) (fun k => c k M.1))
    fun M _ => Holor.cprankMax_1 (cprankMax1_r1 _ _ _)
  rw [Finset.card_univ, Fintype.card_coe, mul_one, ← hT] at hr
  exact (cprank_le_of_cprankMax hr).trans hs

end Bridge

end CP3

theorem MaxCube.LowSlice.certified_three : type_of% @Arxiv.«0805.3777».cprank_le_of_three_slices := by
  intro n _ T
  exact CP3.cprank_le_of_cov T _ (CP3.main n (Fin n) (Fin n) (by simp) (by simp) _ _ _)

namespace MaxCube

/-- A matrix of rank at most two factors through a two-dimensional coordinate space.
Zero terms cover matrices of smaller rank. -/
private lemma rank_two_coordinates (M : Matrix (Fin 4) (Fin 4) ℂ) (hr : M.rank ≤ 2) :
    ∃ y z : Fin 2 → Fin 4 → ℂ, ∀ i j, M i j = ∑ t,y t i*z t j := by
  classical
  let V := LinearMap.range M.mulVecLin
  let b : Module.Basis (Fin M.rank) ℂ V := Module.finBasis ℂ V
  let c (j : Fin 4) : V := ⟨M.col j,Pi.single j 1,Matrix.mulVec_single_one M j⟩
  let u (t : Fin M.rank) (i : Fin 4) := ((b t : V) : Fin 4 → ℂ) i
  let v (t : Fin M.rank) (j : Fin 4) := b.repr (c j) t
  have hm (i j : Fin 4) : M i j=∑ t,u t i*v t j := by
    have hh := congrArg (fun w : V => (w : Fin 4 → ℂ) i) (b.sum_repr (c j))
    change ((∑ t, b.repr (c j) t • b t : V) : Fin 4 → ℂ) i=M i j at hh
    simpa only [u,v,Submodule.coe_sum,Submodule.coe_smul_of_tower,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using hh.symm
  let e : Fin M.rank ⊕ Fin (2-M.rank) ≃ Fin 2 := Fintype.equivOfCardEq (by simp; omega)
  refine ⟨fun t => (e.symm t).elim u 0,fun t => (e.symm t).elim v 0,?_⟩
  intro i j
  let w (t : Fin M.rank ⊕ Fin (2-M.rank)) := (t.elim u 0) i*(t.elim v 0) j
  change M i j=∑ t : Fin 2,w (e.symm t)
  rw [e.symm.sum_comp,Fintype.sum_sum_type]
  simpa [w] using hm i j

/-- If a nontrivial combination of four slices has matrix rank at most two, use
seven rank-one matrices for three of the original slices and two for that combination. -/
lemma nine_of_low_contraction_of_three
    (three : ∀ U : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ, Decomp 3 4 4 7 U)
    (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (p : Fin 4 → ℂ) (hp : p ≠ 0)
    (hlow : (Matrix.of (fun j k => ∑ i,p i*T i j k)).rank ≤ 2) : Decomp 4 4 4 9 T := by
  classical
  obtain ⟨l,hl⟩ : ∃ l,p l ≠ 0 := by
    by_contra! hz
    exact hp (funext hz)
  let B : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of (fun j k => ∑ i,p i*T i j k)
  obtain ⟨u,y,z,hu⟩ := three (fun t : Fin 3 => T (l.succAbove t))
  obtain ⟨y₂,z₂,hh⟩ := rank_two_coordinates B hlow
  let Y : Fin 7 ⊕ Fin 2 → Fin 4 → ℂ := Sum.elim y y₂
  let Z : Fin 7 ⊕ Fin 2 → Fin 4 → ℂ := Sum.elim z z₂
  let F (t : Fin 7 ⊕ Fin 2) : Matrix (Fin 4) (Fin 4) ℂ := fun j k => Y t j*Z t k
  let W := Submodule.span ℂ (Set.range F)
  have mem (t : Fin 7 ⊕ Fin 2) : F t ∈ W := Submodule.subset_span ⟨t,rfl⟩
  have hB : B ∈ W := by
    have eq : B = ∑ t : Fin 2,F (.inr t) := by
      ext j k
      rw [Matrix.sum_apply]
      exact hh j k
    rw [eq]
    exact W.sum_mem fun t _ => mem (.inr t)
  have other (t : Fin 3) : T (l.succAbove t) ∈ W := by
    have eq : T (l.succAbove t)=∑ s : Fin 7,u s t • F (.inl s) := by
      ext j k
      simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
      exact hu t j k
    rw [eq]
    exact W.sum_mem fun s _ => W.smul_mem _ (mem (.inl s))
  have eq : B = p l • T l+∑ t : Fin 3,p (l.succAbove t) • T (l.succAbove t) := by
    have hs : B=∑ i,p i • T i := by ext j k; simp [B,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    exact hs.trans (Fin.sum_univ_succAbove (fun i => p i • T i) l)
  have hlT : T l ∈ W := by
    have hsum : (∑ t : Fin 3,p (l.succAbove t) • T (l.succAbove t)) ∈ W :=
      W.sum_mem fun t _ => W.smul_mem _ (other t)
    have hm : p l • T l ∈ W := by simpa only [eq,add_sub_cancel_right] using W.sub_mem hB hsum
    simpa only [smul_smul,inv_mul_cancel₀ hl,one_smul] using W.smul_mem (p l)⁻¹ hm
  have allmem (i : Fin 4) : T i ∈ W := by
    by_cases he : i=l
    · exact he ▸ hlT
    · obtain ⟨t,rfl⟩ := Fin.exists_succAbove_eq he
      exact other t
  have coeff (i : Fin 4) : ∃ v : Fin 7 ⊕ Fin 2 → ℂ, ∑ t,v t • F t=T i :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (allmem i)
  choose v hv using coeff
  let e : Fin 7 ⊕ Fin 2 ≃ Fin 9 := finSumFinEquiv
  refine ⟨fun t i => v i (e.symm t),fun t => Y (e.symm t),fun t => Z (e.symm t),?_⟩
  intro i j k
  let summand (t : Fin 7 ⊕ Fin 2) := v i t*(Y t j*Z t k)
  change T i j k=∑ t : Fin 9,summand (e.symm t)
  rw [e.symm.sum_comp]
  have hc := (congrArg (fun a : Matrix (Fin 4) (Fin 4) ℂ => a j k) (hv i)).symm
  change T i j k = (∑ t,v i t • F t) j k at hc
  simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] using hc

end MaxCube

namespace MaxCube

/-- The certified complex three-slice bound applied after cycling the coordinates. -/
lemma three_slices_seven (T : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ) : Decomp 3 4 4 7 T := by
  let S (i j : Fin 4) (k : Fin 3) := T k i j
  have hl : (coordinateHolor S).cprank ≤ 7 := @LowSlice.certified_three 4 (by decide) (coordinateHolor S)
  obtain ⟨x,y,z,h⟩ := (cprank_le_iff_decomp S 7).mp hl
  refine ⟨z,x,y,?_⟩
  intro k i j
  exact (h i j k).trans (Finset.sum_congr rfl fun t _ => by ring)

/-- Every nonzero low-rank slice direction yields a tensor rank bound of nine. -/
theorem nine_of_low_contraction (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (p : Fin 4 → ℂ)
    (hp : p ≠ 0) (hlow : (Matrix.of (fun j k => ∑ i,p i*T i j k)).rank ≤ 2) : Decomp 4 4 4 9 T :=
  nine_of_low_contraction_of_three three_slices_seven T p hp hlow

lemma cprank_le_nine_of_low_contraction (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (p : Fin 4 → ℂ)
    (hp : p ≠ 0) (hlow : (Matrix.of (fun j k => ∑ i,p i*T i j k)).rank ≤ 2) :
    (coordinateHolor T).cprank ≤ 9 :=
  (cprank_le_iff_decomp T 9).mpr (nine_of_low_contraction T p hp hlow)

end MaxCube

namespace MaxCube

/-- A low-rank contraction can be separated off. In its absence the first
two coordinate slices form a pencil of rank at least three at every point. -/
theorem split_four_pencil (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (low : ∀ p : Fin 4 → ℂ, p ≠ 0 → (UpperNine.slice T p).rank ≤ 2 → Decomp 4 4 4 9 T)
    (high : 3 ≤ (T 0).rank → (∀ α : ℂ, 3 ≤ (α • T 0 - T 1).rank) → Decomp 4 4 4 9 T) :
    Decomp 4 4 4 9 T := by
  classical
  by_cases hit : ∃ p : Fin 4 → ℂ, p ≠ 0 ∧ (UpperNine.slice T p).rank ≤ 2
  · obtain ⟨p,hp,hr⟩ := hit
    exact low p hp hr
  · have large (p : Fin 4 → ℂ) (hp : p ≠ 0) : 3 ≤ (UpperNine.slice T p).rank := by
      by_contra! small
      exact hit ⟨p,hp,by omega⟩
    apply high
    · let p : Fin 4 → ℂ := ![1,0,0,0]
      have hp : p ≠ 0 := by
        intro h
        have eq := congrFun h 0
        norm_num [p] at eq
      have eq : UpperNine.slice T p = T 0 := by
        ext i j
        simp [UpperNine.slice, p, Fin.sum_univ_four]
      simpa only [eq] using large p hp
    · intro α
      let p : Fin 4 → ℂ := ![α,-1,0,0]
      have hp : p ≠ 0 := by
        intro h
        have eq := congrFun h 1
        norm_num [p] at eq
      have eq : UpperNine.slice T p = α • T 0 - T 1 := by
        ext i j
        simp [UpperNine.slice, p, Fin.sum_univ_four, Matrix.smul_apply, sub_eq_add_neg]
      simpa only [eq] using large p hp

end MaxCube

namespace MaxCube

open Arxiv.«0805.3777»

/-- Every complex four-cube has a decomposition into at most nine pure tensors. -/
theorem four_cube_decomposition (T : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Decomp 4 4 4 9 T :=
  split_four_pencil T (fun p hp h => nine_of_low_contraction T p hp h) (nine_of_minrank_pencil T)

theorem four_cube_upper (T : Holor ℂ [4,4,4]) : T.cprank ≤ 9 := by
  have bound := (cprank_le_iff_decomp (readCoordinates T) 9).mpr (four_cube_decomposition (readCoordinates T))
  rwa [coordinateHolor_readCoordinates] at bound

/-- The maximum ordinary CP rank of a complex four-cube is eight or nine. -/
theorem four_cube_maximum_bounds {R : ℕ} (maximum : IsMaxRank [4,4,4] R) : 8 ≤ R ∧ R ≤ 9 := by
  obtain ⟨T,hT⟩ := maximum.1
  exact ⟨max_four_cube_lower maximum, hT ▸ four_cube_upper T⟩

theorem four_cube_maximum_eight_or_nine :
    ∃ R : ℕ, IsMaxRank [4,4,4] R ∧ (R = 8 ∨ R = 9) := by
  obtain ⟨R,hR⟩ := exists_max_rank [4,4,4]
  obtain ⟨lo,hi⟩ := four_cube_maximum_bounds hR
  exact ⟨R,hR,by omega⟩

end MaxCube

namespace MaxCube.OddLow.Source

/-
Assembled proof of Arxiv.0805.3777.cprank_le_of_square_slices from upstream reduction R1 and step H2.
-/


-- Reduction Arxiv.0805.3777.cprank_le_of_square_slices.R1 of Generic and maximal rank of 3-tensors — cprank le of square slices
-- Credit: @ivillar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The bound: every complex tensor with m slices of size n x n has rank at most (m + 1) n / 2.
--
-- H1 and H2 are one statement about a pair (A, B) of n x n matrices, split by whether the pencil
-- is regular (some combination s A + t B is invertible, H1) or singular (H2): in suitable bases
-- (P, Q) the pair is simultaneously diagonal up to a tensor of rank at most n / 2, that is
--   A = P diag(a) Q + sum_j alpha_j u_j v_j^T,   B = P diag(b) Q + sum_j beta_j u_j v_j^T,
-- with n / 2 rank-one matrices u_j v_j^T. This refines the bound n + n / 2 for the rank of a
-- pencil of square matrices (Ja'Ja'): n of the rank-one matrices can be taken of the form
-- (P e_i)(e_i^T Q).
--
-- What main proves from them.
-- * The perturbation lemma (pert): for any n x n matrices U, V there are diagonal d1, d2 such
--   that the pencil (U + d1, V + d2) has n distinct eigenvalues, hence lies in the span of n
--   rank-one matrices. Conjugating by (P, Q), the span of the n matrices (P e_i)(e_i^T Q) and of
--   n further rank-one matrices contains any given pair (pair_pert).
-- * Odd m = 2k + 1: write the first slice as P diag(D) Q with P, Q products of transvections; it
--   lies in the span of the (P e_i)(e_i^T Q). The other 2k slices are taken in pairs, each pair
--   costing n more rank-one matrices. Total n + k n = (m + 1) n / 2. No hypothesis is used.
-- * Even m = 2k + 2: apply H1 or H2 to the first two slices; they lie in the span of the
--   (P e_i)(e_i^T Q) and of n / 2 more rank-one matrices. The other 2k slices are taken in
--   pairs as before. Total n + n / 2 + k n = (m + 1) n / 2 (rounded down).
--
-- Reuse and credit: the lemmas sep_iff, fel, det_add_corner, exists_eval_ne_zero, osl, osl_all,
-- outer_sum, nice_of_good and diag_sum are taken from the merged proof
-- proofs/Arxiv.0805.3777.cprank_le_of_three_slices.lean (PR #3512, same owner), with its two
-- definitions penPoly and Good written out, since a reduction file declares no definitions.
-- The passage from rank-one sums to CP rank follows the Bridge section of
-- proofs/Arxiv.0805.3777.isMaxRank_three_three_five_bounds.lean (PR #2438, DomTheDeveloper; a
-- port of Kenta Kitamura's https://github.com/KitaKen1/mrank-3-3-5-lean, Apache License 2.0),
-- again without definitions.

namespace OMA.R1

open Matrix Polynomial

def H1 : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), (∃ s t : ℂ, IsUnit (s • A + t • B)) →
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) (u v : Fin (n / 2) → Fin n → ℂ)
      (α β : Fin (n / 2) → ℂ), IsUnit P ∧ IsUnit Q ∧
      A = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
      B = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j)

def H2 : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), (∀ s t : ℂ, ¬ IsUnit (s • A + t • B)) →
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) (u v : Fin (n / 2) → Fin n → ℂ)
      (α β : Fin (n / 2) → ℂ), IsUnit P ∧ IsUnit Q ∧
      A = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
      B = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j)

theorem sep_iff (f : ℂ[X]) :
    f.Separable ↔ ∀ a : ℂ, f.eval a ≠ 0 ∨ (derivative f).eval a ≠ 0 := by
  rw [separable_def, isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  simp only [coe_aeval_eq_eval]

theorem fel (F h : ℂ[X]) (hF : F.Separable) :
    {x : ℂ | ¬ (h + C x * F).Separable}.Finite := by
  set W := F * derivative h - derivative F * h with hWdef
  have hF0 : F ≠ 0 := hF.ne_zero
  by_cases hW : W = 0
  · have hdvd : F ∣ h := by
      have h1 : F ∣ h * derivative F := ⟨derivative h, by linear_combination (-1 : ℂ[X]) * hW⟩
      exact ((separable_def F).mp hF).dvd_of_dvd_mul_right h1
    obtain ⟨g, rfl⟩ := hdvd
    have hg : derivative g = 0 := by
      have h2 : F * F * derivative g = 0 := by
        rw [hWdef, derivative_mul] at hW
        linear_combination hW
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd (mul_self_eq_zero.mp h3) hF0
      · exact h3
    have hgC := eq_C_of_derivative_eq_zero hg
    apply (Set.finite_singleton (-(g.coeff 0))).subset
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [Set.mem_singleton_iff]
    by_contra hne
    apply hx
    have : F * g + C x * F = F * C (g.coeff 0 + x) := by
      rw [hgC]; simp only [coeff_C_zero, C_add]; ring
    rw [this]
    refine hF.mul_unit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_))
    intro h0; apply hne; linear_combination h0
  · let φ : ℂ → ℂ := fun a => if F.eval a ≠ 0 then -(h.eval a / F.eval a)
      else -((derivative h).eval a / (derivative F).eval a)
    apply ((W.roots.toFinset.finite_toSet).image φ).subset
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rw [sep_iff] at hx
    push Not at hx
    obtain ⟨a, ha1, ha2⟩ := hx
    simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add, eval_add,
      eval_mul, eval_C] at ha1 ha2
    refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [mem_roots hW, IsRoot, hWdef]
      simp only [eval_sub, eval_mul]
      linear_combination (eval a F) * ha2 - (eval a (derivative F)) * ha1
    · simp only [φ]
      by_cases hFa : F.eval a ≠ 0
      · rw [if_pos hFa, neg_eq_iff_eq_neg, div_eq_iff hFa]; linear_combination ha1
      · rw [if_neg hFa]
        push Not at hFa
        have hF' : (derivative F).eval a ≠ 0 := by
          rcases (sep_iff F).mp hF a with h4 | h4
          · exact absurd hFa h4
          · exact h4
        rw [neg_eq_iff_eq_neg, div_eq_iff hF']; linear_combination ha2

/-- determinant is affine in the bottom-right corner entry -/
theorem det_add_corner {R : Type*} [CommRing R] (k : ℕ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (a : R) : (M + diagonal (Pi.single (Fin.last k) a)).det
      = M.det + a * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_row _ (Fin.last k), det_succ_row M (Fin.last k)]
  simp_rw [Fin.succAbove_last]
  have hsub : ∀ j : Fin (k + 1), ((M + diagonal (Pi.single (Fin.last k) a)).submatrix
      Fin.castSucc j.succAbove) = M.submatrix Fin.castSucc j.succAbove := by
    intro j; ext r c
    simp [diagonal_apply, Fin.castSucc_ne_last]
  simp_rw [hsub]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have h1 : ∀ j : Fin k, (M + diagonal (Pi.single (Fin.last k) a)) (Fin.last k) j.castSucc
      = M (Fin.last k) j.castSucc := by
    intro j; simp [(Fin.castSucc_ne_last j).symm]
  have h2 : (M + diagonal (Pi.single (Fin.last k) a)) (Fin.last k) (Fin.last k)
      = M (Fin.last k) (Fin.last k) + a := by simp
  simp_rw [h1, h2, Fin.succAbove_last]
  have : ((-1 : R) ^ ((Fin.last k : ℕ) + (Fin.last k : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]; simp
  rw [this]
  ring



theorem exists_eval_ne_zero {p : ℂ[X]} (hp : p ≠ 0) : ∃ a : ℂ, p.eval a ≠ 0 := by
  obtain ⟨a, ha⟩ := (p.roots.toFinset.finite_toSet).exists_notMem
  refine ⟨a, fun h0 => ha ?_⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  exact (mem_roots hp).mpr h0

theorem osl (k : ℕ) (U V : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (h : ((U.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 ∧ (((X : ℂ[X]) • (U.submatrix Fin.castSucc Fin.castSucc).map C + (V.submatrix Fin.castSucc Fin.castSucc).map C).det).Separable)) :
    ∃ x y : ℂ, ((U + diagonal (Pi.single (Fin.last k) x)).det ≠ 0 ∧ (((X : ℂ[X]) • (U + diagonal (Pi.single (Fin.last k) x)).map C + (V + diagonal (Pi.single (Fin.last k) y)).map C).det).Separable) := by
  set Ub := U.submatrix Fin.castSucc Fin.castSucc
  set Vb := V.submatrix Fin.castSucc Fin.castSucc
  set pb := ((X : ℂ[X]) • (Ub).map C + (Vb).map C).det with hpb
  have hpb0 : pb ≠ 0 := h.2.ne_zero
  obtain ⟨a, ha⟩ := exists_eval_ne_zero hpb0
  have hcop : IsCoprime (X - C a) pb := by
    rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
    intro b
    simp only [coe_aeval_eq_eval, eval_sub, eval_X, eval_C]
    by_cases hb : b = a
    · right; rw [hb]; exact ha
    · left; exact sub_ne_zero.mpr hb
  set F := (X - C a) * pb with hF
  have hFs : F.Separable := (separable_X_sub_C (R := ℂ) (x := a)).mul h.2 hcop
  have hpen : ∀ x : ℂ, ((X : ℂ[X]) • (U + diagonal (Pi.single (Fin.last k) x)).map C + (V + diagonal (Pi.single (Fin.last k) (-a * x))).map C).det
      = ((X : ℂ[X]) • (U).map C + (V).map C).det + C x * F := by
    intro x
    have e1 : (X : ℂ[X]) • (U + diagonal (Pi.single (Fin.last k) x)).map C
        + (V + diagonal (Pi.single (Fin.last k) (-a * x))).map C
        = ((X : ℂ[X]) • U.map C + V.map C) + diagonal (Pi.single (Fin.last k) (C x * (X - C a))) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, diagonal_apply,
        smul_eq_mul]
      by_cases hij : i = j
      · subst hij
        by_cases hi : i = Fin.last k
        · subst hi; simp only [if_true, Pi.single_eq_same, map_add, map_mul, map_neg]; ring
        · simp [Pi.single_eq_of_ne hi]
      · simp [hij]
    rw [e1, det_add_corner]
    have e2 : ((X : ℂ[X]) • U.map C + V.map C).submatrix Fin.castSucc Fin.castSucc
        = (X : ℂ[X]) • Ub.map C + Vb.map C := by
      ext i j; simp [Ub, Vb]
    rw [e2, hF, hpb]
    ring
  have hdet : ∀ x : ℂ, (U + diagonal (Pi.single (Fin.last k) x)).det = U.det + x * Ub.det :=
    fun x => det_add_corner k U x
  have hfin := fel F (((X : ℂ[X]) • (U).map C + (V).map C).det) hFs
  have hfin2 : {x : ℂ | U.det + x * Ub.det = 0}.Finite := by
    apply (Set.finite_singleton (-(U.det / Ub.det))).subset
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [Set.mem_singleton_iff]
    rw [eq_neg_iff_add_eq_zero, add_div_eq_mul_add_div _ _ h.1, div_eq_zero_iff]
    left; linear_combination hx
  obtain ⟨x, hx⟩ := (hfin.union hfin2).exists_notMem
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hx
  refine ⟨x, -a * x, ?_, ?_⟩
  · rw [hdet]; exact hx.2
  · rw [hpen]; exact hx.1

theorem osl_all (s : ℕ) : ∀ (n : ℕ) (hs : s ≤ n) (U V : Matrix (Fin n) (Fin n) ℂ),
    ((U.submatrix (Fin.castLE hs) (Fin.castLE hs)).det ≠ 0 ∧ (((X : ℂ[X]) • (U.submatrix (Fin.castLE hs) (Fin.castLE hs)).map C + (V.submatrix (Fin.castLE hs) (Fin.castLE hs)).map C).det).Separable)
    → ∃ d₁ d₂ : Fin n → ℂ, (∀ i : Fin n, (i : ℕ) < s → d₁ i = 0 ∧ d₂ i = 0)
      ∧ ((U + diagonal d₁).det ≠ 0 ∧ (((X : ℂ[X]) • (U + diagonal d₁).map C + (V + diagonal d₂).map C).det).Separable) := by
  intro n
  induction n with
  | zero =>
    intro hs U V h
    obtain rfl : s = 0 := by omega
    refine ⟨0, 0, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
    have hU : U + diagonal (0 : Fin 0 → ℂ) = U.submatrix (Fin.castLE hs) (Fin.castLE hs) :=
      Subsingleton.elim _ _
    have hV : V + diagonal (0 : Fin 0 → ℂ) = V.submatrix (Fin.castLE hs) (Fin.castLE hs) :=
      Subsingleton.elim _ _
    rw [hU, hV]; exact h
  | succ k ih =>
    intro hs U V h
    by_cases hsk : s = k + 1
    · subst hsk
      refine ⟨0, 0, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
      have e : ∀ W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
          W.submatrix (Fin.castLE hs) (Fin.castLE hs) = W + diagonal 0 := by
        intro W; ext i j; simp
      rw [e U, e V] at h; exact h
    · have hs' : s ≤ k := by omega
      obtain ⟨e₁, e₂, he, hg⟩ := ih hs' (U.submatrix Fin.castSucc Fin.castSucc)
        (V.submatrix Fin.castSucc Fin.castSucc) (by
          have e : ∀ W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
              (W.submatrix Fin.castSucc Fin.castSucc).submatrix (Fin.castLE hs') (Fin.castLE hs')
              = W.submatrix (Fin.castLE hs) (Fin.castLE hs) := by
            intro W; ext i j; simp
          rw [e U, e V]; exact h)
      have e3 : ∀ (W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (e : Fin k → ℂ),
          (W + diagonal (Fin.snoc e 0)).submatrix Fin.castSucc Fin.castSucc
            = W.submatrix Fin.castSucc Fin.castSucc + diagonal e := by
        intro W e; ext i j
        simp only [submatrix_apply, Matrix.add_apply, diagonal_apply, Fin.castSucc_inj,
          Fin.snoc_castSucc]
      obtain ⟨x, y, hxy⟩ := osl k (U + diagonal (Fin.snoc e₁ 0))
        (V + diagonal (Fin.snoc e₂ 0)) (by rw [e3, e3]; exact hg)
      refine ⟨Fin.snoc e₁ 0 + Pi.single (Fin.last k) x, Fin.snoc e₂ 0 + Pi.single (Fin.last k) y,
        ?_, ?_⟩
      · intro i hi
        have hne : i ≠ Fin.last k := by
          intro h0; rw [h0, Fin.val_last] at hi; omega
        obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hne
        have hi' : (i' : ℕ) < s := by simpa using hi
        rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne,
          Fin.snoc_castSucc, Fin.snoc_castSucc, (he i' hi').1, (he i' hi').2]
        simp
      · have key : ∀ (W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (f g : Fin (k + 1) → ℂ),
            W + diagonal (f + g) = W + diagonal f + diagonal g := by
          intro W f g; rw [add_assoc, diagonal_add]; rfl
        rw [key, key]; exact hxy

theorem outer_sum {k : ℕ} (M W : Matrix (Fin k) (Fin k) ℂ) (hW : W.det ≠ 0) :
    M = ∑ l, vecMulVec (M *ᵥ fun i => W i l) (W⁻¹ l) := by
  have h1 : M = M * W * W⁻¹ := by
    rw [Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hW), Matrix.mul_one]
  ext i j
  conv_lhs => rw [h1]
  simp only [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply, mulVec, dotProduct,
    Finset.sum_mul]

theorem nice_of_good {k : ℕ} (U V : Matrix (Fin k) (Fin k) ℂ)
    (h : ((U).det ≠ 0 ∧ (((X : ℂ[X]) • (U).map C + (V).map C).det).Separable)) :
    ∃ (x y : Fin k → Fin k → ℂ) (c : Fin k → ℂ),
      U = ∑ l, vecMulVec (x l) (y l) ∧ V = ∑ l, c l • vecMulVec (x l) (y l) := by
  set p := ((X : ℂ[X]) • (U).map C + (V).map C).det with hp
  have hp0 : p ≠ 0 := h.2.ne_zero
  have hdeg : p.natDegree = k := by
    apply le_antisymm
    · have := natDegree_det_X_add_C_le U V
      simp only [Fintype.card_fin] at this
      rw [hp]; exact this
    · apply le_natDegree_of_ne_zero
      have := coeff_det_X_add_C_card U V
      simp only [Fintype.card_fin] at this
      rw [hp, this]; exact h.1
  have hcard : p.roots.card = k := by
    rw [← hdeg]; exact splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hnd : p.roots.Nodup := nodup_roots h.2
  have hfc : p.roots.toFinset.card = k := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  let μ : Fin k → ℂ := fun l => (p.roots.toFinset.equivFin.symm (Fin.cast hfc.symm l) : ℂ)
  have hμinj : Function.Injective μ := by
    intro a b hab
    have := Subtype.val_injective hab
    exact Fin.cast_injective _ (p.roots.toFinset.equivFin.symm.injective this)
  have hμroot : ∀ l, p.eval (μ l) = 0 := by
    intro l
    have hm : μ l ∈ p.roots.toFinset := (p.roots.toFinset.equivFin.symm _).2
    rw [Multiset.mem_toFinset, mem_roots hp0] at hm
    exact hm
  have hdet : ∀ l, (μ l • U + V).det = 0 := by
    intro l
    rw [← hμroot l, hp, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X, eval_C]
  choose v hv0 hv using fun l => exists_mulVec_eq_zero_iff.mpr (hdet l)
  have hUu : IsUnit U := (isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr h.1)
  have hVv : ∀ l, V *ᵥ v l = (-(μ l)) • (U *ᵥ v l) := by
    intro l
    have := hv l
    rw [add_mulVec, smul_mulVec] at this
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact this
  have heig : ∀ l, Module.End.HasEigenvector (toLin' (U⁻¹ * V)) (-(μ l)) (v l) := by
    intro l
    refine ⟨?_, hv0 l⟩
    rw [Module.End.mem_eigenspace_iff, toLin'_apply, ← mulVec_mulVec, hVv l, mulVec_smul,
      mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det U).mp hUu), one_mulVec]
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (toLin' (U⁻¹ * V)) (fun l => -(μ l))
      (neg_injective.comp hμinj) v heig
  let W : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun i l => v l i
  have hWcol : W.col = v := by ext l i; rfl
  have hW : IsUnit W := (linearIndependent_cols_iff_isUnit (K := ℂ)).mp (by rw [hWcol]; exact hli)
  have hWd : W.det ≠ 0 := ((isUnit_iff_isUnit_det W).mp hW).ne_zero
  have hcol : ∀ l, (fun i => W i l) = v l := fun l => rfl
  refine ⟨fun l => U *ᵥ v l, fun l => W⁻¹ l, fun l => -(μ l), ?_, ?_⟩
  · conv_lhs => rw [outer_sum U W hWd]
    simp only [hcol]
  · conv_lhs => rw [outer_sum V W hWd]
    simp only [hcol, hVv, smul_vecMulVec]


/- ### Coverings of matrix spaces by rank-one matrices -/

/-- The perturbation lemma: after adding suitable diagonal matrices, a pair of square matrices
lies in the span of `n` rank-one matrices. -/
theorem pert {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (d₁ d₂ : Fin n → ℂ) (x y : Fin n → Fin n → ℂ) (c : Fin n → ℂ),
      U + diagonal d₁ = ∑ l, vecMulVec (x l) (y l) ∧
      V + diagonal d₂ = ∑ l, c l • vecMulVec (x l) (y l) := by
  obtain ⟨d₁, d₂, -, hg⟩ := osl_all 0 n (Nat.zero_le n) U V
    ⟨by rw [Matrix.det_isEmpty]; exact one_ne_zero,
      by rw [Matrix.det_isEmpty]; exact separable_one⟩
  obtain ⟨x, y, c, h1, h2⟩ := nice_of_good _ _ hg
  exact ⟨d₁, d₂, x, y, c, h1, h2⟩

theorem diag_sum {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) :
    diagonal d = ∑ l, d l • vecMulVec (Pi.single l 1) (Pi.single l 1) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul, diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : i = l
    · subst hl; simp [Ne.symm hij]
    · simp [hl]

theorem base_eq {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) :
    P * diagonal d * Q = ∑ i, d i • vecMulVec (P *ᵥ Pi.single i 1) (Pi.single i 1 ᵥ* Q) := by
  rw [diag_sum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul]

/-- The perturbation lemma in the bases `(P, Q)`. -/
theorem pair_pert {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (hQ : IsUnit Q)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (x y : Fin n → Fin n → ℂ) (d₁ d₂ c : Fin n → ℂ),
      A = ∑ l, vecMulVec (x l) (y l) - P * diagonal d₁ * Q ∧
      B = ∑ l, c l • vecMulVec (x l) (y l) - P * diagonal d₂ * Q := by
  obtain ⟨d₁, d₂, x, y, c, h1, h2⟩ := pert (P⁻¹ * A * Q⁻¹) (P⁻¹ * B * Q⁻¹)
  have hPd : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP
  have hQd : IsUnit Q.det := (isUnit_iff_isUnit_det Q).mp hQ
  have conj : ∀ M : Matrix (Fin n) (Fin n) ℂ, P * (P⁻¹ * M * Q⁻¹) * Q = M := by
    intro M
    calc P * (P⁻¹ * M * Q⁻¹) * Q = (P * P⁻¹) * M * (Q⁻¹ * Q) := by
          simp only [Matrix.mul_assoc]
      _ = M := by
          rw [mul_nonsing_inv _ hPd, nonsing_inv_mul _ hQd, Matrix.one_mul, Matrix.mul_one]
  refine ⟨fun l => P *ᵥ x l, fun l => y l ᵥ* Q, d₁, d₂, c, ?_, ?_⟩
  · have h := congrArg (fun M => P * M * Q) h1
    simp only [Matrix.mul_add, Matrix.add_mul, conj, Matrix.mul_sum, Matrix.sum_mul,
      mul_vecMulVec, vecMulVec_mul] at h
    rw [← h]
    abel
  · have h := congrArg (fun M => P * M * Q) h2
    simp only [Matrix.mul_add, Matrix.add_mul, conj, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul] at h
    rw [← h]
    abel

/-- The covering family: the `n` matrices `(P eᵢ)(eᵢᵀ Q)`, `n` rank-one matrices for each of the
`k` pairs, and `e` extra rank-one matrices. -/
theorem cover {n k e : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (hQ : IsUnit Q)
    (A B : Fin k → Matrix (Fin n) (Fin n) ℂ) (ue ve : Fin e → Fin n → ℂ) :
    ∃ (ι : Type) (_ : Fintype ι) (x y : ι → Fin n → ℂ), Fintype.card ι = n + k * n + e ∧
      (∀ (d : Fin n → ℂ) (α : Fin e → ℂ),
        P * diagonal d * Q + ∑ j, α j • vecMulVec (ue j) (ve j) ∈
          Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l))) ∧
      ∀ j, A j ∈ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) ∧
        B j ∈ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  classical
  choose x' y' d₁ d₂ c hA hB using fun j => pair_pert P Q hP hQ (A j) (B j)
  refine ⟨Fin n ⊕ ((Fin k × Fin n) ⊕ Fin e), inferInstance,
    Sum.elim (fun i => P *ᵥ Pi.single i 1) (Sum.elim (fun p => x' p.1 p.2) ue),
    Sum.elim (fun i => Pi.single i 1 ᵥ* Q) (Sum.elim (fun p => y' p.1 p.2) ve), ?_, ?_⟩
  · rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_fin]
    ring
  · set W := Submodule.span ℂ (Set.range fun l : Fin n ⊕ ((Fin k × Fin n) ⊕ Fin e) =>
      vecMulVec (Sum.elim (fun i => P *ᵥ Pi.single i 1) (Sum.elim (fun p => x' p.1 p.2) ue) l)
        (Sum.elim (fun i => Pi.single i 1 ᵥ* Q) (Sum.elim (fun p => y' p.1 p.2) ve) l)) with hW
    have hbase : ∀ i : Fin n, vecMulVec (P *ᵥ Pi.single i 1) (Pi.single i 1 ᵥ* Q) ∈ W :=
      fun i => Submodule.subset_span ⟨Sum.inl i, rfl⟩
    have hpair : ∀ j l, vecMulVec (x' j l) (y' j l) ∈ W :=
      fun j l => Submodule.subset_span ⟨Sum.inr (Sum.inl (j, l)), rfl⟩
    have hext : ∀ j, vecMulVec (ue j) (ve j) ∈ W :=
      fun j => Submodule.subset_span ⟨Sum.inr (Sum.inr j), rfl⟩
    have hdiag : ∀ d : Fin n → ℂ, P * diagonal d * Q ∈ W := by
      intro d
      rw [base_eq]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbase i)
    refine ⟨fun d α => W.add_mem (hdiag d)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hext j)), fun j => ⟨?_, ?_⟩⟩
    · rw [hA j]
      exact W.sub_mem (Submodule.sum_mem _ fun l _ => hpair j l) (hdiag _)
    · rw [hB j]
      exact W.sub_mem (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hpair j l))
        (hdiag _)

theorem headI_lt {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : t.1.headI < d := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha _ => exact ha

theorem ix_surj {d₁ d₂ d₃ : ℕ} (t : HolorIndex [d₁, d₂, d₃]) :
    ∃ (c : Fin d₁) (i : Fin d₂) (j : Fin d₃),
      t = ⟨[c.1, i.1, j.1], .cons c.2 (.cons i.2 (.cons j.2 .nil))⟩ := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha h =>
    cases h with
    | cons hb h =>
      cases h with
      | cons hc h =>
        cases h
        exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl⟩

theorem cprank_le_of_cprankMax {ds : List ℕ} {x : Holor ℂ ds} {k : ℕ}
    (h : Holor.CPRankMax k x) : x.cprank ≤ k :=
  @Nat.find_min' (fun n => Holor.CPRankMax n x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩ k h

/-- A tensor whose entries are a sum of products has rank at most the number of summands. -/
theorem cprank_le_of_sum {d₁ d₂ d₃ : ℕ} {ι : Type} [Fintype ι] (T : Holor ℂ [d₁, d₂, d₃])
    (u : ι → Fin d₁ → ℂ) (v : ι → Fin d₂ → ℂ) (w : ι → Fin d₃ → ℂ)
    (h : ∀ (c : Fin d₁) (i : Fin d₂) (j : Fin d₃),
      T ⟨[c.1, i.1, j.1], .cons c.2 (.cons i.2 (.cons j.2 .nil))⟩ =
        ∑ l, u l c * v l i * w l j) :
    T.cprank ≤ Fintype.card ι := by
  classical
  let R : ι → Holor ℂ [d₁, d₂, d₃] := fun l =>
    Holor.mul (fun t : HolorIndex [d₁] => u l ⟨t.1.headI, headI_lt t⟩)
      (Holor.mul (fun t : HolorIndex [d₂] => v l ⟨t.1.headI, headI_lt t⟩)
        (Holor.mul (fun t : HolorIndex [d₃] => w l ⟨t.1.headI, headI_lt t⟩)
          (fun _ : HolorIndex [] => (1 : ℂ))))
  have hR : ∀ l, Holor.CPRankMax1 (R l) := fun l => .cons _ _ (.cons _ _ (.cons _ _ (.nil _)))
  have hT : T = ∑ l, R l := by
    funext t
    obtain ⟨c, i, j, rfl⟩ := ix_surj t
    rw [h]
    have hs : ∀ s : Finset ι,
        (∑ l ∈ s, R l) ⟨[c.1, i.1, j.1], .cons c.2 (.cons i.2 (.cons j.2 .nil))⟩ =
          ∑ l ∈ s, u l c * v l i * w l j := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rfl
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
        show R a _ + _ = _
        congr 1
        show u a c * (v a i * (w a j * 1)) = _
        ring
    exact (hs Finset.univ).symm
  have hr := Holor.cprankMax_sum (n := 1) Finset.univ R fun l _ => Holor.cprankMax_1 (hR l)
  rw [Finset.card_univ, mul_one, ← hT] at hr
  exact cprank_le_of_cprankMax hr

/-- If all slices lie in the span of `r` rank-one matrices, the tensor has rank at most `r`. -/
theorem cprank_le_of_cover {m n r : ℕ} (T : Holor ℂ [m, n, n]) {ι : Type} [Fintype ι]
    (x y : ι → Fin n → ℂ) (hcard : Fintype.card ι ≤ r)
    (h : ∀ i : Fin m, (Matrix.of fun (j k : Fin n) =>
        T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ :
          Matrix (Fin n) (Fin n) ℂ) ∈
      Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l))) : T.cprank ≤ r := by
  classical
  have hc : ∀ i : Fin m, ∃ c : ι → ℂ, ∑ l, c l • vecMulVec (x l) (y l) =
      (Matrix.of fun (j k : Fin n) =>
        T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ :
          Matrix (Fin n) (Fin n) ℂ) :=
    fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (h i)
  choose c hc using hc
  refine (cprank_le_of_sum T (fun l i => c i l) x y ?_).trans hcard
  intro i j k
  have h1 := congrFun (congrFun (hc i) j) k
  rw [Matrix.of_apply] at h1
  rw [← h1, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  ring

end OMA.R1

namespace OMA

open Module

namespace SqH2

section Pencil

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The pair `(A, B)` is a sum of at most `r` rank-one pencils. -/
def PRank (r : ℕ) (A B : V →ₗ[ℂ] W) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a b : ι → ℂ) (ψ : ι → V →ₗ[ℂ] ℂ) (u : ι → W),
    Fintype.card ι ≤ r ∧ A = ∑ i, a i • (ψ i).smulRight (u i) ∧
      B = ∑ i, b i • (ψ i).smulRight (u i)

theorem PRank.mono {r r' : ℕ} {A B : V →ₗ[ℂ] W} (h : PRank r A B) (hr : r ≤ r') :
    PRank r' A B := by
  obtain ⟨ι, _, a, b, ψ, u, hc, hA, hB⟩ := h
  exact ⟨ι, _, a, b, ψ, u, hc.trans hr, hA, hB⟩

theorem PRank.comp_right {V' : Type} [AddCommGroup V'] [Module ℂ V'] {r : ℕ}
    {A B : V →ₗ[ℂ] W} (h : PRank r A B) (M : V' →ₗ[ℂ] V) :
    PRank r (A ∘ₗ M) (B ∘ₗ M) := by
  obtain ⟨ι, _, a, b, ψ, u, hc, rfl, rfl⟩ := h
  refine ⟨ι, _, a, b, fun i => ψ i ∘ₗ M, u, hc, ?_, ?_⟩ <;>
  · ext x
    simp [LinearMap.sum_apply]

theorem PRank.comp_left {W' : Type} [AddCommGroup W'] [Module ℂ W'] {r : ℕ}
    {A B : V →ₗ[ℂ] W} (h : PRank r A B) (L : W →ₗ[ℂ] W') :
    PRank r (L ∘ₗ A) (L ∘ₗ B) := by
  obtain ⟨ι, _, a, b, ψ, u, hc, rfl, rfl⟩ := h
  refine ⟨ι, _, a, b, ψ, fun i => L (u i), hc, ?_, ?_⟩ <;>
  · ext x
    simp [LinearMap.sum_apply]

theorem PRank.add_smulRight {r : ℕ} {A B : V →ₗ[ℂ] W} (h : PRank r A B) (a b : ℂ)
    (ψ : V →ₗ[ℂ] ℂ) (u : W) :
    PRank (r + 1) (A + a • ψ.smulRight u) (B + b • ψ.smulRight u) := by
  obtain ⟨ι, _, a', b', ψ', u', hc, rfl, rfl⟩ := h
  refine ⟨Option ι, inferInstance, fun o => o.elim a a', fun o => o.elim b b',
    fun o => o.elim ψ ψ', fun o => o.elim u u', by simpa using hc, ?_, ?_⟩ <;>
  · rw [Fintype.sum_option]
    simp [add_comm]

theorem prank_of_basis {ι : Type} [Fintype ι] (bs : Basis ι ℂ V) (t : ι → ℂ)
    (A B : V →ₗ[ℂ] W) (h : ∀ i, A (bs i) = t i • B (bs i)) :
    PRank (Fintype.card ι) A B := by
  classical
  refine ⟨ι, inferInstance, t, fun _ => 1, bs.coord, fun i => B (bs i), le_rfl, ?_, ?_⟩ <;>
  · refine bs.ext fun j => ?_
    simp [LinearMap.sum_apply, h, Finsupp.single_apply]

/-- No left eigenvector: every nontrivial combination is surjective. -/
def NoLeft (A B : V →ₗ[ℂ] W) : Prop :=
  ∀ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) → Function.Surjective (s • A + t • B)

theorem NoLeft.finrank_lt [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {A B : V →ₗ[ℂ] W}
    (h : NoLeft A B) (hW : 0 < finrank ℂ W) : finrank ℂ W < finrank ℂ V := by
  by_contra hlt
  have hB : Function.Surjective B := by
    have := h 0 1 (Or.inr one_ne_zero)
    simpa using this
  have hle : finrank ℂ W ≤ finrank ℂ V := LinearMap.finrank_le_finrank_of_surjective hB
  have heq : finrank ℂ V = finrank ℂ W := by omega
  have hBi : Function.Injective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hB
  let e : V ≃ₗ[ℂ] W := LinearEquiv.ofBijective B ⟨hBi, hB⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (e.symm.toLinearMap ∘ₗ A)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have h1 : e.symm (A v) = c • v := by
    have := hv.apply_eq_smul
    simpa using this
  have h2 : A v = c • B v := by
    have h := congrArg e h1
    rw [LinearEquiv.apply_symm_apply, map_smul] at h
    exact h
  have hs := h 1 (-c) (Or.inl one_ne_zero)
  have hi : Function.Injective ((1 : ℂ) • A + (-c) • B) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hs
  have h3 : ((1 : ℂ) • A + (-c) • B) v = ((1 : ℂ) • A + (-c) • B) 0 := by
    simp [h2]
  exact hv.2 (hi h3)

theorem span_ker (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A B : V →ₗ[ℂ] W), finrank ℂ V = n → NoLeft A B → ∀ Λ : Finset ℂ,
    (⨆ (t : ℂ) (_ : t ∉ Λ), LinearMap.ker (A + t • B)) = ⊤ := by
  induction n with
  | zero =>
    intro V W _ _ _ _ _ _ A B hn hNL Λ
    have hW : finrank ℂ W = 0 := by
      by_contra hW
      have := hNL.finrank_lt (Nat.pos_of_ne_zero hW)
      omega
    have : Subsingleton W := Module.finrank_zero_iff.mp hW
    obtain ⟨t0, ht0⟩ := Infinite.exists_notMem_finset Λ
    refine top_le_iff.mp (le_iSup₂_of_le t0 ht0 ?_)
    intro x _
    exact Subsingleton.elim _ _
  | succ n ih =>
    intro V W _ _ _ _ _ _ A B hn hNL Λ
    obtain ⟨t0, ht0⟩ := Infinite.exists_notMem_finset Λ
    by_cases hW : finrank ℂ W = 0
    · have : Subsingleton W := Module.finrank_zero_iff.mp hW
      refine top_le_iff.mp (le_iSup₂_of_le t0 ht0 ?_)
      intro x _
      exact Subsingleton.elim _ _
    have hlt := hNL.finrank_lt (Nat.pos_of_ne_zero hW)
    have hker : LinearMap.ker (A + t0 • B) ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt
    obtain ⟨v, hvk, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hAv : A v = -(t0 • B v) := by
      have h : A v + t0 • B v = 0 := by simpa using hvk
      exact eq_neg_of_add_eq_zero_left h
    set p : Submodule ℂ V := Submodule.span ℂ {v} with hp
    set q : Submodule ℂ W := Submodule.span ℂ {B v} with hq
    have hBq : B v ∈ q := Submodule.mem_span_singleton_self _
    have hpA : p ≤ q.comap A := by
      rw [hp, Submodule.span_le, Set.singleton_subset_iff]
      show A v ∈ q
      rw [hAv]
      exact q.neg_mem (q.smul_mem _ hBq)
    have hpB : p ≤ q.comap B := by
      rw [hp, Submodule.span_le, Set.singleton_subset_iff]
      exact hBq
    have hNL' : NoLeft (p.mapQ q A hpA) (p.mapQ q B hpB) := by
      intro s t hst w'
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective q w'
      obtain ⟨x, hx⟩ := hNL s t hst w
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      rw [← hx]
      simp [Submodule.mapQ_apply]
    have hfr : finrank ℂ (V ⧸ p) = n := by
      have h1 := Submodule.finrank_quotient_add_finrank p
      have h2 : finrank ℂ p = 1 := finrank_span_singleton hv
      omega
    have IH := ih (V ⧸ p) (W ⧸ q) (p.mapQ q A hpA) (p.mapQ q B hpB) hfr hNL' (insert t0 Λ)
    set S : Submodule ℂ V := ⨆ (t : ℂ) (_ : t ∉ Λ), LinearMap.ker (A + t • B) with hS
    have hvS : v ∈ S := (le_iSup₂_of_le (f := fun (t : ℂ) (_ : t ∉ Λ) => LinearMap.ker (A + t • B))
      t0 ht0 le_rfl) hvk
    have hpS : p ≤ S := by
      rw [hp, Submodule.span_le, Set.singleton_subset_iff]
      exact hvS
    have hmap : S.map p.mkQ = ⊤ := by
      rw [← top_le_iff, ← IH]
      refine iSup₂_le fun t ht => ?_
      have htΛ : t ∉ Λ := fun h => ht (Finset.mem_insert_of_mem h)
      have htt : t ≠ t0 := fun h => ht (h ▸ Finset.mem_insert_self _ _)
      intro xb hxb
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective p xb
      have h1 : (A + t • B) x ∈ q := by
        have h := LinearMap.mem_ker.mp hxb
        rw [← Submodule.Quotient.mk_eq_zero q]
        simpa [Submodule.mapQ_apply] using h
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
      have htt' : t - t0 ≠ 0 := sub_ne_zero.mpr htt
      refine ⟨x - (c / (t - t0)) • v, ?_, ?_⟩
      · refine (le_iSup₂_of_le (f := fun (t : ℂ) (_ : t ∉ Λ) => LinearMap.ker (A + t • B))
          t htΛ le_rfl) ?_
        rw [LinearMap.mem_ker, map_sub, ← hc, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          hAv, ← sub_eq_zero]
        have : c • B v - (c / (t - t0)) • (-(t0 • B v) + t • B v) - 0
            = (c - (c / (t - t0)) * (t - t0)) • B v := by
          module
        rw [this, div_mul_cancel₀ _ htt', sub_self, zero_smul]
      · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, sub_eq_self,
          Submodule.Quotient.mk_eq_zero]
        exact p.smul_mem _ (Submodule.mem_span_singleton_self _)
    have h2 := (Submodule.map_mkQ_eq_top p S).mp hmap
    rwa [sup_eq_right.mpr hpS] at h2

theorem prank_of_noLeft [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {A B : V →ₗ[ℂ] W}
    (h : NoLeft A B) : PRank (finrank ℂ V) A B := by
  classical
  have hspan := span_ker (finrank ℂ V) V W A B rfl h ∅
  set E : Set V := {v | ∃ t : ℂ, A v = t • B v} with hE
  have hE' : Submodule.span ℂ E = ⊤ := by
    rw [← top_le_iff, ← hspan]
    refine iSup₂_le fun t _ => ?_
    intro x hx
    refine Submodule.subset_span ⟨-t, ?_⟩
    have h1 : A x + t • B x = 0 := by simpa using hx
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h1
  obtain ⟨b, hbE, hbspan, hli⟩ := exists_linearIndependent ℂ E
  have hb : ⊤ ≤ Submodule.span ℂ (Set.range (Subtype.val : b → V)) := by
    rw [Subtype.range_coe, hbspan, hE']
  let bs : Basis b ℂ V := Basis.mk hli hb
  have : Fintype b := FiniteDimensional.fintypeBasisIndex bs
  have hcard : finrank ℂ V = Fintype.card b := Module.finrank_eq_card_basis bs
  have ht : ∀ i : b, ∃ t : ℂ, A (bs i) = t • B (bs i) := by
    intro i
    have h1 : bs i = (i : V) := by simp [bs]
    rw [h1]
    exact hbE i.2
  choose t ht using ht
  rw [hcard]
  exact prank_of_basis bs t A B ht

theorem prank_le (k : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A B : V →ₗ[ℂ] W), finrank ℂ V + finrank ℂ W = k →
    PRank (finrank ℂ W + finrank ℂ V / 2) A B := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro V W _ _ _ _ _ _ A B hk
    by_cases h0 : ∃ v : V, v ≠ 0 ∧ A v = 0 ∧ B v = 0
    · obtain ⟨v, hv, hAv, hBv⟩ := h0
      set p : Submodule ℂ V := Submodule.span ℂ {v} with hp
      have hpA : p ≤ LinearMap.ker A := by
        rw [hp, Submodule.span_le, Set.singleton_subset_iff]
        exact hAv
      have hpB : p ≤ LinearMap.ker B := by
        rw [hp, Submodule.span_le, Set.singleton_subset_iff]
        exact hBv
      have hfr : finrank ℂ (V ⧸ p) + 1 = finrank ℂ V := by
        have h1 := Submodule.finrank_quotient_add_finrank p
        have h2 : finrank ℂ p = 1 := finrank_span_singleton hv
        omega
      have IH := ih (finrank ℂ (V ⧸ p) + finrank ℂ W) (by omega) (V ⧸ p) W
        (p.liftQ A hpA) (p.liftQ B hpB) rfl
      have h2 := IH.comp_right p.mkQ
      rw [Submodule.liftQ_mkQ, Submodule.liftQ_mkQ] at h2
      exact h2.mono (by omega)
    by_cases h1 : NoLeft A B
    · have h2 := prank_of_noLeft h1
      have hinj : Function.Injective (A.prod B) := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro x hx
        by_contra hx0
        have hx' : (A x, B x) = 0 := by simpa using hx
        exact h0 ⟨x, hx0, congrArg Prod.fst hx', congrArg Prod.snd hx'⟩
      have h3 := LinearMap.finrank_le_finrank_of_injective hinj
      rw [Module.finrank_prod] at h3
      exact h2.mono (by omega)
    · simp only [NoLeft, not_forall] at h1
      obtain ⟨s, t, hst, hns⟩ := h1
      have hr : LinearMap.range (s • A + t • B) < ⊤ :=
        lt_top_iff_ne_top.mpr (fun h => hns (LinearMap.range_eq_top.mp h))
      obtain ⟨φ, hφ, hφr⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hr inferInstance
      have hφ0 : ∀ x, s * φ (A x) + t * φ (B x) = 0 := by
        intro x
        have hmem : φ ((s • A + t • B) x) ∈ (LinearMap.range (s • A + t • B)).map φ :=
          ⟨_, ⟨x, rfl⟩, rfl⟩
        rw [hφr] at hmem
        simpa using hmem
      obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
        by_contra h
        exact hφ (LinearMap.ext fun x => by_contra fun hx => h ⟨x, hx⟩)
      set w : W := (φ w0)⁻¹ • w0 with hw
      have hφw : φ w = 1 := by simp [hw, hw0]
      let K : Submodule ℂ W := LinearMap.ker φ
      let P : W →ₗ[ℂ] K := LinearMap.codRestrict K (LinearMap.id - φ.smulRight w) (by
        intro x
        simp [K, hφw])
      have hP : ∀ x, ((P x : K) : W) = x - φ x • w := fun x => rfl
      have hfr : finrank ℂ K + 1 = finrank ℂ W := by
        have h1 : finrank ℂ (LinearMap.range φ) + finrank ℂ K = finrank ℂ W :=
          LinearMap.finrank_range_add_finrank_ker φ
        have hsurj : Function.Surjective φ := by
          intro c
          exact ⟨c • w, by simp [hφw]⟩
        have h2 : finrank ℂ (LinearMap.range φ) = 1 := by
          rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self]
        omega
      have IH := ih (finrank ℂ V + finrank ℂ K) (by omega) V K (P ∘ₗ A) (P ∘ₗ B) rfl
      have h2 := IH.comp_left K.subtype
      by_cases hs : s = 0
      · have ht : t ≠ 0 := by tauto
        have hφB : ∀ x, φ (B x) = 0 := by
          intro x
          have := hφ0 x
          simpa [hs, ht] using this
        have h3 := h2.add_smulRight 1 0 (φ ∘ₗ A) w
        have eA : K.subtype ∘ₗ P ∘ₗ A + (1 : ℂ) • (φ ∘ₗ A).smulRight w = A := by
          ext x
          simp [hP]
        have eB : K.subtype ∘ₗ P ∘ₗ B + (0 : ℂ) • (φ ∘ₗ A).smulRight w = B := by
          ext x
          simp [hP, hφB]
        rw [eA, eB] at h3
        exact h3.mono (by omega)
      · have hφA : ∀ x, φ (A x) = (-(t / s)) * φ (B x) := by
          intro x
          have := hφ0 x
          field_simp
          linear_combination this
        have h3 := h2.add_smulRight (-(t / s)) 1 (φ ∘ₗ B) w
        have eA : K.subtype ∘ₗ P ∘ₗ A + (-(t / s)) • (φ ∘ₗ B).smulRight w = A := by
          ext x
          simp [hP, hφA, mul_smul]
        have eB : K.subtype ∘ₗ P ∘ₗ B + (1 : ℂ) • (φ ∘ₗ B).smulRight w = B := by
          ext x
          simp [hP]
        rw [eA, eB] at h3
        exact h3.mono (by omega)

end Pencil
section Regular

open Matrix

/-- An invertible sum of rank-one matrices has at least `n` terms. -/
theorem card_ge_of_isUnit {n : ℕ} {ι : Type} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (x y : ι → Fin n → ℂ) (h : IsUnit (∑ l ∈ s, c l • vecMulVec (x l) (y l))) : n ≤ s.card := by
  have hprod : ∑ l ∈ s, c l • vecMulVec (x l) (y l) =
      (Matrix.of fun (i : Fin n) (l : s) => c l * x l i) *
        (Matrix.of fun (l : s) (j : Fin n) => y l j) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Matrix.mul_apply,
      Matrix.of_apply, smul_eq_mul]
    rw [← Finset.sum_coe_sort s]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hr : (∑ l ∈ s, c l • vecMulVec (x l) (y l)).rank = n := by
    rw [Matrix.rank_of_isUnit _ h, Fintype.card_fin]
  rw [hprod] at hr
  have hle := (Matrix.rank_mul_le_left (Matrix.of fun (i : Fin n) (l : s) => c l * x l i)
    (Matrix.of fun (l : s) (j : Fin n) => y l j)).trans (Matrix.rank_le_card_width _)
  rw [hr, Fintype.card_coe] at hle
  exact hle

/-- From an invertible sum of more than `n` rank-one matrices one term can be removed. -/
theorem exists_erase {n : ℕ} {ι : Type} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (x y : ι → Fin n → ℂ) (h : IsUnit (∑ l ∈ s, c l • vecMulVec (x l) (y l)))
    (hcard : n < s.card) :
    ∃ l₀ ∈ s, IsUnit (∑ l ∈ s.erase l₀, c l • vecMulVec (x l) (y l)) := by
  set G := ∑ l ∈ s, c l • vecMulVec (x l) (y l) with hG
  have hGdet : IsUnit G.det := (isUnit_iff_isUnit_det G).mp h
  have htr : (G⁻¹ * G).trace = (n : ℂ) := by
    rw [nonsing_inv_mul _ hGdet, Matrix.trace_one, Fintype.card_fin]
  have htr2 : (G⁻¹ * G).trace = ∑ l ∈ s, c l * ((G⁻¹ *ᵥ x l) ⬝ᵥ y l) := by
    have e : G⁻¹ * G = ∑ l ∈ s, c l • vecMulVec (G⁻¹ *ᵥ x l) (y l) := by
      conv_lhs => rw [hG]
      rw [Matrix.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [Matrix.mul_smul, mul_vecMulVec]
    rw [e, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun l _ => by
      rw [Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul]
  by_contra hall
  have h1 : ∀ l ∈ s, c l * ((G⁻¹ *ᵥ x l) ⬝ᵥ y l) = 1 := by
    intro l hl
    by_contra hne
    apply hall
    refine ⟨l, hl, ?_⟩
    rw [Finset.sum_erase_eq_sub hl, ← hG]
    have hfac : G - c l • vecMulVec (x l) (y l) =
        G * (1 + vecMulVec (-(c l) • (G⁻¹ *ᵥ x l)) (y l)) := by
      rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, mul_nonsing_inv _ hGdet, Matrix.one_mulVec, ← smul_vecMulVec,
        neg_smul, sub_eq_add_neg, neg_vecMulVec]
    rw [hfac, isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.vecMulVec_eq Unit,
      Matrix.det_one_add_replicateCol_mul_replicateRow]
    refine hGdet.mul (isUnit_iff_ne_zero.mpr ?_)
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm]
    intro h0
    apply hne
    linear_combination -h0
  have hsum : (n : ℂ) = (s.card : ℂ) := by
    rw [← htr, htr2, Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : n = s.card := by exact_mod_cast hsum
  omega

/-- An invertible sum of rank-one matrices contains an invertible subsum with exactly `n`
terms. -/
theorem exists_subsum {n : ℕ} {ι : Type} [DecidableEq ι] (c : ι → ℂ) (x y : ι → Fin n → ℂ) :
    ∀ (k : ℕ) (s : Finset ι), s.card = n + k →
      IsUnit (∑ l ∈ s, c l • vecMulVec (x l) (y l)) →
      ∃ s' ⊆ s, s'.card = n ∧ IsUnit (∑ l ∈ s', c l • vecMulVec (x l) (y l)) := by
  intro k
  induction k with
  | zero => exact fun s hs h => ⟨s, Finset.Subset.refl s, by simpa using hs, h⟩
  | succ k ih =>
    intro s hs h
    obtain ⟨l₀, hl₀, h'⟩ := exists_erase s c x y h (by omega)
    obtain ⟨s', hs', hc, hu⟩ := ih (s.erase l₀) (by rw [Finset.card_erase_of_mem hl₀]; omega) h'
    exact ⟨s', hs'.trans (Finset.erase_subset _ _), hc, hu⟩

/-- A sum of rank-one matrices over a finset of `n` indices, as `P * diagonal * Q`. -/
theorem sum_eq_mul_diag_mul {n : ℕ} {ι : Type} (s : Finset ι) (e : Fin n ≃ s)
    (d : ι → ℂ) (x y : ι → Fin n → ℂ) :
    ∑ l ∈ s, d l • vecMulVec (x l) (y l) =
      (Matrix.of fun (i : Fin n) (k : Fin n) => x (e k) i) *
        Matrix.diagonal (fun k => d (e k)) * (Matrix.of fun (k : Fin n) (j : Fin n) => y (e k) j) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul]
  rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp e]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- A sum of rank-one matrices over a finset with at most `m` elements, padded by zeros to a
sum over `Fin m`, simultaneously for two families of coefficients. -/
theorem exists_pad {n m : ℕ} {ι : Type} (s : Finset ι) (hs : s.card ≤ m)
    (a b : ι → ℂ) (x y : ι → Fin n → ℂ) :
    ∃ (u v : Fin m → Fin n → ℂ) (α β : Fin m → ℂ),
      ∑ l ∈ s, a l • vecMulVec (x l) (y l) = ∑ j, α j • vecMulVec (u j) (v j) ∧
      ∑ l ∈ s, b l • vecMulVec (x l) (y l) = ∑ j, β j • vecMulVec (u j) (v j) := by
  have hcard : Fintype.card s ≤ Fintype.card (Fin m) := by
    rw [Fintype.card_coe, Fintype.card_fin]
    exact hs
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨Function.extend emb (fun l : s => x l) 0, Function.extend emb (fun l : s => y l) 0,
    Function.extend emb (fun l : s => a l) 0, Function.extend emb (fun l : s => b l) 0, ?_, ?_⟩
  · rw [← Finset.sum_coe_sort s]
    refine Fintype.sum_of_injective emb emb.injective _ _ (fun j hj => ?_) (fun l => ?_)
    · rw [Function.extend_apply' _ _ _ (fun h => hj h), Pi.zero_apply, zero_smul]
    · rw [emb.injective.extend_apply, emb.injective.extend_apply, emb.injective.extend_apply]
  · rw [← Finset.sum_coe_sort s]
    refine Fintype.sum_of_injective emb emb.injective _ _ (fun j hj => ?_) (fun l => ?_)
    · rw [Function.extend_apply' _ _ _ (fun h => hj h), Pi.zero_apply, zero_smul]
    · rw [emb.injective.extend_apply, emb.injective.extend_apply, emb.injective.extend_apply]

/-- A pencil of rank at most `r`, in matrix form. -/
theorem mat_of_prank {n r : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : PRank r (Matrix.toLin' A) (Matrix.toLin' B)) :
    ∃ (ι : Type) (_ : Fintype ι) (a b : ι → ℂ) (x y : ι → Fin n → ℂ),
      Fintype.card ι ≤ r ∧ A = ∑ l, a l • vecMulVec (x l) (y l) ∧
        B = ∑ l, b l • vecMulVec (x l) (y l) := by
  obtain ⟨ι, hι, a, b, ψ, w, hc, hA, hB⟩ := h
  refine ⟨ι, hι, a, b, w, fun l j => ψ l (Pi.single j 1), hc, ?_, ?_⟩
  · ext i j
    have h1 := congrFun (LinearMap.congr_fun hA (Pi.single j 1)) i
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one] at h1
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at h1
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    rw [h1]
    exact Finset.sum_congr rfl fun l _ => by ring
  · ext i j
    have h1 := congrFun (LinearMap.congr_fun hB (Pi.single j 1)) i
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one] at h1
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at h1
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    rw [h1]
    exact Finset.sum_congr rfl fun l _ => by ring

/-- The regular case: a pencil of `n × n` matrices containing an invertible matrix is, in
suitable bases, simultaneously diagonal up to `n / 2` rank-one pencils; moreover no diagonal
coefficient pair vanishes. -/
theorem regular_pencil (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∃ s t : ℂ, IsUnit (s • A + t • B)) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) (u v : Fin (n / 2) → Fin n → ℂ)
      (α β : Fin (n / 2) → ℂ), IsUnit P ∧ IsUnit Q ∧
      A = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
      B = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j) ∧
      ∃ s t : ℂ, ∀ k, s * a k + t * b k ≠ 0 := by
  classical
  obtain ⟨s, t, hst⟩ := h
  have h0 := prank_le (n + n) (Fin n → ℂ) (Fin n → ℂ) (Matrix.toLin' A) (Matrix.toLin' B)
    (by simp)
  rw [Module.finrank_fin_fun] at h0
  obtain ⟨ι, _, a, b, x, y, hc, hA, hB⟩ := mat_of_prank A B h0
  have hsum : s • A + t • B = ∑ l ∈ Finset.univ, (s * a l + t * b l) • vecMulVec (x l) (y l) := by
    rw [hA, hB, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul, smul_smul, add_smul]
  rw [hsum] at hst
  have hge : n ≤ (Finset.univ : Finset ι).card := card_ge_of_isUnit _ _ x y hst
  obtain ⟨s', hs', hcard, hu⟩ := exists_subsum (fun l => s * a l + t * b l) x y
    ((Finset.univ : Finset ι).card - n) Finset.univ (by omega) hst
  have e : Fin n ≃ s' := (Finset.equivFinOfCardEq hcard).symm
  rw [sum_eq_mul_diag_mul s' e] at hu
  have hdet := (isUnit_iff_isUnit_det _).mp hu
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hP : IsUnit (Matrix.of fun (i : Fin n) (k : Fin n) => x (e k) i) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hdet))
  have hQ : IsUnit (Matrix.of fun (k : Fin n) (j : Fin n) => y (e k) j) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right hdet)
  have hD : IsUnit (Matrix.diagonal fun k => s * a (e k) + t * b (e k)).det :=
    isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hdet)
  rw [Matrix.det_diagonal] at hD
  have hrest : (Finset.univ \ s').card ≤ n / 2 := by
    rw [Finset.card_sdiff_of_subset hs', hcard]
    rw [Finset.card_univ]
    omega
  obtain ⟨u, v, α, β, hα, hβ⟩ := exists_pad (Finset.univ \ s') hrest a b x y
  refine ⟨_, _, fun k => a (e k), fun k => b (e k), u, v, α, β, hP, hQ, ?_, ?_, s, t,
    fun k => Finset.prod_ne_zero_iff.mp hD.ne_zero k (Finset.mem_univ k)⟩
  · rw [← sum_eq_mul_diag_mul s' e a x y, ← hα, add_comm, Finset.sum_sdiff hs']
    exact hA
  · rw [← sum_eq_mul_diag_mul s' e b x y, ← hβ, add_comm, Finset.sum_sdiff hs']
    exact hB

end Regular

section Abstract

open Matrix

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem PRank.add {r r' : ℕ} {A B A' B' : V →ₗ[ℂ] W} (h : PRank r A B) (h' : PRank r' A' B') :
    PRank (r + r') (A + A') (B + B') := by
  obtain ⟨ι, _, a, b, ψ, u, hc, rfl, rfl⟩ := h
  obtain ⟨ι', _, a', b', ψ', u', hc', rfl, rfl⟩ := h'
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim b b', Sum.elim ψ ψ', Sum.elim u u',
    ?_, ?_, ?_⟩
  · rw [Fintype.card_sum]
    omega
  · rw [Fintype.sum_sum_type]
    rfl
  · rw [Fintype.sum_sum_type]
    rfl

/-- A pencil of rank at most `r` between quotients lifts to one between the spaces, vanishing
on the submodule that is divided out. -/
theorem PRank.lift {p : Submodule ℂ V} {q : Submodule ℂ W} {r : ℕ}
    {RA RB : (V ⧸ p) →ₗ[ℂ] (W ⧸ q)} (h : PRank r RA RB) :
    ∃ SA SB : V →ₗ[ℂ] W, PRank r SA SB ∧ (∀ v, q.mkQ (SA v) = RA (p.mkQ v)) ∧
      (∀ v, q.mkQ (SB v) = RB (p.mkQ v)) ∧ (∀ v ∈ p, SA v = 0) ∧ (∀ v ∈ p, SB v = 0) := by
  obtain ⟨ι, _, a, b, ψ, u, hc, rfl, rfl⟩ := h
  choose u' hu' using fun i => q.mkQ_surjective (u i)
  refine ⟨∑ i, a i • (ψ i ∘ₗ p.mkQ).smulRight (u' i), ∑ i, b i • (ψ i ∘ₗ p.mkQ).smulRight (u' i),
    ⟨ι, inferInstance, a, b, fun i => ψ i ∘ₗ p.mkQ, u', hc, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro v
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, map_sum, map_smul, hu']
  · intro v
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, map_sum, map_smul, hu']
  · intro v hv
    have h0 : p.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero p).mpr hv
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, h0, map_zero, zero_smul, smul_zero, Finset.sum_const_zero]
  · intro v hv
    have h0 : p.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero p).mpr hv
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, h0, map_zero, zero_smul, smul_zero, Finset.sum_const_zero]

/-- `DP r A B`: in suitable bases of `V` and `W` (indexed by the same type) the pencil `(A, B)`
is diagonal, up to a pencil of rank at most `r`. -/
def DP (r : ℕ) (A B : V →ₗ[ℂ] W) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (bV : Basis ι ℂ V) (bW : Basis ι ℂ W) (a b : ι → ℂ)
    (RA RB : V →ₗ[ℂ] W), PRank r RA RB ∧
      (∀ i, A (bV i) = a i • bW i + RA (bV i)) ∧ (∀ i, B (bV i) = b i • bW i + RB (bV i))

theorem DP.mono {r r' : ℕ} {A B : V →ₗ[ℂ] W} (h : DP r A B) (hr : r ≤ r') : DP r' A B := by
  obtain ⟨ι, hι, bV, bW, a, b, RA, RB, hR, hA, hB⟩ := h
  exact ⟨ι, hι, bV, bW, a, b, RA, RB, hR.mono hr, hA, hB⟩

/-- From a matrix decomposition `P * diagonal * Q + rank-one terms` in some bases to bases in
which the pencil is diagonal up to the rank-one terms. -/
theorem basis_data_of_matrix {d r : ℕ} (bV0 : Basis (Fin d) ℂ V) (bW0 : Basis (Fin d) ℂ W)
    (A B : V →ₗ[ℂ] W) (P Q : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d → ℂ)
    (u v : Fin r → Fin d → ℂ) (α β : Fin r → ℂ) (hP : IsUnit P) (hQ : IsUnit Q)
    (hA : LinearMap.toMatrix bV0 bW0 A =
      P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j))
    (hB : LinearMap.toMatrix bV0 bW0 B =
      P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j)) :
    ∃ (bV : Basis (Fin d) ℂ V) (bW : Basis (Fin d) ℂ W) (RA RB : V →ₗ[ℂ] W), PRank r RA RB ∧
      (∀ i, A (bV i) = a i • bW i + RA (bV i)) ∧ (∀ i, B (bV i) = b i • bW i + RB (bV i)) := by
  classical
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hQi : IsUnit (Q⁻¹).det := Matrix.isUnit_nonsing_inv_det Q hQd
  let ψ : Fin r → V →ₗ[ℂ] ℂ := fun j => bV0.constr ℂ (fun k => v j k)
  let U : Fin r → W := fun j => ∑ i, u j i • bW0 i
  have key : ∀ c : Fin r → ℂ, Matrix.toLin bV0 bW0 (∑ j, c j • Matrix.vecMulVec (u j) (v j)) =
      ∑ j, c j • (ψ j).smulRight (U j) := by
    intro c
    refine bV0.ext fun k => ?_
    rw [Matrix.toLin_self]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, ψ, U,
      Basis.constr_basis, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  have diag : ∀ (c : Fin d → ℂ) (i : Fin d),
      Matrix.toLin bV0 bW0 (P * Matrix.diagonal c * Q) (Matrix.toLin bV0 bV0 Q⁻¹ (bV0 i)) =
        c i • Matrix.toLin bW0 bW0 P (bW0 i) := by
    intro c i
    rw [← Matrix.toLin_mul_apply, Matrix.mul_nonsing_inv_cancel_right _ _ hQd, Matrix.toLin_self,
      Matrix.toLin_self, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, smul_smul, mul_comm]
  refine ⟨bV0.map (Matrix.toLinearEquiv bV0 Q⁻¹ hQi), bW0.map (Matrix.toLinearEquiv bW0 P hPd),
    Matrix.toLin bV0 bW0 (∑ j, α j • Matrix.vecMulVec (u j) (v j)),
    Matrix.toLin bV0 bW0 (∑ j, β j • Matrix.vecMulVec (u j) (v j)),
    ⟨Fin r, inferInstance, α, β, ψ, U, by simp, key α, key β⟩, ?_, ?_⟩
  · intro i
    have h1 : A = Matrix.toLin bV0 bW0 (P * Matrix.diagonal a * Q) +
        Matrix.toLin bV0 bW0 (∑ j, α j • Matrix.vecMulVec (u j) (v j)) := by
      rw [← map_add, ← hA, Matrix.toLin_toMatrix]
    conv_lhs => rw [h1]
    rw [LinearMap.add_apply, Basis.map_apply, Basis.map_apply, Matrix.toLinearEquiv_apply,
      Matrix.toLinearEquiv_apply, diag a i]
  · intro i
    have h1 : B = Matrix.toLin bV0 bW0 (P * Matrix.diagonal b * Q) +
        Matrix.toLin bV0 bW0 (∑ j, β j • Matrix.vecMulVec (u j) (v j)) := by
      rw [← map_add, ← hB, Matrix.toLin_toMatrix]
    conv_lhs => rw [h1]
    rw [LinearMap.add_apply, Basis.map_apply, Basis.map_apply, Matrix.toLinearEquiv_apply,
      Matrix.toLinearEquiv_apply, diag b i]

/-- A statement about all pencils of `d × d` matrices transfers to pencils between spaces of
dimension `d`. -/
theorem DP_of_matrices {d : ℕ} [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hV : finrank ℂ V = d) (hW : finrank ℂ W = d) (A B : V →ₗ[ℂ] W)
    (h : ∀ A' B' : Matrix (Fin d) (Fin d) ℂ,
      ∃ (P Q : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d → ℂ) (u v : Fin (d / 2) → Fin d → ℂ)
        (α β : Fin (d / 2) → ℂ), IsUnit P ∧ IsUnit Q ∧
        A' = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
        B' = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j)) :
    DP (d / 2) A B := by
  classical
  let bV0 : Basis (Fin d) ℂ V := Module.finBasisOfFinrankEq ℂ V hV
  let bW0 : Basis (Fin d) ℂ W := Module.finBasisOfFinrankEq ℂ W hW
  obtain ⟨P, Q, a, b, u, v, α, β, hP, hQ, hA, hB⟩ :=
    h (LinearMap.toMatrix bV0 bW0 A) (LinearMap.toMatrix bV0 bW0 B)
  obtain ⟨bV, bW, RA, RB, hR, h1, h2⟩ :=
    basis_data_of_matrix bV0 bW0 A B P Q a b u v α β hP hQ hA hB
  exact ⟨Fin d, inferInstance, bV, bW, a, b, RA, RB, hR, h1, h2⟩

/-- The regular case for a pencil between spaces of the same dimension `d`. -/
theorem regular_abs {d : ℕ} [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hV : finrank ℂ V = d) (hW : finrank ℂ W = d) (A B : V →ₗ[ℂ] W) (t : ℂ)
    (hinj : Function.Injective (A + t • B)) :
    ∃ (bV : Basis (Fin d) ℂ V) (bW : Basis (Fin d) ℂ W) (a b : Fin d → ℂ) (RA RB : V →ₗ[ℂ] W),
      PRank (d / 2) RA RB ∧ (∀ i, A (bV i) = a i • bW i + RA (bV i)) ∧
      (∀ i, B (bV i) = b i • bW i + RB (bV i)) ∧ ∃ s₀ t₀ : ℂ, ∀ k, s₀ * a k + t₀ * b k ≠ 0 := by
  classical
  let bV0 : Basis (Fin d) ℂ V := Module.finBasisOfFinrankEq ℂ V hV
  let bW0 : Basis (Fin d) ℂ W := Module.finBasisOfFinrankEq ℂ W hW
  have hbij : Function.Bijective (A + t • B) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hV.trans hW.symm)).mp hinj⟩
  have hunit := (LinearEquiv.ofBijective (A + t • B) hbij).isUnit_det bV0 bW0
  have hreg : ∃ s t : ℂ, IsUnit (s • LinearMap.toMatrix bV0 bW0 A + t • LinearMap.toMatrix bV0 bW0 B) := by
    refine ⟨1, t, (Matrix.isUnit_iff_isUnit_det _).mpr ?_⟩
    have e : (1 : ℂ) • LinearMap.toMatrix bV0 bW0 A + t • LinearMap.toMatrix bV0 bW0 B =
        LinearMap.toMatrix bV0 bW0 ((LinearEquiv.ofBijective (A + t • B) hbij : V ≃ₗ[ℂ] W) : V →ₗ[ℂ] W) := by
      rw [one_smul, ← map_smul, ← map_add]
      rfl
    rw [e]
    exact hunit
  obtain ⟨P, Q, a, b, u, v, α, β, hP, hQ, hA, hB, hne⟩ := regular_pencil d _ _ hreg
  obtain ⟨bV, bW, RA, RB, hR, h1, h2⟩ :=
    basis_data_of_matrix bV0 bW0 A B P Q a b u v α β hP hQ hA hB
  exact ⟨bV, bW, a, b, RA, RB, hR, h1, h2, hne⟩

/-- From bases in which the pencil is diagonal up to rank `r` back to matrices. -/
theorem matrix_of_DP {n r : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : DP r (Matrix.toLin' A) (Matrix.toLin' B)) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) (u v : Fin r → Fin n → ℂ)
      (α β : Fin r → ℂ), IsUnit P ∧ IsUnit Q ∧
      A = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
      B = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j) := by
  classical
  obtain ⟨ι, _, bV, bW, a, b, RA, RB, hR, hA, hB⟩ := h
  have hcard : Fintype.card ι = n := by
    rw [← Module.finrank_eq_card_basis bV, Module.finrank_fin_fun]
  let e : Fin n ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => bW (e k) i
  let S : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => bV (e k) i
  have hPc : P.col = bW ∘ e := by
    ext k i
    rfl
  have hSc : S.col = bV ∘ e := by
    ext k i
    rfl
  have hPu : IsUnit P := (Matrix.linearIndependent_cols_iff_isUnit (K := ℂ)).mp
    (by rw [hPc]; exact bW.linearIndependent.comp e e.injective)
  have hSu : IsUnit S := (Matrix.linearIndependent_cols_iff_isUnit (K := ℂ)).mp
    (by rw [hSc]; exact bV.linearIndependent.comp e e.injective)
  have hSd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSu
  have hRm : PRank r (Matrix.toLin' (LinearMap.toMatrix' RA))
      (Matrix.toLin' (LinearMap.toMatrix' RB)) := by
    rw [Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    exact hR
  obtain ⟨κ, _, α', β', x, y, hκ, hRA, hRB⟩ := mat_of_prank _ _ hRm
  have hκ' : (Finset.univ : Finset κ).card ≤ r := by
    rw [Finset.card_univ]
    exact hκ
  obtain ⟨u, v, α, β, hα, hβ⟩ := exists_pad (m := r) (Finset.univ : Finset κ) hκ' α' β' x y
  have key : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (R : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (c : ι → ℂ),
      (∀ i, Matrix.toLin' M (bV i) = c i • bW i + R (bV i)) →
      M = P * Matrix.diagonal (fun k => c (e k)) * S⁻¹ + LinearMap.toMatrix' R := by
    intro M R c hM
    have h1 : (M - LinearMap.toMatrix' R) * S = P * Matrix.diagonal (fun k => c (e k)) := by
      ext i k
      have h2 := congrFun (hM (e k)) i
      have h3 : R (bV (e k)) = LinearMap.toMatrix' R *ᵥ bV (e k) := by
        rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
      rw [Matrix.toLin'_apply, h3] at h2
      have h4 : ((M - LinearMap.toMatrix' R) * S) i k =
          ((M - LinearMap.toMatrix' R) *ᵥ bV (e k)) i := rfl
      rw [h4, Matrix.sub_mulVec, Pi.sub_apply, h2, Matrix.mul_diagonal]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right, P,
        Matrix.of_apply, mul_comm]
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hSd, sub_add_cancel]
  refine ⟨P, S⁻¹, fun k => a (e k), fun k => b (e k), u, v, α, β, hPu,
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det S hSd), ?_, ?_⟩
  · rw [← hα, ← hRA]
    exact key A RA a hA
  · rw [← hβ, ← hRB]
    exact key B RB b hB

theorem finrank_quot_span_singleton [FiniteDimensional ℂ V] {v0 : V} (hv0 : v0 ≠ 0) :
    finrank ℂ (V ⧸ Submodule.span ℂ {v0}) + 1 = finrank ℂ V := by
  have h1 := (Submodule.span ℂ {v0}).finrank_quotient_add_finrank
  have h2 : finrank ℂ (Submodule.span ℂ {v0}) = 1 := finrank_span_singleton hv0
  omega

theorem finrank_ker_functional [FiniteDimensional ℂ W] {φ : W →ₗ[ℂ] ℂ} (hφ : φ ≠ 0) :
    finrank ℂ (LinearMap.ker φ) + 1 = finrank ℂ W := by
  obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
    by_contra h
    exact hφ (LinearMap.ext fun x => by_contra fun hx => h ⟨x, hx⟩)
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have hsurj : Function.Surjective φ := fun c => ⟨(c / φ w0) • w0, by simp [hw0]⟩
  have h2 : finrank ℂ (LinearMap.range φ) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self]
  omega

/-- A common kernel vector together with a common left kernel functional: the pencil is a
smaller pencil plus a zero block. -/
theorem DP_of_zero_block [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (A B : V →ₗ[ℂ] W)
    (v0 : V) (hv0 : v0 ≠ 0) (hA0 : A v0 = 0) (hB0 : B v0 = 0) (φ : W →ₗ[ℂ] ℂ) (hφ : φ ≠ 0)
    (hφA : ∀ x, φ (A x) = 0) (hφB : ∀ x, φ (B x) = 0) (r : ℕ)
    (ih : ∀ A' B' : (V ⧸ Submodule.span ℂ {v0}) →ₗ[ℂ] LinearMap.ker φ, DP r A' B') :
    DP r A B := by
  classical
  have hpA : Submodule.span ℂ {v0} ≤ LinearMap.ker
      (A.codRestrict (LinearMap.ker φ) (fun x => LinearMap.mem_ker.mpr (hφA x))) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact LinearMap.mem_ker.mpr (Subtype.ext hA0)
  have hpB : Submodule.span ℂ {v0} ≤ LinearMap.ker
      (B.codRestrict (LinearMap.ker φ) (fun x => LinearMap.mem_ker.mpr (hφB x))) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact LinearMap.mem_ker.mpr (Subtype.ext hB0)
  obtain ⟨ι, _, bV', bW', a, b, RA', RB', hR, hA', hB'⟩ :=
    ih ((Submodule.span ℂ {v0}).liftQ _ hpA) ((Submodule.span ℂ {v0}).liftQ _ hpB)
  choose v' hv' using fun i => (Submodule.span ℂ {v0}).mkQ_surjective (bV' i)
  obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
    by_contra h
    exact hφ (LinearMap.ext fun x => by_contra fun hx => h ⟨x, hx⟩)
  have hliV0 : LinearIndependent ℂ (Sum.elim (fun _ : Unit => v0) v') := by
    have h1 : LinearIndependent ℂ (fun _ : Unit =>
        (⟨v0, Submodule.mem_span_singleton_self v0⟩ : Submodule.span ℂ {v0})) := by
      rw [linearIndependent_unique_iff]
      intro h
      exact hv0 (congrArg Subtype.val h)
    have h2 : LinearIndependent ℂ
        (Submodule.Quotient.mk (p := Submodule.span ℂ {v0}) ∘ v') := by
      have h3 : Submodule.Quotient.mk (p := Submodule.span ℂ {v0}) ∘ v' = bV' :=
        funext fun i => hv' i
      rw [h3]
      exact bV'.linearIndependent
    exact LinearIndependent.sumElim_of_quotient h1 v' h2
  have hliV : LinearIndependent ℂ (Sum.elim v' (fun _ : Unit => v0)) := by
    have h := hliV0.comp (Equiv.sumComm ι Unit) (Equiv.sumComm ι Unit).injective
    have e : (Sum.elim (fun _ : Unit => v0) v' ∘ ⇑(Equiv.sumComm ι Unit)) =
        Sum.elim v' (fun _ : Unit => v0) := by
      funext x
      cases x <;> rfl
    rw [e] at h
    exact h
  have hliW : LinearIndependent ℂ (Sum.elim (fun i => (bW' i : W)) (fun _ : Unit => w0)) := by
    have h2 : LinearIndependent ℂ
        (Submodule.Quotient.mk (p := LinearMap.ker φ) ∘ (fun _ : Unit => w0)) := by
      rw [linearIndependent_unique_iff]
      intro h
      exact hw0 (LinearMap.mem_ker.mp ((Submodule.Quotient.mk_eq_zero _).mp h))
    exact LinearIndependent.sumElim_of_quotient bW'.linearIndependent _ h2
  have hcV : Fintype.card (ι ⊕ Unit) = finrank ℂ V := by
    have h1 := finrank_quot_span_singleton hv0
    have h3 := Module.finrank_eq_card_basis bV'
    rw [Fintype.card_sum, Fintype.card_unit]
    omega
  have hcW : Fintype.card (ι ⊕ Unit) = finrank ℂ W := by
    have h1 := finrank_ker_functional hφ
    have h3 := Module.finrank_eq_card_basis bW'
    rw [Fintype.card_sum, Fintype.card_unit]
    omega
  have h0 : (Submodule.span ℂ {v0}).mkQ v0 = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self v0)
  refine ⟨ι ⊕ Unit, inferInstance, basisOfLinearIndependentOfCardEqFinrank hliV hcV,
    basisOfLinearIndependentOfCardEqFinrank hliW hcW, Sum.elim a (fun _ => 0),
    Sum.elim b (fun _ => 0), (LinearMap.ker φ).subtype ∘ₗ RA' ∘ₗ (Submodule.span ℂ {v0}).mkQ,
    (LinearMap.ker φ).subtype ∘ₗ RB' ∘ₗ (Submodule.span ℂ {v0}).mkQ,
    (hR.comp_right _).comp_left _, ?_, ?_⟩
  · rintro (i | u)
    · have h2 := congrArg Subtype.val (hA' i)
      rw [← hv' i] at h2
      simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Sum.elim_inl,
        LinearMap.comp_apply, Submodule.subtype_apply]
      exact h2
    · simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Sum.elim_inr,
        LinearMap.comp_apply, h0, map_zero, zero_smul, add_zero, hA0]
  · rintro (i | u)
    · have h2 := congrArg Subtype.val (hB' i)
      rw [← hv' i] at h2
      simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Sum.elim_inl,
        LinearMap.comp_apply, Submodule.subtype_apply]
      exact h2
    · simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Sum.elim_inr,
        LinearMap.comp_apply, h0, map_zero, zero_smul, add_zero, hB0]

/-- Gluing two diagonal blocks of a block triangular pencil whose coefficient pairs are pairwise
independent across the blocks: a Cramer solve for each pair of indices. -/
theorem glue {I J : Type} [Fintype I] [Fintype J] (A B : V →ₗ[ℂ] W) (x : I → V) (wh : I → W)
    (a b : I → ℂ) (v' : J → V) (w' : J → W) (a' b' : J → ℂ)
    (hA : ∀ i, A (x i) = a i • wh i) (hB : ∀ i, B (x i) = b i • wh i)
    (hA' : ∀ j, A (v' j) - a' j • w' j ∈ Submodule.span ℂ (Set.range wh))
    (hB' : ∀ j, B (v' j) - b' j • w' j ∈ Submodule.span ℂ (Set.range wh))
    (hne : ∀ i j, a i * b' j - a' j * b i ≠ 0) :
    ∃ Y X : J → I → ℂ, ∀ j,
      A (v' j - ∑ i, Y j i • x i) = a' j • (w' j + ∑ i, X j i • wh i) ∧
      B (v' j - ∑ i, Y j i • x i) = b' j • (w' j + ∑ i, X j i • wh i) := by
  choose cA hcA using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hA' j)
  choose cB hcB using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hB' j)
  refine ⟨fun j i => (cA j i * b' j - a' j * cB j i) / (a i * b' j - a' j * b i),
    fun j i => (a i * cB j i - b i * cA j i) / (a i * b' j - a' j * b i), fun j => ⟨?_, ?_⟩⟩
  · have e1 : A (v' j) = a' j • w' j + ∑ i, cA j i • wh i := by
      rw [hcA j]
      abel
    rw [map_sub, map_sum, e1, smul_add, Finset.smul_sum, add_sub_assoc]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hA, smul_smul, smul_smul, ← sub_smul]
    congr 1
    rw [div_mul_eq_mul_div, mul_div_assoc', sub_eq_iff_eq_add, ← add_div, eq_div_iff (hne i j)]
    ring
  · have e1 : B (v' j) = b' j • w' j + ∑ i, cB j i • wh i := by
      rw [hcB j]
      abel
    rw [map_sub, map_sum, e1, smul_add, Finset.smul_sum, add_sub_assoc]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hB, smul_smul, smul_smul, ← sub_smul]
    congr 1
    rw [div_mul_eq_mul_div, mul_div_assoc', sub_eq_iff_eq_add, ← add_div, eq_div_iff (hne i j)]
    ring

/-- Span of the eigenvectors of the pencil whose parameter avoids the finite set `F`. -/
def ES (A B : V →ₗ[ℂ] W) (F : Finset ℂ) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ t : ℂ, t ∉ F ∧ A x + t • B x = 0}

theorem ES_anti (A B : V →ₗ[ℂ] W) {F F' : Finset ℂ} (h : F ⊆ F') : ES A B F' ≤ ES A B F :=
  Submodule.span_mono fun _ ⟨t, ht, hx⟩ => ⟨t, fun h' => ht (h h'), hx⟩

/-- For `F` large enough the span of the eigenvectors with parameter outside `F` is constant. -/
theorem exists_stable [FiniteDimensional ℂ V] (A B : V →ₗ[ℂ] W) :
    ∃ F0 : Finset ℂ, ∀ F : Finset ℂ, F0 ⊆ F → ES A B F = ES A B F0 := by
  classical
  have hne : ∃ d, ∃ F : Finset ℂ, finrank ℂ (ES A B F) = d := ⟨_, ∅, rfl⟩
  obtain ⟨F0, hF0⟩ := Nat.find_spec hne
  refine ⟨F0, fun F hF => ?_⟩
  refine Submodule.eq_of_le_of_finrank_le (ES_anti A B hF) ?_
  rw [hF0]
  exact Nat.find_min' hne ⟨F, rfl⟩

theorem exists_eigen_family [FiniteDimensional ℂ V] (A B : V →ₗ[ℂ] W) (F : Finset ℂ) :
    ∃ (I : Type) (_ : Fintype I) (x : I → V) (t : I → ℂ), LinearIndependent ℂ x ∧
      Submodule.span ℂ (Set.range x) = ES A B F ∧
      ∀ i, t i ∉ F ∧ A (x i) + t i • B (x i) = 0 := by
  classical
  obtain ⟨b, hbS, hbspan, hli⟩ :=
    exists_linearIndependent ℂ {x : V | ∃ t : ℂ, t ∉ F ∧ A x + t • B x = 0}
  have hfin : Finite b := hli.finite
  have hft : Fintype b := Fintype.ofFinite b
  choose t ht using fun i : b => hbS i.2
  exact ⟨b, hft, Subtype.val, t, hli, by rw [Subtype.range_coe]; exact hbspan, ht⟩

theorem span_range_smul {I : Type} (c : I → ℂ) (hc : ∀ i, c i ≠ 0) (w : I → W) :
    Submodule.span ℂ (Set.range fun i => c i • w i) = Submodule.span ℂ (Set.range w) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h : w i = (c i)⁻¹ • (c i • w i) := by
      rw [smul_smul, inv_mul_cancel₀ (hc i), one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Without a common kernel vector, the images under `B` of independent eigenvectors with
nonzero parameters span at least half of their number of dimensions. -/
theorem card_le_two_mul [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (A B : V →ₗ[ℂ] W)
    (hk : ∀ v, A v = 0 → B v = 0 → v = 0) {I : Type} [Fintype I] (x : I → V) (t : I → ℂ)
    (hli : LinearIndependent ℂ x) (ht : ∀ i, t i ≠ 0)
    (hx : ∀ i, A (x i) + t i • B (x i) = 0) :
    Fintype.card I ≤ 2 * finrank ℂ (Submodule.span ℂ (Set.range fun i => B (x i))) := by
  classical
  have hrB : LinearMap.range (Fintype.linearCombination ℂ (fun i => B (x i))) =
      Submodule.span ℂ (Set.range fun i => B (x i)) := Fintype.range_linearCombination ..
  have hrA : LinearMap.range (Fintype.linearCombination ℂ (fun i => A (x i))) =
      Submodule.span ℂ (Set.range fun i => B (x i)) := by
    rw [Fintype.range_linearCombination]
    have h : (fun i => A (x i)) = fun i => (-(t i)) • B (x i) := funext fun i => by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left (hx i)
    rw [h]
    exact span_range_smul _ (fun i => neg_ne_zero.mpr (ht i)) _
  have hdisj : LinearMap.ker (Fintype.linearCombination ℂ (fun i => A (x i))) ⊓
      LinearMap.ker (Fintype.linearCombination ℂ (fun i => B (x i))) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro c hc
    obtain ⟨hcA, hcB⟩ := Submodule.mem_inf.mp hc
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hcA hcB
    have h1 : A (∑ i, c i • x i) = 0 := by
      rw [map_sum, ← hcA]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have h2 : B (∑ i, c i • x i) = 0 := by
      rw [map_sum, ← hcB]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    exact funext fun i => Fintype.linearIndependent_iff.mp hli c (hk _ h1 h2) i
  have hA := LinearMap.finrank_range_add_finrank_ker
    (Fintype.linearCombination ℂ (fun i => A (x i)))
  have hB := LinearMap.finrank_range_add_finrank_ker
    (Fintype.linearCombination ℂ (fun i => B (x i)))
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (Fintype.linearCombination ℂ (fun i => A (x i))))
    (LinearMap.ker (Fintype.linearCombination ℂ (fun i => B (x i))))
  rw [hdisj, finrank_bot, add_zero] at hs
  have hle := Submodule.finrank_le
    (LinearMap.ker (Fintype.linearCombination ℂ (fun i => A (x i))) ⊔
      LinearMap.ker (Fintype.linearCombination ℂ (fun i => B (x i))))
  rw [Module.finrank_fintype_fun_eq_card] at hA hB hle
  rw [hrA] at hA
  rw [hrB] at hB
  omega

/-- The main case: a pencil between spaces of the same dimension without a common kernel vector
is diagonal up to rank at most half the dimension. -/
theorem DP_of_no_kernel [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (A B : V →ₗ[ℂ] W)
    (hdim : finrank ℂ V = finrank ℂ W) (hk : ∀ v, A v = 0 → B v = 0 → v = 0) :
    DP (finrank ℂ V / 2) A B := by
  classical
  obtain ⟨F0, hF0⟩ := exists_stable A B
  obtain ⟨V1, hV1⟩ : ∃ V1 : Submodule ℂ V, V1 = ES A B F0 := ⟨_, rfl⟩
  obtain ⟨W1, hW1⟩ : ∃ W1 : Submodule ℂ W, W1 = V1.map B := ⟨_, rfl⟩
  -- a first family of eigenvectors, used to choose the parameter `ts`
  obtain ⟨I0, _, x0, t0, -, hsp0, hx0⟩ := exists_eigen_family A B F0
  rw [← hV1] at hsp0
  obtain ⟨ts, hts⟩ := Infinite.exists_notMem_finset (F0 ∪ Finset.univ.image t0)
  have hts0 : ts ∉ F0 := fun h => hts (Finset.mem_union_left _ h)
  have hts1 : ∀ i, ts ≠ t0 i := fun i h =>
    hts (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h.symm⟩))
  obtain ⟨G, hG⟩ : ∃ G : V →ₗ[ℂ] W, G = A + ts • B := ⟨_, rfl⟩
  have hGx : ∀ x, G x = A x + ts • B x := fun x => by
    rw [hG]
    rfl
  have hkerG : LinearMap.ker G ≤ V1 := by
    intro x hx
    rw [hV1]
    exact Submodule.subset_span ⟨ts, hts0, by rw [← hGx]; exact LinearMap.mem_ker.mp hx⟩
  have hGV1 : V1.map G = W1 := by
    rw [hW1, ← hsp0, Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
    have h : (G ∘ x0) = fun i => (ts - t0 i) • (B ∘ x0) i := funext fun i => by
      have h1 := (hx0 i).2
      rw [Function.comp_apply, Function.comp_apply, hGx, sub_smul,
        eq_neg_of_add_eq_zero_left h1]
      abel
    rw [h]
    exact span_range_smul _ (fun i => sub_ne_zero.mpr (hts1 i)) _
  have hAV1 : ∀ x ∈ V1, A x ∈ W1 := by
    have h : V1 ≤ W1.comap A := by
      rw [hV1]
      refine Submodule.span_le.mpr ?_
      rintro x ⟨t, ht, hx⟩
      have hxV : x ∈ V1 := by
        rw [hV1]
        exact Submodule.subset_span ⟨t, ht, hx⟩
      show A x ∈ W1
      rw [eq_neg_of_add_eq_zero_left hx, ← neg_smul, hW1]
      exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hxV)
    exact fun x hx => h hx
  -- the complement `W3` of the range of `G` and the enlarged target `W1'`
  obtain ⟨W3, hW3⟩ := Submodule.exists_isCompl (LinearMap.range G)
  obtain ⟨W1', hW1'⟩ : ∃ W1' : Submodule ℂ W, W1' = W1 ⊔ W3 := ⟨_, rfl⟩
  have hW1le : W1 ≤ W1' := by
    rw [hW1']
    exact le_sup_left
  have hW3le : W3 ≤ W1' := by
    rw [hW1']
    exact le_sup_right
  have hAq : V1 ≤ W1'.comap A := fun x hx => hW1le (hAV1 x hx)
  have hBq : V1 ≤ W1'.comap B := fun x hx =>
    hW1le (by rw [hW1]; exact Submodule.mem_map_of_mem hx)
  have hGinv : ∀ x, G x ∈ W1' → x ∈ V1 := by
    intro x hx
    rw [hW1', Submodule.mem_sup] at hx
    obtain ⟨w1, hw1, w3, hw3, hsum⟩ := hx
    rw [← hGV1] at hw1
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hw1
    have h4 : G (x - y) = w3 := by
      rw [map_sub, ← hsum]
      abel
    have h3 : w3 ∈ LinearMap.range G ⊓ W3 := Submodule.mem_inf.mpr ⟨⟨x - y, h4⟩, hw3⟩
    rw [hW3.inf_eq_bot, Submodule.mem_bot] at h3
    rw [h3] at h4
    have h5 := hkerG (LinearMap.mem_ker.mpr h4)
    have h6 : x = (x - y) + y := by abel
    rw [h6]
    exact V1.add_mem h5 hy
  -- the quotient pencil is regular
  obtain ⟨Aq, hAqdef⟩ : ∃ Aq : (V ⧸ V1) →ₗ[ℂ] (W ⧸ W1'), Aq = V1.mapQ W1' A hAq := ⟨_, rfl⟩
  obtain ⟨Bq, hBqdef⟩ : ∃ Bq : (V ⧸ V1) →ₗ[ℂ] (W ⧸ W1'), Bq = V1.mapQ W1' B hBq := ⟨_, rfl⟩
  have hAqx : ∀ x, Aq (V1.mkQ x) = W1'.mkQ (A x) := fun x => by
    rw [hAqdef]
    rfl
  have hBqx : ∀ x, Bq (V1.mkQ x) = W1'.mkQ (B x) := fun x => by
    rw [hBqdef]
    rfl
  have hGq : ∀ x, (Aq + ts • Bq) (V1.mkQ x) = W1'.mkQ (G x) := fun x => by
    rw [LinearMap.add_apply, LinearMap.smul_apply, hAqx, hBqx, hGx, map_add, map_smul]
  have hinj : Function.Injective (Aq + ts • Bq) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro xq hxq
    obtain ⟨x, rfl⟩ := V1.mkQ_surjective xq
    rw [LinearMap.mem_ker, hGq] at hxq
    exact (Submodule.Quotient.mk_eq_zero V1).mpr
      (hGinv x ((Submodule.Quotient.mk_eq_zero W1').mp hxq))
  have hsurj : Function.Surjective (Aq + ts • Bq) := by
    intro wq
    obtain ⟨w, rfl⟩ := W1'.mkQ_surjective wq
    have hw : w ∈ LinearMap.range G ⊔ W3 := by
      rw [hW3.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨g, hg, w3, hw3, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hg
    have h0 : W1'.mkQ w3 = 0 := (Submodule.Quotient.mk_eq_zero W1').mpr (hW3le hw3)
    refine ⟨V1.mkQ x, ?_⟩
    rw [hGq, map_add, h0, add_zero]
  have hdq : finrank ℂ (V ⧸ V1) = finrank ℂ (W ⧸ W1') :=
    (LinearEquiv.ofBijective (Aq + ts • Bq) ⟨hinj, hsurj⟩).finrank_eq
  have hqV := V1.finrank_quotient_add_finrank
  have hqW := W1'.finrank_quotient_add_finrank
  have hW1'dim : finrank ℂ W1' = finrank ℂ V1 := by omega
  have hW1W3 : finrank ℂ W1' = finrank ℂ W1 + finrank ℂ W3 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W1 W3
    have h2 : W1 ⊓ W3 = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      obtain ⟨hw1, hw3⟩ := Submodule.mem_inf.mp hw
      have h3 : w ∈ LinearMap.range G ⊓ W3 := by
        refine Submodule.mem_inf.mpr ⟨?_, hw3⟩
        rw [← hGV1] at hw1
        exact LinearMap.map_le_range hw1
      rw [hW3.inf_eq_bot] at h3
      exact (Submodule.mem_bot ℂ).mp h3
    rw [h2, finrank_bot, add_zero, ← hW1'] at h1
    exact h1
  obtain ⟨bVq, bWq, a', b', RAq, RBq, hRq, hAq', hBq', s₀, t₀, hne⟩ :=
    regular_abs (d := finrank ℂ (V ⧸ V1)) rfl hdq.symm Aq Bq ts hinj
  obtain ⟨R2A, R2B, hR2, hR2A, hR2B, hR2A0, hR2B0⟩ := hRq.lift
  choose v' hv' using fun j => V1.mkQ_surjective (bVq j)
  choose w' hw' using fun j => W1'.mkQ_surjective (bWq j)
  -- the finite set of parameters to avoid
  obtain ⟨F, hF⟩ : ∃ F : Finset ℂ,
      F = F0 ∪ ({0} ∪ Finset.univ.image fun j => -(a' j) / b' j) := ⟨_, rfl⟩
  have hF0F : F0 ⊆ F := by
    rw [hF]
    exact Finset.subset_union_left
  have hFz : ∀ t, t ∉ F → t ≠ 0 := by
    intro t ht h
    apply ht
    rw [hF, h]
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_singleton_self 0))
  have hFne : ∀ t, t ∉ F → ∀ j, a' j + t * b' j ≠ 0 := by
    intro t ht j h0
    by_cases hb : b' j = 0
    · have h1 := hne j
      rw [hb, mul_zero, add_zero] at h1 h0
      rw [h0, mul_zero] at h1
      exact h1 rfl
    · apply ht
      rw [hF]
      refine Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩))
      rw [div_eq_iff hb]
      linear_combination -h0
  -- the eigenvectors spanning `V1`, with parameters outside `F`
  obtain ⟨I, _, x, t, hli, hsp, hx⟩ := exists_eigen_family A B F
  rw [hF0 F hF0F, ← hV1] at hsp
  obtain ⟨K, sel, hsel, hselsp, hselli⟩ := exists_linearIndependent' ℂ (fun i => B (x i))
  have hfK : Fintype K := Fintype.ofInjective sel hsel
  obtain ⟨C, hfC, σ, hσl⟩ : ∃ (C : Type) (_ : Fintype C) (σ : K ⊕ C ≃ I),
      ∀ k, σ (Sum.inl k) = sel k :=
    ⟨↥(Set.range sel)ᶜ, Fintype.ofFinite _,
      (Equiv.sumCongr (Equiv.ofInjective sel hsel) (Equiv.refl _)).trans
        (Equiv.Set.sumCompl (Set.range sel)), fun k => by simp⟩
  obtain ⟨xs, hxs⟩ : ∃ xs : K ⊕ C → V, xs = x ∘ σ := ⟨_, rfl⟩
  obtain ⟨tt, htt⟩ : ∃ tt : K ⊕ C → ℂ, tt = t ∘ σ := ⟨_, rfl⟩
  have hxsli : LinearIndependent ℂ xs := by
    rw [hxs]
    exact hli.comp σ σ.injective
  have hxsV1 : ∀ k, xs k ∈ V1 := fun k => by
    rw [hxs, ← hsp]
    exact Submodule.subset_span ⟨σ k, rfl⟩
  have hxse : ∀ k, A (xs k) = (-(tt k)) • B (xs k) := fun k => by
    rw [hxs, htt, neg_smul]
    exact eq_neg_of_add_eq_zero_left (hx (σ k)).2
  have httF : ∀ k, tt k ∉ F := fun k => by
    rw [htt]
    exact (hx (σ k)).1
  have hcardI : Fintype.card I = finrank ℂ V1 := by
    rw [← hsp, finrank_span_eq_card hli]
  have hcardKC : Fintype.card K + Fintype.card C = finrank ℂ V1 := by
    rw [← hcardI, ← Fintype.card_sum]
    exact Fintype.card_congr σ
  have hW1sp : Submodule.span ℂ (Set.range fun i => B (x i)) = W1 := by
    have h : (fun i => B (x i)) = ⇑B ∘ x := rfl
    rw [h, hW1, ← hsp, Submodule.map_span, Set.range_comp]
  have hW1K : finrank ℂ W1 = Fintype.card K := by
    rw [← hW1sp, ← hselsp, finrank_span_eq_card hselli]
  have h2 := card_le_two_mul A B hk x t hli (fun i => hFz _ (hx i).1) (fun i => (hx i).2)
  rw [hW1sp, hW1K, hcardI, ← hcardKC] at h2
  have hW3C : finrank ℂ W3 = Fintype.card C := by omega
  obtain ⟨e, hesp⟩ : ∃ e : C → W, Submodule.span ℂ (Set.range e) = W3 := by
    refine ⟨fun c => (((Module.finBasisOfFinrankEq ℂ W3 hW3C).reindex
      (Fintype.equivFin C).symm) c : W), ?_⟩
    have h : (fun c => (((Module.finBasisOfFinrankEq ℂ W3 hW3C).reindex
        (Fintype.equivFin C).symm) c : W)) = ⇑W3.subtype ∘
          ⇑((Module.finBasisOfFinrankEq ℂ W3 hW3C).reindex (Fintype.equivFin C).symm) := rfl
    rw [h, Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_subtype_top]
  -- the basis `wh` of `W1'`: images of eigenvectors where possible, else the vectors `e`
  obtain ⟨wh, hwh⟩ : ∃ wh : K ⊕ C → W, wh = Sum.elim (fun k => B (xs (Sum.inl k))) e :=
    ⟨_, rfl⟩
  have hwhl : ∀ k, wh (Sum.inl k) = B (xs (Sum.inl k)) := fun k => by
    rw [hwh]
    rfl
  have hwhr : ∀ c, wh (Sum.inr c) = e c := fun c => by
    rw [hwh]
    rfl
  have hwhsp : Submodule.span ℂ (Set.range wh) = W1' := by
    have h : (fun k => B (xs (Sum.inl k))) = (fun i => B (x i)) ∘ sel := funext fun k => by
      rw [hxs]
      exact congrArg (fun i => B (x i)) (hσl k)
    rw [hwh, Set.Sum.elim_range, Submodule.span_union, hesp, hW1', h, hselsp, hW1sp]
  have hwhmem : ∀ k, wh k ∈ W1' := fun k => by
    rw [← hwhsp]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hwhli : LinearIndependent ℂ wh := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    show Fintype.card (K ⊕ C) = finrank ℂ (Submodule.span ℂ (Set.range wh))
    rw [hwhsp, hW1'dim, ← hcardKC, Fintype.card_sum]
  -- a first basis of `V`, for the coordinate functionals of the eigenvectors
  have hmkv' : (Submodule.Quotient.mk (p := V1) ∘ v') = bVq := funext fun j => hv' j
  have hxsS : LinearIndependent ℂ (fun k => (⟨xs k, hxsV1 k⟩ : V1)) :=
    LinearIndependent.of_comp V1.subtype hxsli
  have hwhS : LinearIndependent ℂ (fun k => (⟨wh k, hwhmem k⟩ : W1')) :=
    LinearIndependent.of_comp W1'.subtype hwhli
  have hcard : Fintype.card ((K ⊕ C) ⊕ Fin (finrank ℂ (V ⧸ V1))) = finrank ℂ V := by
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]
    omega
  have hli0 : LinearIndependent ℂ (Sum.elim xs v') :=
    LinearIndependent.sumElim_of_quotient hxsS v' (by rw [hmkv']; exact bVq.linearIndependent)
  obtain ⟨bV0, hbV0⟩ : ∃ bV0 : Basis ((K ⊕ C) ⊕ Fin (finrank ℂ (V ⧸ V1))) ℂ V,
      ⇑bV0 = Sum.elim xs v' :=
    ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli0 hcard,
      coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _⟩
  have hbx : ∀ k, xs k = bV0 (Sum.inl k) := fun k => by
    rw [hbV0]
    rfl
  have hbv : ∀ j, v' j = bV0 (Sum.inr j) := fun j => by
    rw [hbV0]
    rfl
  have hξ1 : ∀ c, bV0.coord (Sum.inl (Sum.inr c)) (xs (Sum.inr c)) = 1 := by
    intro c
    rw [hbx, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]
  have hξ2 : ∀ c c', c' ≠ c → bV0.coord (Sum.inl (Sum.inr c)) (xs (Sum.inr c')) = 0 := by
    intro c c' hc
    rw [hbx, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, if_neg]
    intro h
    exact hc (Sum.inr.inj (Sum.inl.inj h))
  have hξ3 : ∀ c k, bV0.coord (Sum.inl (Sum.inr c)) (xs (Sum.inl k)) = 0 := by
    intro c k
    rw [hbx, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, if_neg]
    intro h
    exact Sum.inl_ne_inr (Sum.inl.inj h)
  have hξ4 : ∀ c j, bV0.coord (Sum.inl (Sum.inr c)) (v' j) = 0 := by
    intro c j
    rw [hbv, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, if_neg]
    exact Sum.inr_ne_inl
  -- the correction of rank at most `card C` on the block of the eigenvectors
  obtain ⟨R1A, hR1A⟩ : ∃ R1A : V →ₗ[ℂ] W, R1A = ∑ c : C, (-(tt (Sum.inr c))) •
      (bV0.coord (Sum.inl (Sum.inr c))).smulRight (B (xs (Sum.inr c)) - e c) := ⟨_, rfl⟩
  obtain ⟨R1B, hR1B⟩ : ∃ R1B : V →ₗ[ℂ] W, R1B = ∑ c : C, (1 : ℂ) •
      (bV0.coord (Sum.inl (Sum.inr c))).smulRight (B (xs (Sum.inr c)) - e c) := ⟨_, rfl⟩
  have hR1 : PRank (Fintype.card C) R1A R1B := by
    rw [hR1A, hR1B]
    exact ⟨C, inferInstance, fun c => -(tt (Sum.inr c)), fun _ => 1,
      fun c => bV0.coord (Sum.inl (Sum.inr c)), fun c => B (xs (Sum.inr c)) - e c, le_rfl,
      rfl, rfl⟩
  have hR1Al : ∀ k, R1A (xs (Sum.inl k)) = 0 := by
    intro k
    rw [hR1A, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ3, zero_smul, smul_zero]
  have hR1Bl : ∀ k, R1B (xs (Sum.inl k)) = 0 := by
    intro k
    rw [hR1B, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ3, zero_smul, smul_zero]
  have hR1Ar : ∀ c, R1A (xs (Sum.inr c)) =
      (-(tt (Sum.inr c))) • (B (xs (Sum.inr c)) - e c) := by
    intro c
    rw [hR1A, LinearMap.sum_apply, Finset.sum_eq_single c]
    · rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ1, one_smul]
    · intro c' _ hc'
      rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ2 c' c hc'.symm, zero_smul,
        smul_zero]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have hR1Br : ∀ c, R1B (xs (Sum.inr c)) = (1 : ℂ) • (B (xs (Sum.inr c)) - e c) := by
    intro c
    rw [hR1B, LinearMap.sum_apply, Finset.sum_eq_single c]
    · rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ1, one_smul]
    · intro c' _ hc'
      rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ2 c' c hc'.symm, zero_smul,
        smul_zero]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have hR1Av : ∀ j, R1A (v' j) = 0 := by
    intro j
    rw [hR1A, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ4, zero_smul, smul_zero]
  have hR1Bv : ∀ j, R1B (v' j) = 0 := by
    intro j
    rw [hR1B, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ4, zero_smul, smul_zero]
  -- the corrected pencil is block triangular with diagonal blocks
  obtain ⟨Ac, hAc⟩ : ∃ Ac : V →ₗ[ℂ] W, Ac = A - (R1A + R2A) := ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc : V →ₗ[ℂ] W, Bc = B - (R1B + R2B) := ⟨_, rfl⟩
  have hAcx : ∀ v, Ac v = A v - (R1A v + R2A v) := fun v => by
    rw [hAc]
    rfl
  have hBcx : ∀ v, Bc v = B v - (R1B v + R2B v) := fun v => by
    rw [hBc]
    rfl
  have hAcxs : ∀ k, Ac (xs k) = (-(tt k)) • wh k := by
    rintro (k | c)
    · rw [hAcx, hR1Al, hR2A0 _ (hxsV1 _), add_zero, sub_zero, hxse, hwhl]
    · rw [hAcx, hR1Ar, hR2A0 _ (hxsV1 _), add_zero, hxse, hwhr, smul_sub]
      abel
  have hBcxs : ∀ k, Bc (xs k) = (1 : ℂ) • wh k := by
    rintro (k | c)
    · rw [hBcx, hR1Bl, hR2B0 _ (hxsV1 _), add_zero, sub_zero, hwhl, one_smul]
    · rw [hBcx, hR1Br, hR2B0 _ (hxsV1 _), add_zero, hwhr, one_smul, one_smul]
      abel
  have hAcv : ∀ j, Ac (v' j) - a' j • w' j ∈ Submodule.span ℂ (Set.range wh) := by
    intro j
    have h1 := hAq' j
    rw [← hv' j, ← hw' j, hAqx, ← hR2A] at h1
    rw [hwhsp, ← Submodule.Quotient.mk_eq_zero, hAcx, hR1Av, zero_add]
    show W1'.mkQ (A (v' j) - R2A (v' j) - a' j • w' j) = 0
    rw [map_sub, map_sub, map_smul, h1]
    abel
  have hBcv : ∀ j, Bc (v' j) - b' j • w' j ∈ Submodule.span ℂ (Set.range wh) := by
    intro j
    have h1 := hBq' j
    rw [← hv' j, ← hw' j, hBqx, ← hR2B] at h1
    rw [hwhsp, ← Submodule.Quotient.mk_eq_zero, hBcx, hR1Bv, zero_add]
    show W1'.mkQ (B (v' j) - R2B (v' j) - b' j • w' j) = 0
    rw [map_sub, map_sub, map_smul, h1]
    abel
  have hne' : ∀ (k : K ⊕ C) (j : Fin (finrank ℂ (V ⧸ V1))),
      (-(tt k)) * b' j - a' j * 1 ≠ 0 := by
    intro k j h
    exact hFne (tt k) (httF k) j (by linear_combination -h)
  obtain ⟨Y, X, hYX⟩ := glue Ac Bc xs wh (fun k => -(tt k)) (fun _ => 1) v' w' a' b'
    hAcxs hBcxs hAcv hBcv hne'
  -- the final bases
  have hvh : ∀ j, Submodule.Quotient.mk (p := V1) (v' j - ∑ k, Y j k • xs k) = bVq j := by
    intro j
    rw [← hv' j]
    refine (Submodule.Quotient.eq V1).mpr ?_
    rw [sub_sub_cancel_left]
    exact V1.neg_mem (V1.sum_mem fun k _ => V1.smul_mem _ (hxsV1 k))
  have hwh' : ∀ j, Submodule.Quotient.mk (p := W1') (w' j + ∑ k, X j k • wh k) = bWq j := by
    intro j
    rw [← hw' j]
    refine (Submodule.Quotient.eq W1').mpr ?_
    rw [add_sub_cancel_left]
    exact W1'.sum_mem fun k _ => W1'.smul_mem _ (hwhmem k)
  have hliV : LinearIndependent ℂ (Sum.elim xs fun j => v' j - ∑ k, Y j k • xs k) :=
    LinearIndependent.sumElim_of_quotient hxsS _ (by
      have h : (Submodule.Quotient.mk (p := V1) ∘ fun j => v' j - ∑ k, Y j k • xs k) = bVq :=
        funext hvh
      rw [h]
      exact bVq.linearIndependent)
  have hliW : LinearIndependent ℂ (Sum.elim wh fun j => w' j + ∑ k, X j k • wh k) :=
    LinearIndependent.sumElim_of_quotient hwhS _ (by
      have h : (Submodule.Quotient.mk (p := W1') ∘ fun j => w' j + ∑ k, X j k • wh k) = bWq :=
        funext hwh'
      rw [h]
      exact bWq.linearIndependent)
  have hcardW : Fintype.card ((K ⊕ C) ⊕ Fin (finrank ℂ (V ⧸ V1))) = finrank ℂ W := by
    rw [hcard, hdim]
  have hDP : DP (Fintype.card C + finrank ℂ (V ⧸ V1) / 2) A B := by
    refine ⟨(K ⊕ C) ⊕ Fin (finrank ℂ (V ⧸ V1)), inferInstance,
      basisOfLinearIndependentOfCardEqFinrank' _ hliV hcard,
      basisOfLinearIndependentOfCardEqFinrank' _ hliW hcardW,
      Sum.elim (fun k => -(tt k)) a', Sum.elim (fun _ => 1) b', R1A + R2A, R1B + R2B,
      hR1.add hR2, ?_, ?_⟩
    · rintro (k | j)
      · simp only [coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inl,
          LinearMap.add_apply]
        rw [← hAcxs k, hAcx]
        abel
      · simp only [coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inr,
          LinearMap.add_apply]
        rw [← (hYX j).1, hAcx]
        abel
    · rintro (k | j)
      · simp only [coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inl,
          LinearMap.add_apply]
        rw [← hBcxs k, hBcx]
        abel
      · simp only [coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inr,
          LinearMap.add_apply]
        rw [← (hYX j).2, hBcx]
        abel
  exact hDP.mono (by omega)

end Abstract

section Final

open Matrix

/-- The conclusion of H2 with `r` rank-one matrices. -/
def Goal (n r : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) (u v : Fin r → Fin n → ℂ)
    (α β : Fin r → ℂ), IsUnit P ∧ IsUnit Q ∧
    A = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
    B = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j)

/-- Every pencil of `n × n` matrices is, in suitable bases, simultaneously diagonal up to
`n / 2` rank-one pencils. -/
theorem all_pencils : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), Goal n (n / 2) A B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have case2 : ∀ A B : Matrix (Fin n) (Fin n) ℂ,
        (∀ v : Fin n → ℂ, A *ᵥ v = 0 → B *ᵥ v = 0 → v = 0) → Goal n (n / 2) A B := by
      intro A B hk
      have h := DP_of_no_kernel (Matrix.toLin' A) (Matrix.toLin' B) rfl
        (fun v h1 h2 => hk v (by rwa [Matrix.toLin'_apply] at h1)
          (by rwa [Matrix.toLin'_apply] at h2))
      rw [Module.finrank_fin_fun] at h
      exact matrix_of_DP A B h
    intro A B
    by_cases hk : ∀ v : Fin n → ℂ, A *ᵥ v = 0 → B *ᵥ v = 0 → v = 0
    · exact case2 A B hk
    by_cases hl : ∀ φ : Fin n → ℂ, φ ᵥ* A = 0 → φ ᵥ* B = 0 → φ = 0
    · obtain ⟨P, Q, a, b, u, v, α, β, hP, hQ, hA, hB⟩ := case2 Aᵀ Bᵀ (fun φ h1 h2 =>
        hl φ (by rwa [Matrix.mulVec_transpose] at h1) (by rwa [Matrix.mulVec_transpose] at h2))
      have htr : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ) (γ : Fin (n / 2) → ℂ),
          Mᵀ = P * Matrix.diagonal c * Q + ∑ j, γ j • Matrix.vecMulVec (u j) (v j) →
          M = Qᵀ * Matrix.diagonal c * Pᵀ + ∑ j, γ j • Matrix.vecMulVec (v j) (u j) := by
        intro M c γ h
        have h1 := congrArg Matrix.transpose h
        rw [Matrix.transpose_transpose] at h1
        rw [h1, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
          Matrix.diagonal_transpose, Matrix.transpose_sum, Matrix.mul_assoc]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by
          rw [Matrix.transpose_smul, Matrix.transpose_vecMulVec]
      exact ⟨Qᵀ, Pᵀ, a, b, v, u, α, β,
        (Matrix.isUnit_iff_isUnit_det _).mpr (by
          rw [Matrix.det_transpose]
          exact (Matrix.isUnit_iff_isUnit_det _).mp hQ),
        (Matrix.isUnit_iff_isUnit_det _).mpr (by
          rw [Matrix.det_transpose]
          exact (Matrix.isUnit_iff_isUnit_det _).mp hP), htr A a α hA, htr B b β hB⟩
    · push Not at hk hl
      obtain ⟨v0, hv0A, hv0B, hv0⟩ := hk
      obtain ⟨φ0, hφA, hφB, hφ0⟩ := hl
      have hn : n ≠ 0 := by
        rintro rfl
        exact hv0 (Subsingleton.elim _ _)
      let φ : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
        { toFun := fun x => φ0 ⬝ᵥ x
          map_add' := fun x y => dotProduct_add φ0 x y
          map_smul' := fun c x => by simp [dotProduct_smul] }
      have hφ : φ ≠ 0 := by
        intro h
        apply hφ0
        funext j
        have h1 := LinearMap.congr_fun h (Pi.single j 1)
        simpa [φ] using h1
      have hDP : DP ((n - 1) / 2) (Matrix.toLin' A) (Matrix.toLin' B) := by
        refine DP_of_zero_block _ _ v0 hv0 (by rw [Matrix.toLin'_apply]; exact hv0A)
          (by rw [Matrix.toLin'_apply]; exact hv0B) φ hφ ?_ ?_ _ ?_
        · intro x
          show φ0 ⬝ᵥ (Matrix.toLin' A x) = 0
          rw [Matrix.toLin'_apply, Matrix.dotProduct_mulVec, hφA, zero_dotProduct]
        · intro x
          show φ0 ⬝ᵥ (Matrix.toLin' B x) = 0
          rw [Matrix.toLin'_apply, Matrix.dotProduct_mulVec, hφB, zero_dotProduct]
        · intro A' B'
          have hV : finrank ℂ ((Fin n → ℂ) ⧸ Submodule.span ℂ {v0}) = n - 1 := by
            have h := finrank_quot_span_singleton hv0
            rw [Module.finrank_fin_fun] at h
            omega
          have hW : finrank ℂ (LinearMap.ker φ) = n - 1 := by
            have h := finrank_ker_functional hφ
            rw [Module.finrank_fin_fun] at h
            omega
          exact DP_of_matrices hV hW A' B' (ih (n - 1) (by omega))
      exact matrix_of_DP A B (hDP.mono (by omega))

end Final

end SqH2

end OMA

open OMA.R1 Matrix Polynomial in
theorem square_slices_bound : type_of% @Arxiv.«0805.3777».cprank_le_of_square_slices := by
  intro m n hm hn T
  have h1 : H1 := fun n A B _ => OMA.SqH2.all_pencils n A B
  have h2 : H2 := fun n A B _ => OMA.SqH2.all_pencils n A B
  classical
  let S : ℕ → Matrix (Fin n) (Fin n) ℂ := fun i => Matrix.of fun j k =>
    if h : i < m then T ⟨[i, j.1, k.1], .cons h (.cons j.2 (.cons k.2 .nil))⟩ else 0
  have hS : ∀ i : Fin m, (Matrix.of fun (j k : Fin n) =>
      T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ :
        Matrix (Fin n) (Fin n) ℂ) = S i.1 := by
    intro i
    ext j k
    simp only [S, Matrix.of_apply, dif_pos i.2]
  have hfin : ∀ (ι : Type) (_ : Fintype ι) (x y : ι → Fin n → ℂ),
      Fintype.card ι ≤ (m + 1) * n / 2 →
      (∀ i < m, S i ∈ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l))) →
      T.cprank ≤ (m + 1) * n / 2 := by
    intro ι _ x y hcard hmem
    exact cprank_le_of_cover T x y hcard fun i => by
      rw [hS i]
      exact hmem i.1 i.2
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
  · -- even number of slices
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hE : ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ)
        (u v : Fin (n / 2) → Fin n → ℂ) (α β : Fin (n / 2) → ℂ), IsUnit P ∧ IsUnit Q ∧
        S 0 = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
        S 1 = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j) := by
      by_cases h : ∃ s t : ℂ, IsUnit (s • S 0 + t • S 1)
      · exact h1 n (S 0) (S 1) h
      · exact h2 n (S 0) (S 1) fun s t hst => h ⟨s, t, hst⟩
    obtain ⟨P, Q, a, b, u, v, α, β, hP, hQ, hS0, hS1⟩ := hE
    obtain ⟨ι, inst, x, y, hcard, hbase, hpairs⟩ := cover P Q hP hQ
      (fun j : Fin k => S (2 * j.1 + 2)) (fun j : Fin k => S (2 * j.1 + 3)) u v
    refine hfin ι inst x y ?_ ?_
    · rw [hcard, hk]
      have e : (2 * (k + 1) + 1) * n = n + 2 * ((k + 1) * n) := by ring
      rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      have e2 : (k + 1) * n = k * n + n := by ring
      omega
    · intro i hi
      rcases Nat.lt_or_ge i 2 with h2' | h2'
      · interval_cases i
        · rw [hS0]
          exact hbase a α
        · rw [hS1]
          exact hbase b β
      · obtain ⟨j, hj | hj⟩ : ∃ j, i = 2 * j + 2 ∨ i = 2 * j + 3 := ⟨(i - 2) / 2, by omega⟩
        · have hjk : j < k := by omega
          rw [hj]
          exact (hpairs ⟨j, hjk⟩).1
        · have hjk : j < k := by omega
          rw [hj]
          exact (hpairs ⟨j, hjk⟩).2
  · -- odd number of slices
    obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (S 0)
    have hP : IsUnit (L.map Matrix.TransvectionStruct.toMatrix).prod :=
      (isUnit_iff_isUnit_det _).mpr (by
        rw [Matrix.TransvectionStruct.det_toMatrix_prod]
        exact isUnit_one)
    have hQ : IsUnit (L'.map Matrix.TransvectionStruct.toMatrix).prod :=
      (isUnit_iff_isUnit_det _).mpr (by
        rw [Matrix.TransvectionStruct.det_toMatrix_prod]
        exact isUnit_one)
    obtain ⟨ι, inst, x, y, hcard, hbase, hpairs⟩ := cover _ _ hP hQ
      (fun j : Fin k => S (2 * j.1 + 1)) (fun j : Fin k => S (2 * j.1 + 2))
      (Fin.elim0 : Fin 0 → Fin n → ℂ) (Fin.elim0 : Fin 0 → Fin n → ℂ)
    refine hfin ι inst x y ?_ ?_
    · rw [hcard, hk]
      have e : (2 * k + 1 + 1) * n = 2 * ((k + 1) * n) := by ring
      rw [e, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      have e2 : (k + 1) * n = k * n + n := by ring
      omega
    · intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · rw [h0, hD]
        have hb := hbase D (Fin.elim0 : Fin 0 → ℂ)
        simpa using hb
      · obtain ⟨j, hj | hj⟩ : ∃ j, i = 2 * j + 1 ∨ i = 2 * j + 2 := ⟨(i - 1) / 2, by omega⟩
        · have hjk : j < k := by omega
          rw [hj]
          exact (hpairs ⟨j, hjk⟩).1
        · have hjk : j < k := by omega
          rw [hj]
          exact (hpairs ⟨j, hjk⟩).2

end MaxCube.OddLow.Source

namespace MaxCube

/-- A bounded-rank matrix is a sum of that many outer products, including zero padding. -/
private lemma low_rank_coordinates {b c r : ℕ} (M : Matrix (Fin b) (Fin c) ℂ) (hr : M.rank ≤ r) :
    ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ, ∀ i j, M i j = ∑ t,y t i*z t j := by
  classical
  let V := LinearMap.range M.mulVecLin
  let basis : Module.Basis (Fin M.rank) ℂ V := Module.finBasis ℂ V
  let column (j : Fin c) : V := ⟨M.col j,Pi.single j 1,Matrix.mulVec_single_one M j⟩
  let u (t : Fin M.rank) (i : Fin b) := ((basis t : V) : Fin b → ℂ) i
  let v (t : Fin M.rank) (j : Fin c) := basis.repr (column j) t
  have hm (i : Fin b) (j : Fin c) : M i j=∑ t,u t i*v t j := by
    have hh := congrArg (fun w : V => (w : Fin b → ℂ) i) (basis.sum_repr (column j))
    change ((∑ t,basis.repr (column j) t • basis t : V) : Fin b → ℂ) i=M i j at hh
    simpa only [u,v,Submodule.coe_sum,Submodule.coe_smul_of_tower,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using hh.symm
  let e : Fin M.rank ⊕ Fin (r-M.rank) ≃ Fin r := Fintype.equivOfCardEq (by simp; omega)
  refine ⟨fun t => (e.symm t).elim u 0,fun t => (e.symm t).elim v 0,?_⟩
  intro i j
  let w (t : Fin M.rank ⊕ Fin (r-M.rank)) := (t.elim u 0) i*(t.elim v 0) j
  change M i j=∑ t : Fin r,w (e.symm t)
  rw [e.symm.sum_comp,Fintype.sum_sum_type]
  simpa [w] using hm i j

/-- Replace one slice by a nonzero linear combination, cover the remaining slices,
and adjoin at most the matrix rank of that combination. -/
lemma decomp_of_contraction_rank_le {a b c s r : ℕ}
    (otherSlices : ∀ U : Fin a → Matrix (Fin b) (Fin c) ℂ, Decomp a b c s U)
    (T : Fin (a+1) → Matrix (Fin b) (Fin c) ℂ) (p : Fin (a+1) → ℂ) (hp : p ≠ 0)
    (hr : (Matrix.of (fun j k => ∑ i,p i*T i j k)).rank ≤ r) : Decomp (a+1) b c (s+r) T := by
  classical
  obtain ⟨l,hl⟩ : ∃ l,p l≠0 := by
    by_contra! hz
    exact hp (funext hz)
  let C : Matrix (Fin b) (Fin c) ℂ := Matrix.of (fun j k => ∑ i,p i*T i j k)
  obtain ⟨u,y,z,hu⟩ := otherSlices (fun t : Fin a => T (l.succAbove t))
  obtain ⟨y₁,z₁,hh⟩ := low_rank_coordinates C hr
  let Y : Fin s ⊕ Fin r → Fin b → ℂ := Sum.elim y y₁
  let Z : Fin s ⊕ Fin r → Fin c → ℂ := Sum.elim z z₁
  let F (t : Fin s ⊕ Fin r) : Matrix (Fin b) (Fin c) ℂ := fun j k => Y t j*Z t k
  let W := Submodule.span ℂ (Set.range F)
  have mem (t : Fin s ⊕ Fin r) : F t ∈ W := Submodule.subset_span ⟨t,rfl⟩
  have hC : C ∈ W := by
    have eq : C=∑ t : Fin r,F (.inr t) := by
      ext j k
      rw [Matrix.sum_apply]
      exact hh j k
    rw [eq]
    exact W.sum_mem fun t _ => mem (.inr t)
  have other (t : Fin a) : T (l.succAbove t) ∈ W := by
    have eq : T (l.succAbove t)=∑ u' : Fin s,u u' t • F (.inl u') := by
      ext j k
      simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
      exact hu t j k
    rw [eq]
    exact W.sum_mem fun t' _ => W.smul_mem _ (mem (.inl t'))
  have eq : C=p l • T l + ∑ t : Fin a,p (l.succAbove t) • T (l.succAbove t) := by
    have hs : C=∑ i,p i • T i := by ext j k; simp [C,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    exact hs.trans (Fin.sum_univ_succAbove (fun i => p i • T i) l)
  have hlT : T l ∈ W := by
    have hsum : (∑ t : Fin a,p (l.succAbove t) • T (l.succAbove t)) ∈ W :=
      W.sum_mem fun t _ => W.smul_mem _ (other t)
    have hm : p l • T l ∈ W := by simpa only [eq,add_sub_cancel_right] using W.sub_mem hC hsum
    simpa only [smul_smul,inv_mul_cancel₀ hl,one_smul] using W.smul_mem (p l)⁻¹ hm
  have allmem (i : Fin (a+1)) : T i ∈ W := by
    by_cases he : i=l
    · exact he ▸ hlT
    · obtain ⟨t,rfl⟩ := Fin.exists_succAbove_eq he
      exact other t
  have coeff (i : Fin (a+1)) : ∃ v : Fin s ⊕ Fin r → ℂ, ∑ t,v t • F t=T i :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (allmem i)
  choose v hv using coeff
  let e : Fin s ⊕ Fin r ≃ Fin (s+r) := finSumFinEquiv
  refine ⟨fun t i => v i (e.symm t),fun t => Y (e.symm t),fun t => Z (e.symm t),?_⟩
  intro i j k
  let term (t : Fin s ⊕ Fin r) := v i t*(Y t j*Z t k)
  change T i j k=∑ t : Fin (s+r),term (e.symm t)
  rw [e.symm.sum_comp]
  have hc := (congrArg (fun m : Matrix (Fin b) (Fin c) ℂ => m j k) (hv i)).symm
  change T i j k = (∑ t,v i t • F t) j k at hc
  simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] using hc


end MaxCube

namespace MaxCube.OddLow

/-- A low-rank linear combination in the first mode yields an improved bound
for odd cubical tensors. The remaining even number of square slices uses
the certified ordinary square-slice estimate. -/
theorem first_mode {k : ℕ} (hk : 2 ≤ k)
    (T : Fin (2*k+1) → Matrix (Fin (2*k+1)) (Fin (2*k+1)) ℂ)
    (p : Fin (2*k+1) → ℂ) (hp : p ≠ 0)
    (hlow : (Matrix.of (fun j l => ∑ i, p i * T i j l)).rank ≤ k) :
    Decomp (2*k+1) (2*k+1) (2*k+1) ((2*k+1)*(2*k+2)/2-1) T := by
  have core (U : Fin (2*k) → Matrix (Fin (2*k+1)) (Fin (2*k+1)) ℂ) :
      Decomp (2*k) (2*k+1) (2*k+1) ((2*k+1)*(2*k+1)/2) U :=
    (cprank_le_iff_decomp U _).mp (@Source.square_slices_bound (2*k) (2*k+1) (by omega) (by omega) (coordinateHolor U))
  have whole := decomp_of_contraction_rank_le core T p hp hlow
  have arithmetic : (2*k+1)*(2*k+1)/2 + k = (2*k+1)*(2*k+2)/2-1 := by
    let v := 2*k*k+2*k
    have h₁ : (2*k+1)*(2*k+1) = v*2+1 := by dsimp [v]; ring
    have h₂ : (2*k+1)*(2*k+2) = (v+k+1)*2 := by dsimp [v]; ring
    rw [h₁,h₂]
    omega
  rwa [arithmetic] at whole

/-- Recover a tensor decomposition after the cyclic change of order
(second index, third index, first index). -/
lemma unrotate {n r : ℕ} (T : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (h : Decomp n n n r (fun i j l => T l i j)) : Decomp n n n r T := by
  obtain ⟨x,y,z,repr⟩ := h
  refine ⟨z,x,y,?_⟩
  intro i j l
  exact (repr j l i).trans (Finset.sum_congr rfl fun t _ => by ring)

/-- Contraction in the second mode, with row index in the third axis. -/
theorem second_mode {k : ℕ} (hk : 2 ≤ k)
    (T : Fin (2*k+1) → Matrix (Fin (2*k+1)) (Fin (2*k+1)) ℂ)
    (p : Fin (2*k+1) → ℂ) (hp : p ≠ 0)
    (hlow : (Matrix.of (fun l i => ∑ j, p j * T i j l)).rank ≤ k) :
    Decomp (2*k+1) (2*k+1) (2*k+1) ((2*k+1)*(2*k+2)/2-1) T :=
  unrotate T (first_mode hk (fun j l i => T i j l) p hp hlow)

/-- Contraction in the third mode, with row index in the first axis. -/
theorem third_mode {k : ℕ} (hk : 2 ≤ k)
    (T : Fin (2*k+1) → Matrix (Fin (2*k+1)) (Fin (2*k+1)) ℂ)
    (p : Fin (2*k+1) → ℂ) (hp : p ≠ 0)
    (hlow : (Matrix.of (fun i j => ∑ l, p l * T i j l)).rank ≤ k) :
    Decomp (2*k+1) (2*k+1) (2*k+1) ((2*k+1)*(2*k+2)/2-1) T :=
  unrotate T (second_mode hk (fun j l i => T i j l) p hp hlow)

theorem cprank_of_low_mode {k : ℕ} (hk : 2 ≤ k)
    (T : Fin (2*k+1) → Matrix (Fin (2*k+1)) (Fin (2*k+1)) ℂ)
    (p : Fin (2*k+1) → ℂ) (hp : p ≠ 0)
    (hlow : (Matrix.of (fun j l => ∑ i, p i * T i j l)).rank ≤ k ∨
      (Matrix.of (fun l i => ∑ j, p j * T i j l)).rank ≤ k ∨
      (Matrix.of (fun i j => ∑ l, p l * T i j l)).rank ≤ k) :
    (coordinateHolor T).cprank ≤ (2*k+1)*(2*k+2)/2-1 := by
  apply (cprank_le_iff_decomp T _).mpr
  rcases hlow with h | h | h
  · exact first_mode hk T p hp h
  · exact second_mode hk T p hp h
  · exact third_mode hk T p hp h

/-- A counterexample to the improved odd-cube upper bound must have large
matrix rank in all nonzero directions in all three modes. -/
theorem all_contractions_large {k : ℕ} (hk : 2 ≤ k)
    (T : Fin (2*k+1) → Matrix (Fin (2*k+1)) (Fin (2*k+1)) ℂ)
    (h : ¬ Decomp (2*k+1) (2*k+1) (2*k+1) ((2*k+1)*(2*k+2)/2-1) T)
    (p : Fin (2*k+1) → ℂ) (hp : p ≠ 0) :
    k < (Matrix.of (fun j l => ∑ i, p i * T i j l)).rank ∧
    k < (Matrix.of (fun l i => ∑ j, p j * T i j l)).rank ∧
    k < (Matrix.of (fun i j => ∑ l, p l * T i j l)).rank := by
  exact ⟨lt_of_not_ge (fun hm => h (first_mode hk T p hp hm)),
    lt_of_not_ge (fun hm => h (second_mode hk T p hp hm)),
    lt_of_not_ge (fun hm => h (third_mode hk T p hp hm))⟩

end MaxCube.OddLow

namespace MaxCube.MatchedThree

open Matrix CP3

/-- A rank-one cover whose span contains an invertible matrix. -/
def RegCov {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℂ (Matrix ι ι ℂ)) (r : ℕ) : Prop :=
  ∃ s : Finset (Matrix ι ι ℂ), s.card ≤ r ∧ (∀ M ∈ s, IsR1 M) ∧
    S ≤ Submodule.span ℂ (s : Set (Matrix ι ι ℂ)) ∧
      ∃ R : Matrix ι ι ℂ, R ∈ Submodule.span ℂ (s : Set (Matrix ι ι ℂ)) ∧ R.det ≠ 0

lemma RegCov.mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S S' : Submodule ℂ (Matrix ι ι ℂ)} {r : ℕ} (h : S' ≤ S) (hS : RegCov S r) :
    RegCov S' r := by
  obtain ⟨s, hs, h1, h2, h3⟩ := hS
  exact ⟨s, hs, h1, h.trans h2, h3⟩

lemma RegCov.map {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    {S : Submodule ℂ (Matrix ι ι ℂ)} {r : ℕ}
    (g : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι' ι' ℂ)
    (h1 : ∀ M, IsR1 M → IsR1 (g M)) (hi : ∀ M, M.det ≠ 0 → (g M).det ≠ 0)
    (hS : RegCov S r) : RegCov (S.map g) r := by
  classical
  obtain ⟨s, hs, rankone, contains, R, hR, hdet⟩ := hS
  refine ⟨s.image g, Finset.card_image_le.trans hs, ?_, ?_, g R, ?_, hi R hdet⟩
  · intro M hM
    obtain ⟨N,hN,rfl⟩ := Finset.mem_image.mp hM
    exact h1 N (rankone N hN)
  · rw [Finset.coe_image, ← Submodule.map_span]
    exact Submodule.map_mono contains
  · rw [Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hR

lemma transfer {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    {A B C : Matrix ι ι ℂ} {r : ℕ}
    (f : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι' ι' ℂ) (g : Matrix ι' ι' ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (h1 : ∀ M, IsR1 M → IsR1 (g M)) (hi : ∀ M, M.det ≠ 0 → (g M).det ≠ 0)
    (hA : g (f A) = A) (hB : g (f B) = B) (hC : g (f C) = C)
    (h : RegCov (sp3 (f A) (f B) (f C)) r) : RegCov (sp3 A B C) r := by
  have mapped := h.map g h1 hi
  rwa [sp3_map, hA, hB, hC] at mapped

-- The regular-cover versions below adapt ivillar's formal proof of the
-- Sumi–Miyazaki–Sakata three-slice estimate (upstream proof blob
-- 860efc9a0bfbbd4c28c3dea7defbe06673f2d73e). The additional witness is
-- the first corrected matrix of the simple-spectrum pencil.

theorem L43Fin {n s : ℕ} (hs : s ≤ n) (D : Fin n → ℂ) (B C : Matrix (Fin n) (Fin n) ℂ)
    (j0 : Fin n) (hj0 : (j0 : ℕ) < s) (hD : D j0 = 0)
    (hgood : Good (B.submatrix (Fin.castLE hs) (Fin.castLE hs))
      (C.submatrix (Fin.castLE hs) (Fin.castLE hs))) :
    RegCov (sp3 (diagonal D) B C) (2 * n - 1) := by
  classical
  obtain ⟨d₁, d₂, hd, hg⟩ := osl_all s n hs B C hgood
  obtain ⟨x, y, c, hB, hC⟩ := nice_of_good _ _ hg
  let E : Fin n → Matrix (Fin n) (Fin n) ℂ := fun l => vecMulVec (Pi.single l 1) (Pi.single l 1)
  let T₁ : Finset (Matrix (Fin n) (Fin n) ℂ) := (Finset.univ.erase j0).image E
  let T₂ : Finset (Matrix (Fin n) (Fin n) ℂ) := Finset.univ.image fun l => vecMulVec (x l) (y l)
  have hT₁ : T₁.card ≤ n - 1 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hT₂ : T₂.card ≤ n := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
  have hn : 1 ≤ n := by have := j0.2; omega
  refine ⟨T₁ ∪ T₂, (Finset.card_union_le _ _).trans (by omega), ?_, ?_⟩
  · intro M hM
    rcases Finset.mem_union.mp hM with h | h
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h
      exact ⟨_, _, rfl⟩
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h
      exact ⟨_, _, rfl⟩
  · set W := Submodule.span ℂ ((T₁ ∪ T₂ : Finset _) : Set (Matrix (Fin n) (Fin n) ℂ))
    have hdiag : ∀ d : Fin n → ℂ, d j0 = 0 → diagonal d ∈ W := by
      intro d hd0
      rw [CP3.diag_sum, ← Finset.sum_erase Finset.univ (a := j0) (by simp [hd0])]
      apply Submodule.sum_mem
      intro l hl
      apply Submodule.smul_mem
      apply Submodule.subset_span
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      left
      exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
    have hnice : ∀ c' : Fin n → ℂ, ∑ l, c' l • vecMulVec (x l) (y l) ∈ W := by
      intro c'
      apply Submodule.sum_mem
      intro l _
      apply Submodule.smul_mem
      apply Submodule.subset_span
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      right
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
    refine ⟨?_, B + diagonal d₁, ?_, hg.1⟩
    · apply sp3_le (hdiag D hD)
      · have : B = (B + diagonal d₁) - diagonal d₁ := by abel
        rw [this, hB]
        refine W.sub_mem ?_ (hdiag d₁ (hd j0 hj0).1)
        simpa using hnice 1
      · have : C = (C + diagonal d₂) - diagonal d₂ := by abel
        rw [this, hC]
        exact W.sub_mem (hnice c) (hdiag d₂ (hd j0 hj0).2)
    · rw [hB]
      simpa using hnice 1

theorem L43 {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (core : Fin s → ι)
    (hcore : Function.Injective core) (D : ι → ℂ) (B C : Matrix ι ι ℂ) (j0 : Fin s)
    (hD : D (core j0) = 0) (hgood : Good (B.submatrix core core) (C.submatrix core core)) :
    RegCov (sp3 (diagonal D) B C) (2 * Fintype.card ι - 1) := by
  have hs : s ≤ Fintype.card ι := by
    simpa using Fintype.card_le_of_injective core hcore
  obtain ⟨e, he⟩ := exists_equiv_core s core hcore hs
  have he' : ∀ a, e.symm (Fin.castLE hs a) = core a := by
    intro a; rw [← he a, Equiv.symm_apply_apply]
  have hgg : ∀ M : Matrix ι ι ℂ, subL e e (subL e.symm e.symm M) = M := by
    intro M; ext i j; simp [subL_apply]
  refine transfer (subL e.symm e.symm) (subL e e) (isR1_subL e e)
    (fun M hn => by simpa only [subL_apply, det_submatrix_equiv_self] using hn) (hgg _) (hgg _) (hgg _) ?_
  have hdg : subL e.symm e.symm (diagonal D) = diagonal (D ∘ e.symm) := by
    ext i j; simp [subL_apply, diagonal_apply]
  rw [hdg]
  have hsub : ∀ M : Matrix ι ι ℂ, (subL e.symm e.symm M).submatrix (Fin.castLE hs) (Fin.castLE hs)
      = M.submatrix core core := by
    intro M; ext i j; simp [subL_apply, he']
  refine L43Fin hs (D ∘ e.symm) _ _ (Fin.castLE hs j0) (by simp) (by simp [he', hD]) ?_
  rw [hsub, hsub]; exact hgood

theorem stepA {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℂ) (B C : Matrix ι ι ℂ) (i j : ι)
    (hi : D i = 0) (hj : D j = 0) (hB : B i j ≠ 0) :
    RegCov (sp3 (diagonal D) B C) (2 * Fintype.card ι - 1) := by
  set σ := Equiv.swap i j
  have hgg : ∀ M : Matrix ι ι ℂ, subL id σ (subL id σ M) = M := by
    intro M; ext a b; simp [subL_apply, σ]
  refine transfer (subL id σ) (subL id σ) (isR1_subL id σ)
    (fun M hn => by
      rw [subL_apply, det_permute']
      exact mul_ne_zero (Int.cast_ne_zero.mpr (Units.ne_zero _)) hn) (hgg _) (hgg _) (hgg _) ?_
  have hdg : subL id σ (diagonal D) = diagonal D := by
    ext a b
    simp only [subL_apply, submatrix_apply, id, diagonal_apply, σ]
    by_cases hb1 : b = i
    · subst hb1; rw [Equiv.swap_apply_left]
      by_cases ha : a = j
      · subst ha; simp [hj]
      · by_cases hab : a = b
        · subst hab; simp [hi]
        · simp [ha, hab]
    · by_cases hb2 : b = j
      · subst hb2; rw [Equiv.swap_apply_right]
        by_cases ha : a = i
        · subst ha; simp [hi]
        · by_cases hab : a = b
          · subst hab; simp [hj]
          · simp [ha, hab]
      · rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2]
  rw [hdg]
  refine L43 1 (fun _ => i) (fun a b _ => Subsingleton.elim a b) D _ _ 0 hi (core1 _ _ ?_)
  simp only [subL_apply, submatrix_apply, id, σ, Equiv.swap_apply_left]
  exact hB

theorem stepB_core {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℂ) (X Y : Matrix ι ι ℂ)
    (p j : ι) (hpj : p ≠ j) (hj : D j = 0) (hX : X j j = 0) (hY : Y j j = 0)
    (h1 : X p j * X j p ≠ 0) (h2 : X p j * Y j p ≠ Y p j * X j p) :
    RegCov (sp3 (diagonal D) X Y) (2 * Fintype.card ι - 1) := by
  have hinj : Function.Injective ![p, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [Ne.symm hpj]
  exact L43 2 ![p, j] hinj D X Y 1 (by simpa using hj)
    (core2 _ _ (by simpa using hX) (by simpa using hY) (by simpa using h1) (by simpa using h2))

theorem stepB_pair {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℂ) (B C : Matrix ι ι ℂ)
    (p j : ι) (hpj : p ≠ j) (hj : D j = 0) (hB : B j j = 0) (hC : C j j = 0)
    (hdet : C p j * B j p ≠ B p j * C j p) :
    RegCov (sp3 (diagonal D) B C) (2 * Fintype.card ι - 1) := by
  by_cases hc1 : B p j * B j p ≠ 0
  · exact stepB_core D B C p j hpj hj hB hC hc1 (fun h => hdet (by linear_combination -h))
  by_cases hc2 : C p j * C j p ≠ 0
  · rw [sp3_swap]
    exact stepB_core D C B p j hpj hj hC hB hc2 hdet
  push Not at hc1 hc2
  have hmono : sp3 (diagonal D) B C ≤ sp3 (diagonal D) (B + C) C := by
    apply sp3_le (mem_sp3_1 _ _ _) _ (mem_sp3_3 _ _ _)
    have := Submodule.sub_mem _ (mem_sp3_2 (diagonal D) (B + C) C) (mem_sp3_3 (diagonal D) (B + C) C)
    simpa using this
  refine RegCov.mono hmono (stepB_core D (B + C) C p j hpj hj (by simp [hB, hC]) hC ?_ ?_)
  · simp only [Matrix.add_apply]
    rcases mul_eq_zero.mp hc1 with h | h <;> rcases mul_eq_zero.mp hc2 with h' | h'
    · rw [h, h'] at hdet; simp at hdet
    · rw [h, h', zero_add, add_zero]
      exact mul_ne_zero (left_ne_zero_of_mul (by rw [h] at hdet; simpa using hdet))
        (right_ne_zero_of_mul (by rw [h] at hdet; simpa using hdet))
    · rw [h, h', add_zero, zero_add]
      have : B p j * C j p ≠ 0 := by rw [h] at hdet; simpa [eq_comm] using hdet
      exact this
    · rw [h, h'] at hdet; simp at hdet
  · simp only [Matrix.add_apply]
    intro h
    apply hdet
    linear_combination -h

theorem stepB {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℂ) (hD01 : ∀ i, D i = 0 ∨ D i = 1)
    (B C : Matrix ι ι ℂ) (hZZ : ∀ a b, D a = 0 → D b = 0 → B a b = 0 ∧ C a b = 0) (j : ι)
    (hj : D j = 0) (hind : ∀ c₁ c₂ : ℂ, (∀ i, c₁ * B i j + c₂ * C i j = 0) → c₁ = 0 ∧ c₂ = 0)
    (p : ι) (hp : B j p ≠ 0 ∨ C j p ≠ 0) :
    RegCov (sp3 (diagonal D) B C) (2 * Fintype.card ι - 1) := by
  have hDp : D p = 1 := by
    rcases hD01 p with h | h
    · exfalso
      obtain ⟨h1, h2⟩ := hZZ j p hj h
      rcases hp with h3 | h3
      · exact h3 h1
      · exact h3 h2
    · exact h
  have hpj : p ≠ j := by
    intro h; rw [h, hj] at hDp; norm_num at hDp
  set w : ι → ℂ := fun i => B j p * C i j - C j p * B i j with hw
  have hwex : ∃ q, w q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hind (-C j p) (B j p) (fun i => by
      have := hcon i; simp only [hw] at this; linear_combination this)
    rcases hp with h3 | h3
    · exact h3 h2
    · exact h3 (neg_eq_zero.mp h1)
  obtain ⟨t, q, hqp, htq, hwt⟩ : ∃ (t : ℂ) (q : ι), q ≠ p ∧ (t = 0 ∨ (D q = 1 ∧ q ≠ j)) ∧
      w p + t * w q ≠ 0 := by
    by_cases hwp : w p ≠ 0
    · exact ⟨0, j, Ne.symm hpj, Or.inl rfl, by simpa using hwp⟩
    push Not at hwp
    obtain ⟨q, hq⟩ := hwex
    have hqp : q ≠ p := fun h => hq (h ▸ hwp)
    have hDq : D q = 1 := by
      rcases hD01 q with h | h
      · exfalso; apply hq
        simp only [hw, (hZZ q j h hj).1, (hZZ q j h hj).2, mul_zero, sub_zero]
      · exact h
    have hqj : q ≠ j := fun h => by rw [h, hj] at hDq; norm_num at hDq
    exact ⟨1, q, hqp, Or.inr ⟨hDq, hqj⟩, by rw [hwp]; simpa using hq⟩
  set E := single p q (1 : ℂ)
  have hEE : E * E = 0 := single_mul_single_of_ne (1 : ℂ) p q p hqp 1
  set G := 1 + t • E
  set Gi := 1 - t • E
  have hGGi : G * Gi = 1 := by
    simp only [G, Gi, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hEE, smul_zero]
    abel
  have hGiG : Gi * G = 1 := by
    simp only [G, Gi, Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hEE, smul_zero]
    abel
  have hgg : ∀ M : Matrix ι ι ℂ, lrMul Gi G (lrMul G Gi M) = M := by
    intro M
    simp only [lrMul_apply]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul, Matrix.mul_assoc, hGiG,
      Matrix.mul_one]
  refine transfer (lrMul G Gi) (lrMul Gi G) (isR1_lrMul Gi G)
    (fun M hn => by
      rw [lrMul_apply, det_mul, det_mul, mul_right_comm,
        show Gi.det * G.det = 1 by rw [← det_mul, hGiG, det_one], one_mul]
      exact hn) (hgg _) (hgg _) (hgg _) ?_
  have hcomm : t • E * diagonal D = diagonal D * (t • E) := by
    ext a b
    simp only [Matrix.smul_apply, smul_eq_mul, E,
      mul_diagonal, diagonal_mul, single_apply]
    rcases htq with h | ⟨h, _⟩
    · simp [h]
    · by_cases hab : p = a ∧ q = b
      · obtain ⟨rfl, rfl⟩ := hab; simp [hDp, h]
      · simp [hab]
  have hGD : G * diagonal D = diagonal D * G := by
    simp only [G, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hcomm]
  have hdg : lrMul G Gi (diagonal D) = diagonal D := by
    rw [lrMul_apply, hGD, Matrix.mul_assoc, hGGi, Matrix.mul_one]
  rw [hdg]
  have hq' : t * (if j = q then (1 : ℂ) else 0) = 0 := by
    rcases htq with h | ⟨_, h⟩
    · simp [h]
    · simp [Ne.symm h]
  have entry : ∀ M : Matrix ι ι ℂ, lrMul G Gi M p j = M p j + t * M q j ∧
      lrMul G Gi M j p = M j p ∧ lrMul G Gi M j j = M j j := by
    intro M
    simp only [lrMul_apply, G, Gi, E, conj_apply]
    refine ⟨?_, ?_, ?_⟩
    · rcases htq with h | ⟨_, h⟩
      · simp [h]
      · simp [Ne.symm h]
    · simp [Ne.symm hpj, Ne.symm hqp]
    · rcases htq with h | ⟨_, h⟩
      · simp [h, Ne.symm hpj]
      · simp [Ne.symm h, Ne.symm hpj]
  obtain ⟨b1, b2, b3⟩ := entry B
  obtain ⟨c1, c2, c3⟩ := entry C
  refine stepB_pair D _ _ p j hpj hj (by rw [b3]; exact (hZZ j j hj hj).1)
    (by rw [c3]; exact (hZZ j j hj hj).2) ?_
  rw [b1, b2, c1, c2]
  intro h
  apply hwt
  simp only [hw]
  linear_combination h

end MaxCube.MatchedThree

namespace MaxCube.HighSelection

/-- Select a preimage with two nonzero images and a second preimage independent
in the first image. A fixed nonzero kernel vector supplies a third independent
coefficient vector. -/
private lemma choose_linear {E U V : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (A : E →ₗ[ℂ] U) (R : E →ₗ[ℂ] V) (q : E) (hq : q≠0) (hAq : A q=0)
    (rankA : 1<Module.finrank ℂ (LinearMap.range A)) (hR : R≠0) :
    ∃ b z : E, LinearIndependent ℂ ![q,b,z] ∧
      (∀ u v : ℂ, u • A b + v • A z = 0 → u=0 ∧ v=0) ∧ R b≠0 := by
  classical
  have hA : A≠0 := by
    intro h
    have hb := (LinearMap.range_eq_bot.mpr h)
    have dz : Module.finrank ℂ (LinearMap.range A)=0 :=
      (congrArg (fun W : Submodule ℂ U => Module.finrank ℂ W) hb).trans (finrank_bot ℂ U)
    omega
  obtain ⟨x,hx⟩ : ∃ x, A x≠0 := by
    by_contra! h
    exact hA (LinearMap.ext h)
  obtain ⟨y,hy⟩ : ∃ y, R y≠0 := by
    by_contra! h
    exact hR (LinearMap.ext h)
  obtain ⟨b,ab,rb⟩ : ∃ b, A b≠0 ∧ R b≠0 := by
    by_cases rx : R x=0
    · by_cases ay : A y=0
      · exact ⟨x+y,by simpa only [map_add,ay,add_zero] using hx,
          by simpa only [map_add,rx,zero_add] using hy⟩
      · exact ⟨y,ay,hy⟩
    · exact ⟨x,hx,rx⟩
  let u : LinearMap.range A := ⟨A b,b,rfl⟩
  have un : u≠0 := fun h => ab (congrArg Subtype.val h)
  obtain ⟨s,ind⟩ := exists_linearIndependent_pair_of_one_lt_finrank rankA un
  obtain ⟨z,hz⟩ := s.property
  have separate (c d : ℂ) (h : c • A b + d • A z=0) : c=0 ∧ d=0 := by
    have eq : c • u + d • s=0 := by
      apply Subtype.ext
      change c • A b + d • s.val=0
      rwa [← hz]
    have relation : ∑ i : Fin 2, (![c,d] : Fin 2 → ℂ) i • (![u,s] : Fin 2 → LinearMap.range A) i=0 := by
      simpa [Fin.sum_univ_two] using eq
    have all := Fintype.linearIndependent_iff.mp ind (![c,d] : Fin 2 → ℂ) relation
    exact ⟨all 0,all 1⟩
  refine ⟨b,z,?_,separate,rb⟩
  apply Fintype.linearIndependent_iff.mpr
  intro f hf i
  have sum : f 0 • q + f 1 • b + f 2 • z = 0 := by
    simpa [Fin.sum_univ_three,add_assoc] using hf
  have image : f 1 • A b + f 2 • A z=0 := by
    simpa only [map_add,map_smul,hAq,smul_zero,zero_add,map_zero] using congrArg A sum
  obtain ⟨h₁,h₂⟩ := separate _ _ image
  rw [h₁,h₂,zero_smul,zero_smul,add_zero,add_zero] at sum
  have h₀ := (smul_eq_zero.mp sum).resolve_right hq
  fin_cases i <;> assumption

open Matrix

/-- In normalized coordinates, the selected slices have independent j-columns
and the first one has a nonzero j-row. These are the input tests of CP3.stepB. -/
theorem choose {n : ℕ} (T : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (q : Fin n → ℂ) (D : Fin n → ℂ) (j : Fin n) (hq : q≠0)
    (hdiag : (∑ s, q s • T s) = Matrix.diagonal D) (hj : D j=0)
    (highColumn : 2≤(Matrix.of fun i s => T s i j).rank)
    (highRow : 2≤(Matrix.of fun k s => T s j k).rank) :
    ∃ b z : Fin n → ℂ, LinearIndependent ℂ ![q,b,z] ∧
      (∀ c₁ c₂ : ℂ, (∀ i, c₁*(∑ s, b s • T s) i j+c₂*(∑ s, z s • T s) i j=0) →
        c₁=0 ∧ c₂=0) ∧ ∃ p, (∑ s, b s • T s) j p≠0 := by
  classical
  let U := Matrix.of fun i s => T s i j
  let V := Matrix.of fun k s => T s j k
  have col (x : Fin n → ℂ) (i : Fin n) : U.mulVecLin x i=(∑ s,x s • T s) i j := by
    simp only [Matrix.mulVecLin_apply,U,Matrix.mulVec,dotProduct,Matrix.of_apply,Matrix.sum_apply,
      Matrix.smul_apply,smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have row (x : Fin n → ℂ) (i : Fin n) : V.mulVecLin x i=(∑ s,x s • T s) j i := by
    simp only [Matrix.mulVecLin_apply,V,Matrix.mulVec,dotProduct,Matrix.of_apply,Matrix.sum_apply,
      Matrix.smul_apply,smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have uq : U.mulVecLin q=0 := by
    funext i
    rw [col,hdiag]
    by_cases h : i=j
    · subst i
      simp [hj]
    · simp [h]
  change 2≤Module.finrank ℂ (LinearMap.range U.mulVecLin) at highColumn
  change 2≤Module.finrank ℂ (LinearMap.range V.mulVecLin) at highRow
  have rv : V.mulVecLin ≠ 0 := by
    intro h
    have hb := (LinearMap.range_eq_bot.mpr h)
    have dz : Module.finrank ℂ (LinearMap.range V.mulVecLin)=0 :=
      (congrArg (fun W : Submodule ℂ (Fin n → ℂ) => Module.finrank ℂ W) hb).trans (finrank_bot ℂ _)
    omega
  obtain ⟨b,z,ind,split,rb⟩ := choose_linear U.mulVecLin V.mulVecLin q hq uq highColumn rv
  refine ⟨b,z,ind,?_,?_⟩
  · intro c₁ c₂ h
    apply split
    funext i
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,col,Pi.zero_apply] using h i
  · by_contra! h
    apply rb
    funext i
    exact (row b i).trans (h i)

end MaxCube.HighSelection

namespace MaxCube.HighSelection

open Matrix

/-- A fixed column of the normalized slice pencil is the third-mode
contraction at the matching column of Q, followed by multiplication by P.
A fixed row similarly tests the second-mode contraction at the matching row of P. -/
theorem transport {n : ℕ} (T : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hP : P.det≠0) (hQ : Q.det≠0) (j : Fin n)
    (third : ∀ x : Fin n → ℂ, x≠0 → 2≤(Matrix.of (fun i s => ∑ k,x k*T s i k)).rank)
    (second : ∀ y : Fin n → ℂ, y≠0 → 2≤(Matrix.of (fun k s => ∑ i,y i*T s i k)).rank) :
    2≤(Matrix.of (fun i s => (P*T s*Q) i j)).rank ∧ 2≤(Matrix.of (fun k s => (P*T s*Q) j k)).rank := by
  classical
  have colNZ : (fun k => Q k j) ≠ 0 :=
    (Matrix.linearIndependent_cols_of_det_ne_zero hQ).ne_zero j
  have rowNZ : (fun i => P j i) ≠ 0 :=
    (Matrix.linearIndependent_cols_of_det_ne_zero
      (show P.transpose.det≠0 by rwa [Matrix.det_transpose])).ne_zero j
  let C := Matrix.of (fun i s => ∑ k,Q k j*T s i k)
  let R := Matrix.of (fun k s => ∑ i,P j i*T s i k)
  have cols : Matrix.of (fun i s => (P*T s*Q) i j) = P*C := by
    ext i s
    simp only [C,Matrix.of_apply,Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have rows : Matrix.of (fun k s => (P*T s*Q) j k) = Q.transpose*R := by
    ext k s
    simp only [R,Matrix.of_apply,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [cols,rows,Matrix.rank_mul_eq_right_of_det_ne_zero P C hP,
    Matrix.rank_mul_eq_right_of_det_ne_zero Q.transpose R (by rwa [Matrix.det_transpose])]
  exact ⟨third _ colNZ,second _ rowNZ⟩

theorem normalize_sum {n : ℕ} (T : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    (∑ s,x s • (P*T s*Q)) = P*(∑ s,x s • T s)*Q := by
  simp only [Finset.mul_sum,Finset.sum_mul,Matrix.mul_smul,Matrix.smul_mul]

end MaxCube.HighSelection

namespace MaxCube.HighSelection

/-- Select two companions to the prescribed singular contraction, using
only the original tensor's other two contraction-rank hypotheses. -/
theorem choose_normalized {n : ℕ} (T : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hP : P.det≠0) (hQ : Q.det≠0)
    (q : Fin n → ℂ) (D : Fin n → ℂ) (j : Fin n) (hq : q≠0)
    (hdiag : P*(∑ s,q s • T s)*Q=Matrix.diagonal D) (hj : D j=0)
    (third : ∀ x : Fin n → ℂ, x≠0 → 2≤(Matrix.of (fun i s => ∑ k,x k*T s i k)).rank)
    (second : ∀ y : Fin n → ℂ, y≠0 → 2≤(Matrix.of (fun k s => ∑ i,y i*T s i k)).rank) :
    ∃ b z : Fin n → ℂ, LinearIndependent ℂ ![q,b,z] ∧
      (∀ c₁ c₂ : ℂ, (∀ i, c₁*(P*(∑ s,b s • T s)*Q) i j+c₂*(P*(∑ s,z s • T s)*Q) i j=0) →
        c₁=0 ∧ c₂=0) ∧ ∃ p, (P*(∑ s,b s • T s)*Q) j p≠0 := by
  obtain ⟨hc,hr⟩ := transport T P Q hP hQ j third second
  obtain ⟨b,z,ind,sep,row⟩ := choose (fun s => P*T s*Q) q D j hq
    ((normalize_sum T P Q q).trans hdiag) hj hc hr
  refine ⟨b,z,ind,?_,?_⟩
  · simpa only [normalize_sum] using sep
  · simpa only [normalize_sum] using row

end MaxCube.HighSelection

namespace MaxCube.HighSelection

open Matrix CP3

/-- Choose three independent coefficient directions whose three unnormalized
slices admit a rank-one cover containing an invertible matrix. -/
theorem choose_regular_triple {n : ℕ} (T : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (q : Fin n → ℂ) (hq : q≠0) (singular : (∑ s,q s • T s).det=0)
    (third : ∀ x : Fin n → ℂ, x≠0 → 2≤(Matrix.of (fun i s => ∑ k,x k*T s i k)).rank)
    (second : ∀ y : Fin n → ℂ, y≠0 → 2≤(Matrix.of (fun k s => ∑ i,y i*T s i k)).rank) :
    ∃ b z : Fin n → ℂ, LinearIndependent ℂ ![q,b,z] ∧
      MatchedThree.RegCov (sp3 (∑ s,q s • T s) (∑ s,b s • T s) (∑ s,z s • T s)) (2*n-1) := by
  classical
  let A := ∑ s,q s • T s
  obtain ⟨P,Q,hP,hQ,D,hd,diag⟩ := normal_form A
  have zero : (diagonal D).det=0 := by rw [←diag,det_mul,det_mul]; change P.det * (∑ s,q s • T s).det * Q.det=0; rw [singular]; ring
  rw [det_diagonal,Finset.prod_eq_zero_iff] at zero
  obtain ⟨j,_,hj⟩ := zero
  obtain ⟨b,z,ind,sep,p,row⟩ := choose_normalized T P Q
    (isUnit_iff_ne_zero.mp hP) (isUnit_iff_ne_zero.mp hQ) q D j hq diag hj third second
  let B := ∑ s,b s • T s
  let Z := ∑ s,z s • T s
  let B' := P*B*Q
  let Z' := P*Z*Q
  have normalized : MatchedThree.RegCov (sp3 (diagonal D) B' Z') (2*Fintype.card (Fin n)-1) := by
    by_cases badB : ∃ u v, D u=0 ∧ D v=0 ∧ B' u v≠0
    · obtain ⟨u,v,hu,hv,h⟩ := badB
      exact MatchedThree.stepA D B' Z' u v hu hv h
    by_cases badZ : ∃ u v, D u=0 ∧ D v=0 ∧ Z' u v≠0
    · obtain ⟨u,v,hu,hv,h⟩ := badZ
      rw [sp3_swap (diagonal D) B' Z']
      exact MatchedThree.stepA D Z' B' u v hu hv h
    have block (u v : Fin n) (hu : D u=0) (hv : D v=0) : B' u v=0 ∧ Z' u v=0 :=
      ⟨by_contra fun h => badB ⟨u,v,hu,hv,h⟩,by_contra fun h => badZ ⟨u,v,hu,hv,h⟩⟩
    exact MatchedThree.stepB D hd B' Z' block j hj sep p (Or.inl row)
  refine ⟨b,z,?_⟩
  change LinearIndependent ℂ ![q,b,z] ∧ MatchedThree.RegCov (sp3 A B Z) (2*n-1)
  refine ⟨ind,?_⟩
  have recover (M : Matrix (Fin n) (Fin n) ℂ) : lrMul P⁻¹ Q⁻¹ (lrMul P Q M)=M := by
    simp only [lrMul_apply]
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hP,Matrix.one_mul,
      Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hQ,Matrix.mul_one]
  have preserves (M : Matrix (Fin n) (Fin n) ℂ) (hm : M.det≠0) :
      (lrMul P⁻¹ Q⁻¹ M).det≠0 := by
    rw [lrMul_apply,det_mul,det_mul,det_nonsing_inv,det_nonsing_inv]
    exact mul_ne_zero (mul_ne_zero (Ring.isUnit_iff_inverse_ne_zero.mp hP) hm)
      (Ring.isUnit_iff_inverse_ne_zero.mp hQ)
  apply MatchedThree.transfer (lrMul P Q) (lrMul P⁻¹ Q⁻¹) (isR1_lrMul _ _) preserves
    (recover A) (recover B) (recover Z)
  change MatchedThree.RegCov (sp3 (P*A*Q) B' Z') (2*n-1)
  rw [diag]
  simpa only [Fintype.card_fin] using normalized

end MaxCube.HighSelection

namespace MaxCube.HighSelection

open Matrix CP3

/-- A complex pencil on any two distinct coefficient directions has a nonzero
coefficient vector where its determinant vanishes. -/
theorem singular_direction {n : ℕ} (hn : 2≤n) (T : Fin n → Matrix (Fin n) (Fin n) ℂ) :
    ∃ q : Fin n → ℂ, q≠0 ∧ (∑ s,q s • T s).det=0 := by
  classical
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have ne : i≠j := fun h => (by decide : (0:ℕ)≠1) (congrArg Fin.val h)
  obtain ⟨x,y,nonzero,singular⟩ := CP3.sing_comb (T i) (T j) (by simpa using (show 0<n by omega))
  let q (s : Fin n) : ℂ := (if i=s then x else 0)+(if j=s then y else 0)
  have qi : q i=x := by simp [q,ne.symm]
  have qj : q j=y := by simp [q,ne]
  have nz : q≠0 := by
    intro zero
    rcases nonzero with hx|hy
    · exact hx (qi.symm.trans (congrFun zero i))
    · exact hy (qj.symm.trans (congrFun zero j))
  refine ⟨q,nz,?_⟩
  have eq : (∑ s,q s • T s) = x • T i+y • T j := by
    simp [q,add_smul,Finset.sum_add_distrib,ite_smul]
  rwa [eq]

/-- Under the two cross-mode rank conditions there is a regular rank-one
cover of three slices whose first-mode coefficient directions are independent. -/
theorem regular_triple_of_high {n : ℕ} (hn : 2≤n) (T : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (third : ∀ x : Fin n → ℂ, x≠0 → 2≤(Matrix.of (fun i s => ∑ k,x k*T s i k)).rank)
    (second : ∀ y : Fin n → ℂ, y≠0 → 2≤(Matrix.of (fun k s => ∑ i,y i*T s i k)).rank) :
    ∃ q b z : Fin n → ℂ, LinearIndependent ℂ ![q,b,z] ∧
      MatchedThree.RegCov (sp3 (∑ s,q s • T s) (∑ s,b s • T s) (∑ s,z s • T s)) (2*n-1) := by
  obtain ⟨q,hq,hs⟩ := singular_direction hn T
  exact ⟨q,choose_regular_triple T q hq hs third second⟩

end MaxCube.HighSelection

namespace MaxCube.RegularExtension

open Matrix

private lemma det_one_sub_outer {n : ℕ} (u v : Fin n → ℂ) :
    (1 - vecMulVec u v).det = 1 - (vecMulVec u v).trace := by
  have neg : vecMulVec (-u) v = -vecMulVec u v := by ext i j; simp [vecMulVec]
  rw [sub_eq_add_neg, ← neg, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]
  rw [dotProduct_neg, trace_vecMulVec, dotProduct_comm v u, sub_eq_add_neg]

private lemma det_remove {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ) (hL : L.det ≠ 0)
    (u v : Fin n → ℂ) :
    (L-vecMulVec u v).det = L.det*(1-(L⁻¹*vecMulVec u v).trace) := by
  have hu : IsUnit L.det := isUnit_iff_ne_zero.mpr hL
  have hprod : L*(1-L⁻¹*vecMulVec u v) = L-vecMulVec u v := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, L.mul_nonsing_inv hu, Matrix.one_mul]
  rw [← hprod, Matrix.det_mul, mul_vecMulVec, det_one_sub_outer]

/-- An invertible sum of finitely many rank-one matrices contains a
subsum of exactly n terms that is still invertible. If deleting every term
destroys invertibility, its contribution to the trace after normalization
is one, so the number of terms equals the trace of the identity. -/
theorem invertible_subsum {n : ℕ} {I : Type*} [DecidableEq I] (u v : I → Fin n → ℂ)
    (S : Finset I) (hinv : (∑ i ∈ S, vecMulVec (u i) (v i)).det ≠ 0) :
    ∃ s ⊆ S, s.card=n ∧ (∑ i ∈ s, vecMulVec (u i) (v i)).det ≠ 0 := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases count : S.card=n
    · exact ⟨S, Finset.Subset.rfl, count, hinv⟩
    let E (i : I) := vecMulVec (u i) (v i)
    let L := ∑ i ∈ S, E i
    have good : L.det ≠ 0 := hinv
    have can_remove : ∃ i∈S, (∑ t ∈ S.erase i, E t).det ≠ 0 := by
      by_contra! bad
      have share (i : I) (hi : i∈S) : (L⁻¹*E i).trace=1 := by
        have hiss : (∑ t ∈ S.erase i, E t) = L-E i :=
          eq_sub_of_add_eq (Finset.sum_erase_add _ _ hi)
        have hi' := bad i hi
        rw [hiss, det_remove L good (u i) (v i)] at hi'
        exact (sub_eq_zero.mp ((mul_eq_zero.mp hi').resolve_left good)).symm
      have htr : (S.card : ℂ) = (n : ℂ) := calc
        _ = ∑ i ∈ S, (L⁻¹*E i).trace := by
          rw [Finset.sum_congr rfl share]; simp
        _ = (L⁻¹*L).trace := by rw [show L⁻¹*L = ∑ i ∈ S, L⁻¹*E i from Matrix.mul_sum _ _ _, trace_sum]
        _ = _ := by rw [L.nonsing_inv_mul (isUnit_iff_ne_zero.mpr good), trace_one, Fintype.card_fin]
      exact count (by exact_mod_cast htr)
    obtain ⟨i,hi,hs⟩ := can_remove
    obtain ⟨s,hsub,hc,hdet⟩ := ih _ (Finset.erase_ssubset hi) hs
    exact ⟨s,hsub.trans (Finset.erase_subset _ _),hc,hdet⟩

/-- A single choice of n summands gives bases of both the column factors
and the row factors whenever one weighted sum is invertible. -/
theorem common_bases {n r : ℕ} (u v : Fin r → Fin n → ℂ) (α : Fin r → ℂ)
    (hinv : (∑ t, α t • vecMulVec (u t) (v t)).det ≠ 0) :
    ∃ f : Fin n → Fin r, Function.Injective f ∧
      IsUnit (Matrix.of (fun i j => u (f j) i)) ∧ IsUnit (Matrix.of (fun i j => v (f i) j)) := by
  classical
  let U (t : Fin r) := α t • u t
  have hE (t : Fin r) : vecMulVec (U t) (v t) = α t • vecMulVec (u t) (v t) := by
    ext i j
    simp [U, vecMulVec, smul_eq_mul, mul_assoc]
  obtain ⟨s,_,hc,hdet⟩ := invertible_subsum U v Finset.univ (by simpa only [hE] using hinv)
  let e : Fin n ≃ s := Fintype.equivOfCardEq (by simpa using hc.symm)
  let f (i : Fin n) : Fin r := e i
  let P := Matrix.of (fun i j => u (f j) i)
  let Q := Matrix.of (fun i j => v (f i) j)
  have hsum : P * diagonal (fun i => α (f i)) * Q = ∑ t ∈ s, vecMulVec (U t) (v t) := by
    calc
      _ = ∑ i : Fin n, vecMulVec (U (f i)) (v (f i)) := by
        ext i j
        rw [Matrix.mul_apply,Matrix.sum_apply]
        simp only [Matrix.mul_diagonal, P,Q,U, Matrix.of_apply, Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ t : s, vecMulVec (U t.val) (v t.val) := e.sum_comp (fun t : s => vecMulVec (U t.val) (v t.val))
      _ = _ := Finset.sum_coe_sort s (fun t => vecMulVec (U t) (v t))
  rw [← hsum, Matrix.det_mul, Matrix.det_mul] at hdet
  obtain ⟨hpq,hq⟩ := mul_ne_zero_iff.mp hdet
  exact ⟨f,Subtype.val_injective.comp e.injective,
    (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hpq).1),
    (Matrix.isUnit_iff_isUnit_det Q).mpr (isUnit_iff_ne_zero.mpr hq)⟩

end MaxCube.RegularExtension

namespace MaxCube.RegularExtension.PublishedPair

open Matrix Polynomial

theorem pert {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (d₁ d₂ : Fin n → ℂ) (x y : Fin n → Fin n → ℂ) (c : Fin n → ℂ),
      U + diagonal d₁ = ∑ l, vecMulVec (x l) (y l) ∧
      V + diagonal d₂ = ∑ l, c l • vecMulVec (x l) (y l) := by
  obtain ⟨d₁, d₂, -, hg⟩ := CP3.osl_all 0 n (Nat.zero_le n) U V
    ⟨by rw [Matrix.det_isEmpty]; exact one_ne_zero,
      by unfold CP3.penPoly; rw [Matrix.det_isEmpty]; exact separable_one⟩
  obtain ⟨x, y, c, h1, h2⟩ := CP3.nice_of_good _ _ hg
  exact ⟨d₁, d₂, x, y, c, h1, h2⟩

theorem base_eq {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) :
    P * diagonal d * Q = ∑ i, d i • vecMulVec (P *ᵥ Pi.single i 1) (Pi.single i 1 ᵥ* Q) := by
  rw [CP3.diag_sum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul]

/-- The perturbation lemma in the bases `(P, Q)`. -/
theorem pair_pert {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (hQ : IsUnit Q)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (x y : Fin n → Fin n → ℂ) (d₁ d₂ c : Fin n → ℂ),
      A = ∑ l, vecMulVec (x l) (y l) - P * diagonal d₁ * Q ∧
      B = ∑ l, c l • vecMulVec (x l) (y l) - P * diagonal d₂ * Q := by
  obtain ⟨d₁, d₂, x, y, c, h1, h2⟩ := pert (P⁻¹ * A * Q⁻¹) (P⁻¹ * B * Q⁻¹)
  have hPd : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP
  have hQd : IsUnit Q.det := (isUnit_iff_isUnit_det Q).mp hQ
  have conj : ∀ M : Matrix (Fin n) (Fin n) ℂ, P * (P⁻¹ * M * Q⁻¹) * Q = M := by
    intro M
    calc P * (P⁻¹ * M * Q⁻¹) * Q = (P * P⁻¹) * M * (Q⁻¹ * Q) := by
          simp only [Matrix.mul_assoc]
      _ = M := by
          rw [mul_nonsing_inv _ hPd, nonsing_inv_mul _ hQd, Matrix.one_mul, Matrix.mul_one]
  refine ⟨fun l => P *ᵥ x l, fun l => y l ᵥ* Q, d₁, d₂, c, ?_, ?_⟩
  · have h := congrArg (fun M => P * M * Q) h1
    simp only [Matrix.mul_add, Matrix.add_mul, conj, Matrix.mul_sum, Matrix.sum_mul,
      mul_vecMulVec, vecMulVec_mul] at h
    rw [← h]
    abel
  · have h := congrArg (fun M => P * M * Q) h2
    simp only [Matrix.mul_add, Matrix.add_mul, conj, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul] at h
    rw [← h]
    abel


end MaxCube.RegularExtension.PublishedPair

namespace MaxCube.RegularExtension

open Matrix

theorem decomp_of_span {m n r : ℕ} (T : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (u v : Fin r → Fin n → ℂ)
    (h : ∀ i, T i ∈ Submodule.span ℂ (Set.range fun t => vecMulVec (u t) (v t))) :
    Decomp m n n r T := by
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (h i)
  refine ⟨fun t i => a i t,u,v,?_⟩
  intro i j k
  have hc := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M j k) (ha i).symm
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply] using hc

/-- An invertible combination of the core slices permits a simultaneous
diagonal basis from the original rank-one summands. Each additional pair
requires only n new rank-one matrices. -/
theorem extended_cover {m n r k : ℕ} (S : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (A B : Fin k → Matrix (Fin n) (Fin n) ℂ) (core : Decomp m n n r S)
    (p : Fin m → ℂ) (regular : (∑ i, p i • S i).det ≠ 0) :
    ∃ u v : Fin (r+k*n) → Fin n → ℂ,
      let W := Submodule.span ℂ (Set.range fun t => vecMulVec (u t) (v t))
      (∀ i, S i ∈ W) ∧ ∀ l, A l ∈ W ∧ B l ∈ W := by
  classical
  obtain ⟨c,x,y,hs⟩ := core
  let F (t : Fin r) := vecMulVec (x t) (y t)
  have rep (i : Fin m) : S i = ∑ t, c t i • F t := by
    ext j l
    simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul, F, Matrix.vecMulVec_apply]
      using hs i j l
  let α (t : Fin r) := ∑ i, p i*c t i
  have hL : (∑ i, p i • S i) = ∑ t, α t • F t := by
    simp_rw [rep, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [show α t = ∑ i, p i*c t i from rfl, Finset.sum_smul]
  obtain ⟨f,_,hP,hQ⟩ := common_bases x y α (hL ▸ regular)
  let P := Matrix.of (fun i j => x (f j) i)
  let Q := Matrix.of (fun i j => y (f i) j)
  choose X Y d₁ d₂ μ hc₁ hc₂ using fun l => PublishedPair.pair_pert P Q hP hQ (A l) (B l)
  let e : Fin r ⊕ (Fin k × Fin n) ≃ Fin (r+k*n) :=
    (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv
  let U (t : Fin (r+k*n)) := (e.symm t).elim x (fun j => X j.1 j.2)
  let V (t : Fin (r+k*n)) := (e.symm t).elim y (fun j => Y j.1 j.2)
  let W := Submodule.span ℂ (Set.range fun t => vecMulVec (U t) (V t))
  have old (t : Fin r) : F t ∈ W := by
    apply Submodule.subset_span
    exact ⟨e (.inl t), by simp [U,V,F]⟩
  have new (l : Fin k) (i : Fin n) : vecMulVec (X l i) (Y l i) ∈ W := by
    apply Submodule.subset_span
    exact ⟨e (.inr (l,i)), by simp [U,V]⟩
  have diagonal_in (d : Fin n → ℂ) : P * diagonal d * Q ∈ W := by
    have eQ (i : Fin n) : Pi.single i 1 ᵥ* Q = y (f i) := by
      funext j
      simp [Q,Matrix.vecMul, dotProduct, Pi.single_apply, ite_mul]
    have eP (i : Fin n) : P *ᵥ Pi.single i 1 = x (f i) := by
      funext j
      simp [P,Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]
    rw [PublishedPair.base_eq]
    exact W.sum_mem fun i _ => W.smul_mem _ (by rw [eP,eQ]; exact old (f i))
  refine ⟨U,V,fun i => ?_,fun l => ⟨?_,?_⟩⟩
  · rw [rep]; exact W.sum_mem fun t _ => W.smul_mem _ (old t)
  · rw [hc₁]; exact W.sub_mem (W.sum_mem fun i _ => new l i) (diagonal_in _)
  · rw [hc₂]; exact W.sub_mem (W.sum_mem fun i _ => W.smul_mem _ (new l i)) (diagonal_in _)

/-- Extending any regular m-slice core by 2k arbitrary n-by-n slices
increases its exhibited length from r to at most r+kn. -/
theorem extend_pairs {m n r k : ℕ} (T : Fin (m+2*k) → Matrix (Fin n) (Fin n) ℂ)
    (core : Decomp m n n r (fun i => T (Fin.castAdd (2*k) i))) (p : Fin m → ℂ)
    (regular : (∑ i, p i • T (Fin.castAdd (2*k) i)).det ≠ 0) :
    Decomp (m+2*k) n n (r+k*n) T := by
  classical
  let e : Fin m ⊕ (Fin 2 × Fin k) ≃ Fin (m+2*k) :=
    (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv
  let S (j : Fin m) := T (Fin.castAdd (2*k) j)
  let A (l : Fin k) := T (e (.inr (0,l)))
  let B (l : Fin k) := T (e (.inr (1,l)))
  obtain ⟨u,v,hS,hAB⟩ := extended_cover S A B core p regular
  apply decomp_of_span T u v
  intro i
  obtain ⟨s,rfl⟩ := e.surjective i
  rcases s with j | ⟨j,l⟩
  · exact hS j
  · fin_cases j
    · exact (hAB l).1
    · exact (hAB l).2

end MaxCube.RegularExtension

namespace MaxCube.RegularExtension

open Matrix

/-- The regular matrix may be any weighted sum of the original rank-one
factors, including choices outside the span of the original tensor slices. -/
theorem extend_rankone_family {n r k : ℕ} (x y : Fin r → Fin n → ℂ)
    (A B : Fin k → Matrix (Fin n) (Fin n) ℂ) (α : Fin r → ℂ)
    (regular : (∑ t, α t • vecMulVec (x t) (y t)).det ≠ 0) :
    ∃ u v : Fin (r+k*n) → Fin n → ℂ,
      let W := Submodule.span ℂ (Set.range fun i => vecMulVec (u i) (v i))
      (∀ t, vecMulVec (x t) (y t) ∈ W) ∧ ∀ j, A j ∈ W ∧ B j ∈ W := by
  let S (t : Fin r) := vecMulVec (x t) (y t)
  have hs : Decomp r n n r S := by
    refine ⟨fun t i => if t=i then 1 else 0, x,y,?_⟩
    intro i j l
    simp [S, vecMulVec, ite_mul]
  exact extended_cover S A B hs α regular

/-- A regular finite rank-one cover extends over pairs of arbitrary matrices.
The output retains the entire span of the input cover. -/
theorem extend_regular_finset {n r k : ℕ} (s : Finset (Matrix (Fin n) (Fin n) ℂ))
    (card : s.card ≤ r) (pure : ∀ M∈s, CP3.IsR1 M)
    (regular : ∃ L∈Submodule.span ℂ (s : Set (Matrix (Fin n) (Fin n) ℂ)), L.det ≠ 0)
    (A B : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    ∃ u v : Fin (r+k*n) → Fin n → ℂ,
      let W := Submodule.span ℂ (Set.range fun i => vecMulVec (u i) (v i))
      Submodule.span ℂ (s : Set (Matrix (Fin n) (Fin n) ℂ)) ≤ W ∧ ∀ j, A j ∈ W ∧ B j ∈ W := by
  classical
  choose X Y hxy using fun M : s => pure M.val M.property
  let e : s ≃ Fin s.card := Fintype.equivFinOfCardEq (Fintype.card_coe _)
  let pad (f : s → Fin n → ℂ) (t : Fin r) : Fin n → ℂ :=
    if h : t.val<s.card then f (e.symm ⟨t.val,h⟩) else 0
  let x := pad X
  let y := pad Y
  let D (t : Fin r) := vecMulVec (x t) (y t)
  have incl : Submodule.span ℂ (s : Set (Matrix (Fin n) (Fin n) ℂ)) ≤ Submodule.span ℂ (Set.range D) := by
    apply Submodule.span_le.mpr
    intro M hM
    apply Submodule.subset_span
    let z : s := ⟨M,hM⟩
    refine ⟨Fin.castLE card (e z),?_⟩
    simp only [D,x,y,pad,Fin.val_castLE,dif_pos (e z).isLt]
    change vecMulVec (X (e.symm (e z))) (Y (e.symm (e z))) = M
    rw [e.symm_apply_apply]
    exact (hxy z).symm
  obtain ⟨L,hL,hdet⟩ := regular
  obtain ⟨α,hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (incl hL)
  obtain ⟨u,v,hD,hAB⟩ := extend_rankone_family x y A B α
    (show (∑ t, α t • D t).det ≠ 0 by rwa [hα])
  refine ⟨u,v,incl.trans (Submodule.span_le.mpr ?_),hAB⟩
  rintro _ ⟨i,rfl⟩
  exact hD i

/-- A matched cover for any chosen slice subspace can be used together with
k arbitrary slice pairs. It suffices that these spaces span the target slices. -/
theorem decomp_of_regular_span {m n r k : ℕ} (T : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (matched : ∃ s : Finset (Matrix (Fin n) (Fin n) ℂ),
      s.card ≤ r ∧ (∀ M∈s, CP3.IsR1 M) ∧ S ≤ Submodule.span ℂ (s : Set (Matrix (Fin n) (Fin n) ℂ)) ∧
        ∃ L∈Submodule.span ℂ (s : Set (Matrix (Fin n) (Fin n) ℂ)), L.det ≠ 0)
    (A B : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (cover : ∀ i, T i ∈ S ⊔ (Submodule.span ℂ (Set.range A) ⊔ Submodule.span ℂ (Set.range B))) :
    Decomp m n n (r+k*n) T := by
  obtain ⟨s,hc,hp,hS,hreg⟩ := matched
  obtain ⟨u,v,hs,hAB⟩ := extend_regular_finset s hc hp hreg A B
  apply decomp_of_span T u v
  have hA : Submodule.span ℂ (Set.range A) ≤ _ :=
    Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact (hAB j).1)
  have hB : Submodule.span ℂ (Set.range B) ≤ _ :=
    Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact (hAB j).2)
  exact fun i => (sup_le (hS.trans hs) (sup_le hA hB)) (cover i)

/-- Three independent coefficient vectors determine a core in a freely chosen
slice basis. A regular cover for that core extends over the 2k-dimensional
complement, independently of the original slice coordinates. -/
theorem decomp_of_matched_triple {n r k : ℕ}
    (T : Fin (3+2*k) → Matrix (Fin n) (Fin n) ℂ)
    (w : Fin 3 → Fin (3+2*k) → ℂ) (hw : LinearIndependent ℂ w)
    (matched : let M := fun i => ∑ t, w i t • T t
      ∃ s : Finset (Matrix (Fin n) (Fin n) ℂ), s.card ≤ r ∧ (∀ N∈s, CP3.IsR1 N) ∧
        CP3.sp3 (M 0) (M 1) (M 2) ≤ Submodule.span ℂ (s : Set (Matrix (Fin n) (Fin n) ℂ)) ∧
          ∃ L∈Submodule.span ℂ (s : Set (Matrix (Fin n) (Fin n) ℂ)), L.det≠0) :
    Decomp (3+2*k) n n (r+k*n) T := by
  classical
  let D := Fintype.linearCombination ℂ T
  let M (j : Fin 3) := D (w j)
  let W := CP3.sp3 (M 0) (M 1) (M 2)
  let E := Submodule.span ℂ (Set.range w)
  obtain ⟨C,hC⟩ := Submodule.exists_isCompl E
  have dimE : Module.finrank ℂ E = 3 := by simpa [E] using finrank_span_eq_card hw
  have dimC : Module.finrank ℂ C = 2*k := by
    have ht := Submodule.finrank_add_eq_of_isCompl hC
    rw [dimE, Module.finrank_pi, Fintype.card_fin] at ht
    omega
  let b := Module.finBasisOfFinrankEq ℂ C dimC
  let e : Fin 2 × Fin k ≃ Fin (2*k) := finProdFinEquiv
  let A (t : Fin k) := D ((b (e (0,t))).val)
  let B (t : Fin k) := D ((b (e (1,t))).val)
  let Y := W ⊔ (Submodule.span ℂ (Set.range A) ⊔ Submodule.span ℂ (Set.range B))
  have left : E ≤ Y.comap D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change M i ∈ Y
    apply (le_sup_left : W ≤ Y)
    fin_cases i
    · exact CP3.mem_sp3_1 _ _ _
    · exact CP3.mem_sp3_2 _ _ _
    · exact CP3.mem_sp3_3 _ _ _
  have right : C ≤ Y.comap D := by
    have allC : (⊤ : Submodule ℂ C) ≤ (Y.comap D).comap C.subtype := by
      rw [← b.span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change D ((b j).val) ∈ Y
      obtain ⟨⟨i,t⟩,rfl⟩ := e.surjective j
      fin_cases i
      · exact (le_sup_of_le_right le_sup_left : Submodule.span ℂ (Set.range A) ≤ Y)
          (Submodule.subset_span (Set.mem_range_self t))
      · exact (le_sup_of_le_right le_sup_right : Submodule.span ℂ (Set.range B) ≤ Y)
          (Submodule.subset_span (Set.mem_range_self t))
    intro z hz
    exact allC (show (⟨z,hz⟩ : C) ∈ (⊤ : Submodule ℂ C) from trivial)
  have full : (⊤ : Submodule ℂ (Fin (3+2*k) → ℂ)) ≤ Y.comap D := by
    rw [← hC.sup_eq_top]
    exact sup_le left right
  apply decomp_of_regular_span T W matched A B
  intro i
  have h := full (show Pi.single i (1 : ℂ) ∈ (⊤ : Submodule ℂ (Fin (3+2*k) → ℂ)) from trivial)
  change D (Pi.single i 1) ∈ Y at h
  simpa [D] using h

end MaxCube.RegularExtension

namespace MaxCube.OddCube

open Arxiv.«0805.3777»

private theorem extend_triple {n p : ℕ} (size : n = 3 + 2 * p)
    (T : Fin n → Matrix (Fin n) (Fin n) ℂ) (w : Fin 3 → Fin n → ℂ)
    (independent : LinearIndependent ℂ w)
    (cover : MatchedThree.RegCov (CP3.sp3 (∑ t, w 0 t • T t)
        (∑ t, w 1 t • T t) (∑ t, w 2 t • T t)) (2 * n - 1)) :
    Decomp n n n (2 * n - 1 + p * n) T := by
  subst n
  exact RegularExtension.decomp_of_matched_triple T w independent cover

/-- Every complex cube of odd side at least five is a sum of at most
`n(n+1)/2 - 1` simple tensors. -/
theorem decomp {k : ℕ} (hk : 2 ≤ k)
    (T : Fin (2*k+1) → Matrix (Fin (2*k+1)) (Fin (2*k+1)) ℂ) :
    Decomp (2*k+1) (2*k+1) (2*k+1) ((2*k+1)*(2*k+2)/2-1) T := by
  classical
  by_contra failure
  have large := OddLow.all_contractions_large hk T failure
  obtain ⟨q,b,z,independent,cover⟩ := HighSelection.regular_triple_of_high (by omega) T
    (fun x hx => by
      rw [← Matrix.rank_transpose]
      exact hk.trans (large x hx).2.2.le)
    (fun y hy => hk.trans (large y hy).2.1.le)
  have size : 2*k+1 = 3+2*(k-1) := by omega
  have all_slices := extend_triple size T ![q,b,z] independent cover
  have doubled : (2*k+1)*(2*k+2) = ((k+1)*(2*k+1))*2 := by ring
  have count : 2*(2*k+1)-1+(k-1)*(2*k+1) = (2*k+1)*(2*k+2)/2-1 := by
    rw [doubled, Nat.mul_div_cancel _ (by decide), show k+1=2+(k-1) by omega, Nat.add_mul]
    omega
  exact failure (count ▸ all_slices)

/-- The ordinary CP rank of any complex tensor of odd cubical format. -/
theorem cprank_le {n : ℕ} (hn : 5 ≤ n) (odd : Odd n) (T : Holor ℂ [n,n,n]) :
    T.cprank ≤ n*(n+1)/2-1 := by
  obtain ⟨k,rfl⟩ := odd
  let M (i j l : Fin (2*k+1)) := T ⟨[i.val,j.val,l.val],.cons i.isLt (.cons j.isLt (.cons l.isLt .nil))⟩
  have eq : coordinateHolor M = T := by
    funext idx
    obtain ⟨_,h⟩ := idx
    cases h with | cons _ h =>
      cases h with | cons _ h =>
        cases h with | cons _ h =>
          cases h
          rfl
  rw [← eq]
  exact (cprank_le_iff_decomp M _).mpr (decomp (by omega) M)

theorem max_rank_le {n R : ℕ} (hn : 5 ≤ n) (odd : Odd n) (hm : IsMaxRank [n,n,n] R) :
    R ≤ n*(n+1)/2-1 := by
  obtain ⟨T,rfl⟩ := hm.1
  exact cprank_le hn odd T

theorem cprank_five (T : Holor ℂ [5,5,5]) : T.cprank ≤ 14 :=
  cprank_le (by decide) ⟨2,rfl⟩ T

theorem cprank_seven (T : Holor ℂ [7,7,7]) : T.cprank ≤ 27 :=
  cprank_le (by decide) ⟨3,rfl⟩ T

end MaxCube.OddCube

namespace MaxCube.OddCube

open Arxiv.«0805.3777»

/-- The three-slice bound includes side three in the odd-cube estimate. -/
theorem cprank_le_of_three_le {n : ℕ} (hn : 3 ≤ n) (odd : Odd n) (T : Holor ℂ [n,n,n]) :
    T.cprank ≤ n*(n+1)/2-1 := by
  by_cases large : 5 ≤ n
  · exact cprank_le large odd T
  have three : n=3 := by
    obtain ⟨k,hk⟩ := odd
    omega
  subst n
  exact MaxCube.LowSlice.certified_three (by decide) T

theorem max_rank_le_of_three_le {n R : ℕ} (hn : 3 ≤ n) (odd : Odd n) (hm : IsMaxRank [n,n,n] R) :
    R ≤ n*(n+1)/2-1 := by
  obtain ⟨T,rfl⟩ := hm.1
  exact cprank_le_of_three_le hn odd T

end MaxCube.OddCube
