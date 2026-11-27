import OMAReductions.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1

/-!
Root a tree at one vertex and take a smallest total dominating set. The vertices
outside that set which have a child outside it, together with the set, cover every
edge, and those extra vertices inject into the dominating set.
-/

open SimpleGraph

theorem OMA.solution :
    OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H2 := by
  classical
  intro α _ _ T hT hcard
  have hnt : Nontrivial α :=
    (Fintype.one_lt_card_iff_nontrivial).mp (by omega)
  have hmin : T.minDegree = 1 := hT.minDegree_eq_one_of_nontrivial
  have hS : {n : ℕ | ∃ D : Finset α, T.IsTotalNDominatingSet n D}.Nonempty := by
    refine ⟨Fintype.card α, Finset.univ, ?_, by simp⟩
    intro v
    have hdeg : 0 < T.degree v := by
      have := T.minDegree_le_degree v
      omega
    obtain ⟨w, hw⟩ := (T.degree_pos_iff_exists_adj v).mp hdeg
    exact ⟨w, Finset.mem_univ _, hw⟩
  obtain ⟨D, hDom, hDcard⟩ := Nat.sInf_mem hS
  have hγ : D.card = T.totalDominationNumber := by
    simpa [SimpleGraph.totalDominationNumber] using hDcard
  inhabit α
  let r : α := default
  have hpath (v : α) : ∃ q : T.Walk v r, q.IsPath ∧ q.length = T.dist v r :=
    hT.connected.exists_path_of_dist v r
  let p (v : α) : T.Walk v r := Classical.choose (hpath v)
  have hp (v : α) : (p v).IsPath ∧ (p v).length = T.dist v r :=
    Classical.choose_spec (hpath v)
  let parent (v : α) : α := (p v).snd
  have dist_lt_of_mem {x z : α} (hz : z ∈ (p x).support) (hne : z ≠ x) :
      T.dist z r < T.dist x r := by
    obtain ⟨i, hi, hiz⟩ := List.mem_iff_getElem.mp hz
    have hi_le : i ≤ (p x).length := by
      have hlen := (p x).length_support
      omega
    have hget : (p x).getVert i = z := by
      rw [Walk.getVert_eq_support_getElem (p x) hi_le]
      simpa using hiz
    have hi0 : 0 < i := by
      by_contra h0
      have hiz0 : i = 0 := by omega
      have : z = x := by
        rw [← hget, hiz0, Walk.getVert_zero]
      exact hne this
    have hle := T.dist_le (((p x).drop i).copy hget rfl)
    rw [Walk.length_copy, Walk.drop_length] at hle
    have hlen := (hp x).2
    omega
  have not_on {x y : α} (hxy : T.Adj x y) (hlen : T.dist x r ≤ T.dist y r) :
      y ∉ (p x).support := by
    intro hy
    have hne : y ≠ x := hxy.ne.symm
    have hlt := dist_lt_of_mem hy hne
    omega
  have path_eq {x y : α} (hxy : T.Adj x y) (hlen : T.dist x r ≤ T.dist y r) :
      p y = (p x).cons hxy.symm := by
    have hcons : ((p x).cons hxy.symm).IsPath :=
      (Walk.cons_isPath_iff _ _).2 ⟨(hp x).1, not_on hxy hlen⟩
    exact (hT.existsUnique_path y r).unique (hp y).1 hcons
  have parent_eq {x y : α} (hxy : T.Adj x y) (hlen : T.dist x r ≤ T.dist y r) :
      y ≠ r ∧ parent y = x := by
    have heq := path_eq hxy hlen
    refine ⟨?_, ?_⟩
    · intro hyr
      have hlen0 : (p y).length = 0 := by
        rw [(hp y).2, hyr, T.dist_self]
      rw [heq, Walk.length_cons] at hlen0
      omega
    · change (p y).snd = x
      rw [heq, Walk.snd_cons]
  let P : Finset α := Finset.univ.filter fun u =>
    u ∉ D ∧ ∃ v, v ≠ r ∧ parent v = u ∧ v ∉ D
  have hv_ex (u : α) (hu : u ∈ P) : ∃ v, v ≠ r ∧ parent v = u ∧ v ∉ D :=
    (Finset.mem_filter.mp hu).2.2
  let vOf (u : α) (hu : u ∈ P) : α := Classical.choose (hv_ex u hu)
  have hvOf (u : α) (hu : u ∈ P) :
      vOf u hu ≠ r ∧ parent (vOf u hu) = u ∧ vOf u hu ∉ D :=
    Classical.choose_spec (hv_ex u hu)
  have hc_ex (u : α) (hu : u ∈ P) : ∃ c, parent c = vOf u hu ∧ c ∈ D := by
    have huD : u ∉ D := (Finset.mem_filter.mp hu).2.1
    obtain ⟨_hvr, hpv, _hvD⟩ := hvOf u hu
    let v := vOf u hu
    obtain ⟨w, hwD, hvw⟩ := hDom v
    have hw_ne : w ≠ u := fun hwu => huD (hwu ▸ hwD)
    have hlen : T.dist v r ≤ T.dist w r := by
      by_contra hlt
      have hle : T.dist w r ≤ T.dist v r := by omega
      have hpvw : parent v = w := (parent_eq hvw.symm hle).2
      exact hw_ne (hpvw.symm.trans hpv)
    exact ⟨w, (parent_eq hvw hlen).2, hwD⟩
  let f (u : α) : α :=
    if hu : u ∈ P then Classical.choose (hc_ex u hu) else r
  have hf_spec (u : α) (hu : u ∈ P) : parent (f u) = vOf u hu ∧ f u ∈ D := by
    simp only [f, dif_pos hu]
    exact Classical.choose_spec (hc_ex u hu)
  have hf_parent (u : α) (hu : u ∈ P) : parent (vOf u hu) = u :=
    (hvOf u hu).2.1
  have hinj : Set.InjOn f (P : Set α) := by
    intro u hu v hv hfeq
    have hu' : u ∈ P := by simpa using hu
    have hv' : v ∈ P := by simpa using hv
    have hcu := hf_spec u hu'
    have hcv := hf_spec v hv'
    have hchild_eq : vOf u hu' = vOf v hv' := by
      have hpu := hcu.1
      have hpv := hcv.1
      rw [hfeq] at hpu
      exact hpu.symm.trans hpv
    rw [← hf_parent u hu', ← hf_parent v hv', hchild_eq]
  have hfin (u : α) (hu : u ∈ P) : f u ∈ D := (hf_spec u hu).2
  have hPcard : P.card ≤ D.card :=
    Finset.card_le_card_of_injOn f (fun u hu => hfin u hu) hinj
  have hcover : T.IsVertexCover (↑(D ∪ P) : Set α) := by
    intro x y hxy
    by_cases hlen : T.dist x r ≤ T.dist y r
    · obtain ⟨hyr, hpy⟩ := parent_eq hxy hlen
      by_cases hx : x ∈ D
      · exact Or.inl (by simpa using Finset.mem_union_left P hx)
      · by_cases hy : y ∈ D
        · exact Or.inr (by simpa using Finset.mem_union_left P hy)
        · have hxP : x ∈ P := by
            refine Finset.mem_filter.mpr ⟨by simp, hx, y, hyr, hpy, hy⟩
          exact Or.inl (by simpa using Finset.mem_union_right D hxP)
    · have hlen' : T.dist y r ≤ T.dist x r := by omega
      obtain ⟨hxr, hpx⟩ := parent_eq hxy.symm hlen'
      by_cases hy : y ∈ D
      · exact Or.inr (by simpa using Finset.mem_union_left P hy)
      · by_cases hx : x ∈ D
        · exact Or.inl (by simpa using Finset.mem_union_left P hx)
        · have hyP : y ∈ P := by
            refine Finset.mem_filter.mpr ⟨by simp, hy, x, hxr, hpx, hx⟩
          exact Or.inr (by simpa using Finset.mem_union_right D hyP)
  have hvc : T.vertexCoverNum ≤ ((D ∪ P : Finset α) : Set α).encard :=
    hcover.vertexCoverNum_le
  rw [Set.encard_coe_eq_coe_finsetCard] at hvc
  have hto : T.vertexCoverNum.toNat ≤ (D ∪ P).card :=
    ENat.toNat_le_toNat hvc (by simp)
  have hunion : (D ∪ P).card ≤ 2 * D.card := by
    calc (D ∪ P).card ≤ D.card + P.card := Finset.card_union_le _ _
      _ ≤ D.card + D.card := Nat.add_le_add_left hPcard _
      _ = 2 * D.card := by omega
  rw [hγ] at hunion
  exact hto.trans hunion
