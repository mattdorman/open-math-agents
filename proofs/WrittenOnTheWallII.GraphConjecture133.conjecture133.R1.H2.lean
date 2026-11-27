import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1

/-!
A geodesic realizing the radius is an induced path on one more vertex than the
radius, whether or not the graph contains a four-cycle.
-/

open SimpleGraph

theorem OMA.solution :
    OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H2 := by
  intro α _ _ _ G hconn _
  have : Nonempty α := inferInstance
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  obtain ⟨p, hp, hlen⟩ := hconn.exists_path_of_dist u v
  have hget (k : Fin p.support.length) : p.support.get k = p.getVert k.val := by
    have hk : k.val ≤ p.length := by
      have hlenS := p.length_support
      omega
    rw [List.get_eq_getElem]
    exact (Walk.getVert_eq_support_getElem p hk).symm
  have hind : G.isInducedPath p.support := by
    refine ⟨hp.support_nodup, ?_⟩
    intro i j
    constructor
    · intro hadj
      by_contra hcons
      have hne : i.val ≠ j.val := by
        intro h
        have heq : p.support.get i = p.support.get j := by simp [h]
        exact hadj.ne heq
      have hlenS := p.length_support
      rcases Nat.lt_or_gt_of_ne hne with hij | hji
      · have hstep : i.val + 2 ≤ j.val := by
          have hnot : i.val + 1 ≠ j.val := by
            intro h
            exact hcons (Or.inl h)
          omega
        have hi : i.val ≤ p.length := by omega
        have hj : j.val ≤ p.length := by omega
        have hdu : G.dist u (p.getVert i.val) ≤ i.val := by
          have hwalk := G.dist_le (p.take i.val)
          simpa [Walk.take_length, hi] using hwalk
        have hdv : G.dist (p.getVert j.val) v ≤ p.length - j.val := by
          have hwalk := G.dist_le (p.drop j.val)
          simpa [Walk.drop_length] using hwalk
        have hchord : G.dist (p.getVert i.val) (p.getVert j.val) = 1 :=
          dist_eq_one_iff_adj.mpr (by
            have hadj' := hadj
            rwa [hget i, hget j] at hadj')
        have huj : G.dist u (p.getVert j.val) ≤ i.val + 1 := by
          have htri := hconn.dist_triangle (u := u) (v := p.getVert i.val)
            (w := p.getVert j.val)
          omega
        have huv' : G.dist u v ≤ i.val + 1 + (p.length - j.val) := by
          have htri := hconn.dist_triangle (u := u) (v := p.getVert j.val) (w := v)
          omega
        have hshort : i.val + 1 + (p.length - j.val) < p.length := by omega
        rw [hlen] at huv'
        omega
      · have hstep : j.val + 2 ≤ i.val := by
          have hnot : j.val + 1 ≠ i.val := by
            intro h
            exact hcons (Or.inr h)
          omega
        have hi : i.val ≤ p.length := by omega
        have hj : j.val ≤ p.length := by omega
        have hdu : G.dist u (p.getVert j.val) ≤ j.val := by
          have hwalk := G.dist_le (p.take j.val)
          simpa [Walk.take_length, hj] using hwalk
        have hdv : G.dist (p.getVert i.val) v ≤ p.length - i.val := by
          have hwalk := G.dist_le (p.drop i.val)
          simpa [Walk.drop_length] using hwalk
        have hchord : G.dist (p.getVert j.val) (p.getVert i.val) = 1 :=
          dist_eq_one_iff_adj.mpr (by
            have hadj' := hadj.symm
            rwa [hget j, hget i] at hadj')
        have hui : G.dist u (p.getVert i.val) ≤ j.val + 1 := by
          have htri := hconn.dist_triangle (u := u) (v := p.getVert j.val)
            (w := p.getVert i.val)
          omega
        have huv' : G.dist u v ≤ j.val + 1 + (p.length - i.val) := by
          have htri := hconn.dist_triangle (u := u) (v := p.getVert i.val) (w := v)
          omega
        have hshort : j.val + 1 + (p.length - i.val) < p.length := by omega
        rw [hlen] at huv'
        omega
    · intro hcons
      rcases hcons with h | h
      · have hi : i.val < p.length := by
          have hlenS := p.length_support
          omega
        have hadj := p.adj_getVert_succ hi
        have hsucc : p.getVert (i.val + 1) = p.getVert j.val := by simp [h]
        rw [hget i, hget j, ← hsucc]
        exact hadj
      · have hj : j.val < p.length := by
          have hlenS := p.length_support
          omega
        have hadj := (p.adj_getVert_succ hj).symm
        have hsucc : p.getVert (j.val + 1) = p.getVert i.val := by simp [h]
        rw [hget i, hget j, ← hsucc]
        exact hadj
  have hcard : p.support.length = G.radius.toNat + 1 := by
    rw [p.length_support, hlen, SimpleGraph.dist, huv]
  have hnat : G.radius.toNat + 1 ≤ path G := by
    simpa [hcard] using length_le_path_of_isInducedPath G p.support hind
  exact_mod_cast hnat
