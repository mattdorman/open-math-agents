import OMAReductions.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1

/-!
When the minimum degree is at least two, twice the radius divided by that degree
is at most the radius. A shortest path realizing the radius is an induced tree on
one more vertex, so the radius itself is at most the largest induced tree.
-/

theorem OMA.solution :
    OMA.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1.H2 := by
  intro α _ _ _ G _ hconn hpos hdeg
  have : Nonempty α := inferInstance
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  obtain ⟨p, hp, hlen⟩ := hconn.exists_path_of_dist u v
  have htree := SimpleGraph.Walk.induce_support_isTree_of_length_eq_dist p hlen
  have hcard : p.support.toFinset.card = G.radius.toNat + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support, hlen,
      SimpleGraph.dist, huv]
  have hnat : G.radius.toNat + 1 ≤ SimpleGraph.largestInducedTreeSize G := by
    simpa [hcard] using SimpleGraph.card_le_largestInducedTreeSize htree
  have hr : (G.radius.toNat : ℝ) ≤ (SimpleGraph.largestInducedTreeSize G : ℝ) := by
    exact_mod_cast Nat.le_of_succ_le hnat
  have hdiv : 2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (G.radius.toNat : ℝ) := by
    have hδ : (2 : ℝ) ≤ G.minDegree := by exact_mod_cast hdeg
    have hδpos : (0 : ℝ) < G.minDegree := by exact_mod_cast hpos
    have hmul : 2 * (G.radius.toNat : ℝ) ≤ (G.minDegree : ℝ) * (G.radius.toNat : ℝ) :=
      mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)
    calc 2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ)
        ≤ (G.minDegree : ℝ) * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) :=
          div_le_div_of_nonneg_right hmul hδpos.le
      _ = (G.radius.toNat : ℝ) := by field_simp
  exact hdiv.trans hr
