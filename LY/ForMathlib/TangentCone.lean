import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.GDelta.MetrizableSpace

open Set Filter Topology InnerProductSpace RealInnerProductSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
If a set `s` is the intersection of an open set `U` and a closed half-space `H`,
then the tangent cone to `s` at a point `y` that lies in `U` and on the boundary
of `H` is the half-space `H` translated to the origin. [YuriKudriashov]
-/
theorem posTangentConeAt_of_intersection_open_with_halfspace'
    (U : Set E) (hU : IsOpen U)
    (n : E)
    (y : E) (hy_on_boundary : ⟪y, n⟫ = 0)
    (hy_in_U : y ∈ U) :
    posTangentConeAt (U ∩ {z | ⟪z, n⟫ ≥ 0}) y = {d | ⟪d, n⟫ ≥ 0} := by
  refine' Set.Subset.antisymm _ _ <;> intro d hd <;> erw [ posTangentConeAt ] at * <;> simp_all
  · obtain ⟨w, h⟩ := hd
    obtain ⟨w_1, h⟩ := h
    obtain ⟨left, right⟩ := h
    obtain ⟨w_2, h⟩ := left
    obtain ⟨left, right⟩ := right
    -- By the continuity of the inner product, we have ⟪d, n⟫ = lim_{j → ∞} ⟪w_j • w_1 j, n⟫.
    have h_cont : Filter.Tendsto (fun j => ⟪w j • w_1 j, n⟫) Filter.atTop (nhds (⟪d, n⟫)) := by
      exact Filter.Tendsto.inner right tendsto_const_nhds;
    -- Since ⟪y + w_1 j, n⟫ ≥ 0 for all j ≥ w_2, and ⟪y, n⟫ = 0, it follows that ⟪w_1 j, n⟫ ≥ 0 for all j ≥ w_2.
    have h_nonneg : ∀ j ≥ w_2, ⟪w_1 j, n⟫ ≥ 0 := by
      intro j hj; specialize h j hj; simp_all +decide [ inner_add_left ] ;
    -- Since $w_j$ tends to infinity, for sufficiently large $j$, $w_j$ is positive. Therefore, for $j \geq w_2$ and sufficiently large, $⟪w_j • w_1 j, n⟫$ is non-negative.
    have h_pos : ∀ᶠ j in Filter.atTop, 0 ≤ ⟪w j • w_1 j, n⟫ := by
      filter_upwards [ left.eventually_gt_atTop 0, Filter.eventually_ge_atTop w_2 ] with j hj₁ hj₂ using by simpa only [ inner_smul_left ] using mul_nonneg hj₁.le ( h_nonneg j hj₂ ) ;
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_cont ( by filter_upwards [ h_pos ] with j hj; exact hj );
  · -- Choose $c_n = n$ and $d_n = \frac{1}{n} d$.
    use fun n => n, fun n => (1 / n : ℝ) • d;
    -- Show that the sequence $y + \frac{1}{n} d$ converges to $y$ and is eventually in $U$.
    have h_seq_conv : Filter.Tendsto (fun n : ℕ => y + (1 / (n : ℝ)) • d) Filter.atTop (nhds y) := by
      simpa using tendsto_const_nhds.add ( tendsto_inverse_atTop_nhds_zero_nat.smul_const d );
    exact ⟨ Filter.eventually_atTop.mp ( h_seq_conv.eventually ( hU.mem_nhds hy_in_U ) ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun n hn => ⟨ hN n hn, by simpa [ inner_add_left, inner_smul_left, hy_on_boundary ] using mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) hd ⟩ ⟩, tendsto_natCast_atTop_atTop, tendsto_const_nhds.congr' <| by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; simp +decide [ hn ] ⟩

/-- The tangent cone to a closed half-space at a point on its boundary is the
    half-space itself (translated to the origin). -/
theorem posTangentConeAt_halfspace
    (n : E)
    (y : E) (hy_on_boundary : ⟪y, n⟫ = 0) :
    let H := {z | ⟪z, n⟫ ≥ 0}
    posTangentConeAt H y = {d | ⟪d, n⟫ ≥ 0} := by
  let H_origin := {d | ⟪d, n⟫ ≥ 0}
  ext d
  constructor
  -- Part 1: (⊆) the tangent cone is a subset of the half-space.
  · intro hd_in_cone
    obtain ⟨c, y', hy', hc, hcd⟩ := hd_in_cone
    have hy'_in_H : ∀ᶠ k in atTop, y + y' k ∈ H_origin := hy'
    have h_inner_seq : ∀ᶠ k in atTop, ⟪y + y' k, n⟫ ≥ 0 := hy'_in_H
    have h_inner_y' : ∀ᶠ k in atTop, ⟪y' k, n⟫ ≥ 0 := by
      filter_upwards [h_inner_seq] with k hk
      rwa [inner_add_left, hy_on_boundary, zero_add] at hk
    -- From Tendsto c atTop atTop, we get eventually 0 < c k.
    have hc_pos : ∀ᶠ k in atTop, 0 < c k :=
      hc.eventually_gt_atTop 0
    have h_inner_smul : ∀ᶠ k in atTop, ⟪c k • y' k, n⟫ ≥ 0 := by
      filter_upwards [h_inner_y', hc_pos] with k h_inner h_c
      rw [inner_smul_left]
      exact mul_nonneg (le_of_lt h_c) h_inner
    -- Limit of ⟪c k • y' k, n⟫ is ⟪d, n⟫.
    have h_inner_lim : Tendsto (fun k => ⟪c k • y' k, n⟫) atTop (𝓝 ⟪d, n⟫) :=
      Filter.Tendsto.inner hcd tendsto_const_nhds
    -- Since eventually 0 ≤ ⟪c k • y' k, n⟫, pass to the limit to get 0 ≤ ⟪d, n⟫.
    have : 0 ≤ ⟪d, n⟫ :=
      le_of_tendsto_of_tendsto tendsto_const_nhds h_inner_lim h_inner_smul
    exact this
  -- Part 2: (⊇) the half-space is a subset of the tangent cone.
  · intro hd_in_halfspace
    use fun k => (k + 1 : ℝ)
    use fun k => (1 / (k + 1 : ℝ)) • d
    refine ⟨?_, ?_, ?_⟩
    -- `y + y' k` is eventually in the set `H`.
    · apply Eventually.of_forall
      intro k
      show ⟪y + (1 / (k + 1 : ℝ)) • d, n⟫ ≥ 0
      rw [inner_add_left, hy_on_boundary, zero_add, inner_smul_left]
      have h_pos : 0 ≤ (1 / (k + 1 : ℝ)) := by positivity
      exact mul_nonneg h_pos hd_in_halfspace
    -- the sequence of scalars `c k` tends to `+∞`.
    · have : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
        apply Tendsto.atTop_add
        · exact tendsto_natCast_atTop_atTop
        · exact tendsto_const_nhds
      exact this
    -- the sequence `c k • y' k` converges to `d`.
    · have hconst :
          (fun k : ℕ => ((k : ℝ) + 1) • ((1 / ((k : ℝ) + 1)) • d)) = (fun _ => d) := by
        funext k
        have hk_ne : ((k : ℝ) + 1) ≠ 0 := by
          have hk_pos : 0 < ((k : ℝ) + 1) :=
            add_pos_of_nonneg_of_pos (by exact_mod_cast (Nat.zero_le k)) zero_lt_one
          exact ne_of_gt hk_pos
        have hk_mul_one_div : ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1)) = (1 : ℝ) := by
          simpa [one_div] using (by simp_all only [ge_iff_le, mem_setOf_eq, ne_eq, not_false_eq_true, mul_inv_cancel₀])
        simp [smul_smul]; simp_all only [ge_iff_le, mem_setOf_eq, ne_eq, one_div, not_false_eq_true,
          mul_inv_cancel₀, one_smul]
      have : Tendsto (fun _ : ℕ => d) atTop (𝓝 d) := tendsto_const_nhds
      simp_all only [ge_iff_le, mem_setOf_eq, one_div, tendsto_const_nhds_iff]

/-- Intersecting with a neighborhood of `x` does not change the positive tangent cone. -/
lemma posTangentConeAt_inter_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : Set E) (x : E) (ht : t ∈ 𝓝 x) :
    posTangentConeAt (s ∩ t) x = posTangentConeAt s x := by
  apply le_antisymm
  · exact (posTangentConeAt_mono (a := x) (by intro z hz; exact hz.1))
  · intro y hy
    rcases hy with ⟨c, d, hd, hc, hcd⟩
    have hc' : Tendsto (fun n => ‖c n‖) atTop atTop :=
      tendsto_abs_atTop_atTop.comp hc
    have hd0 : Tendsto d atTop (𝓝 (0 : E)) :=
      tangentConeAt.lim_zero (l := atTop) hc' hcd
    have hx_add : Tendsto (fun n => x + d n) atTop (𝓝 x) := by
      simpa [add_zero] using tendsto_const_nhds.add hd0
    have h_in_t : ∀ᶠ n in atTop, x + d n ∈ t := hx_add.eventually ht
    refine ⟨c, d, (hd.and h_in_t).mono (by intro n h; exact ⟨h.1, h.2⟩), hc, hcd⟩

/--
If a set `s` is the intersection of an open set `U` and a closed half-space `H`,
then the tangent cone to `s` at a point `y` that lies in `U` and on the boundary
of `H` is the half-space `H` translated to the origin.
-/
theorem posTangentConeAt_of_intersection_open_with_halfspace
    (U : Set E) (hU : IsOpen U)
    (n : E)
    (y : E) (hy_on_boundary : ⟪y, n⟫ = 0)
    (hy_in_U : y ∈ U) :
    posTangentConeAt (U ∩ {z | ⟪z, n⟫ ≥ 0}) y = {d | ⟪d, n⟫ ≥ 0} := by
  have hremove :
      posTangentConeAt (U ∩ {z | ⟪z, n⟫ ≥ 0}) y =
        posTangentConeAt ({z | ⟪z, n⟫ ≥ 0}) y := by
    simpa [inter_comm] using
      posTangentConeAt_inter_nhds
        (s := {z | ⟪z, n⟫ ≥ 0}) (t := U) (x := y) (hU.mem_nhds hy_in_U)
  simpa [hremove] using posTangentConeAt_halfspace (n := n) (y := y) hy_on_boundary

open Set Metric

/-- A non-empty, proper, convex subset `s` of a finite-dimensional real normed vector space `E`
    has a non-empty relative frontier (i.e., its frontier within its own affine hull). -/
lemma Convex.exists_relative_boundary_point
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (_ : Convex ℝ s) (hs_nonempty : s.Nonempty)
    (hs_proper : (s : Set E) ≠ (affineSpan ℝ s : Set E)) :
    (frontier s ∩ (affineSpan ℝ s : Set E)).Nonempty := by
  -- Let H be the affine span of s
  set H : AffineSubspace ℝ E := affineSpan ℝ s with hH_def
  -- Since s ⊊ H, there exists p ∈ H \ s
  have h_sub : s ⊆ (H : Set E) := by
    simpa [hH_def] using (subset_spanPoints ℝ s)
  have h_ss : s ⊂ (H : Set E) := HasSubset.Subset.ssubset_of_ne h_sub hs_proper
  obtain ⟨p, hp_in_H, hp_notin_s⟩ := Set.exists_of_ssubset h_ss
  -- Take q ∈ s
  obtain ⟨q, hq_in_s⟩ := hs_nonempty
  -- Since p ∉ s and q ∈ s, we have p ≠ q
  have hpq_ne : p ≠ q := by
    intro h; exact hp_notin_s (h ▸ hq_in_s)
  -- Define I = {t ∈ [0,1] | lineMap p q t ∈ s}
  set I := {t ∈ Icc (0 : ℝ) 1 | AffineMap.lineMap (k := ℝ) p q t ∈ s} with hI_def
  -- 1 ∈ I since lineMap p q 1 = q ∈ s
  have hI_one_mem : (1 : ℝ) ∈ I := by
    refine ⟨right_mem_Icc.2 (show (0 : ℝ) ≤ 1 from zero_le_one), ?_⟩
    simpa [AffineMap.lineMap_apply_one] using hq_in_s
  have hI_nonempty : I.Nonempty := ⟨1, hI_one_mem⟩
  -- I is bounded below
  have hI_bdd : BddBelow I := ⟨0, fun t ht => ht.1.1⟩
  -- Let t₀ = inf I
  set t₀ := sInf I with ht₀_def
  have ht₀_mem_Icc : t₀ ∈ Icc (0 : ℝ) 1 := by
    refine ⟨?left, ?right⟩
    · -- 0 ≤ t₀
      exact le_csInf hI_nonempty (by intro t ht; exact ht.1.1)
    · -- t₀ ≤ 1
      exact csInf_le hI_bdd hI_one_mem
  -- Let z = lineMap p q t₀
  set z := AffineMap.lineMap (k := ℝ) p q t₀ with hz_def
  -- z ∈ H (as a point on segment [p,q] ⊆ H)
  have hq_in_H : q ∈ (H : Set E) := h_sub hq_in_s
  have hz_in_H : z ∈ (H : Set E) := by
    -- Affine map lineMap keeps you inside the affine subspace generated by endpoints
    simpa [hz_def] using (AffineMap.lineMap_mem (k := ℝ) (Q := H) t₀ hp_in_H hq_in_H)
  -- Build the witness x := z with z ∈ frontier s and z ∈ H
  refine ⟨z, ?hz_frontier, hz_in_H⟩
  -- Show z ∈ frontier s
  rw [frontier_eq_closure_inter_closure]
  constructor
  · -- z ∈ closure s
    -- Claim: t₀ ∈ closure I
    have ht₀_closure_I : t₀ ∈ closure I := by
      apply mem_closure_iff_nhds.2
      intro U hU
      obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.1 hU
      -- Find t ∈ I with t < t₀ + ε (since t₀ = inf I)
      have : ∃ t ∈ I, t < t₀ + ε := by
        by_contra! h
        have h' : ∀ t ∈ I, t₀ + ε ≤ t := h
        have : t₀ + ε ≤ t₀ :=
          ConditionallyCompleteLattice.le_csInf I (t₀ + ε) hI_nonempty h
        linarith
      obtain ⟨t, ht_mem, ht_lt⟩ := this
      refine ⟨t, ?_, ht_mem⟩
      apply hε_sub
      have : dist t₀ t < ε := by
        have hle : t₀ ≤ t := csInf_le hI_bdd ht_mem
        have hlt : t - t₀ < ε := by linarith
        have hnn : 0 ≤ t - t₀ := sub_nonneg.mpr hle
        have habs : |t - t₀| < ε := by simpa [abs_of_nonneg hnn] using hlt
        simpa [Real.dist_eq, abs_sub_comm] using habs
      exact mem_ball_comm.mp this
    -- Since lineMap is continuous and t₀ ∈ closure I, we have z ∈ closure (lineMap p q '' I)
    have hcont : Continuous (fun t : ℝ => AffineMap.lineMap (k := ℝ) p q t) := by
      -- use the continuity of the affine map lineMap directly
      simpa using (AffineMap.lineMap_continuous)
    have hz_cl : z ∈ closure (AffineMap.lineMap (k := ℝ) p q '' I) := by
      -- from t₀ ∈ closure I and continuity of lineMap, we get f '' closure I ⊆ closure (f '' I)
      have hsubset :
          (fun t : ℝ => AffineMap.lineMap (k := ℝ) p q t) '' closure I ⊆
            closure (AffineMap.lineMap (k := ℝ) p q '' I) :=
        image_closure_subset_closure_image hcont
      have hz_im : z ∈ (fun t : ℝ => AffineMap.lineMap (k := ℝ) p q t) '' closure I := by
        refine ⟨t₀, ht₀_closure_I, ?_⟩
        simp [hz_def]
      exact hsubset hz_im
    -- Since lineMap p q '' I ⊆ s, we have z ∈ closure s
    refine closure_mono (by
      intro x hx; rcases hx with ⟨t, ht, rfl⟩
      exact ht.2) hz_cl
  · -- z ∈ closure sᶜ
    -- We'll show: for any ε > 0, we can take t slightly less than t₀ (or p if t₀ = 0) so that lineMap p q t ∉ s and is ε-close to z.
    apply mem_closure_iff_nhds.2
    intro U hU
    obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.mem_nhds_iff.1 hU
    have hqp_pos : 0 < ‖q -ᵥ p‖ := by
      rw [norm_pos_iff]
      exact vsub_ne_zero.2 hpq_ne.symm
    by_cases h0 : t₀ = 0
    · -- Then z = p, and p ∉ s lies in every neighborhood of z
      refine ⟨p, ?_, ?_⟩
      · apply hε_sub
        simp [Metric.mem_ball, hz_def, h0, AffineMap.lineMap_apply (k := ℝ)]
        exact hε_pos
      · exact hp_notin_s
    · -- Take t slightly smaller than t₀
      have h0_pos : 0 < t₀ := lt_of_le_of_ne ht₀_mem_Icc.1 (Ne.symm h0)
      set δ := min (ε / (2 * ‖q -ᵥ p‖ + 1)) (t₀ / 2) with hδ_def
      have hδ_pos : 0 < δ := by
        have h1 : 0 < ε / (2 * ‖q -ᵥ p‖ + 1) := by
          apply div_pos hε_pos
          have : 0 < 2 * ‖q -ᵥ p‖ + 1 := by nlinarith [hqp_pos]
          exact this
        have h2 : 0 < t₀ / 2 := by
          have : 0 < t₀ := h0_pos
          linarith
        exact lt_min_iff.mpr ⟨h1, h2⟩
      set t := t₀ - δ with ht_def
      have ht_mem_Icc : t ∈ Icc (0 : ℝ) 1 := by
        constructor
        · -- 0 ≤ t
          have hδ_le_t0 : δ ≤ t₀ := by
            have : δ ≤ t₀ / 2 := min_le_right _ _
            linarith
          have : 0 ≤ t₀ - δ := by linarith
          simpa [ht_def] using this
        · -- t ≤ 1
          have : t ≤ t₀ := by linarith [hδ_pos.le]
          exact this.trans ht₀_mem_Icc.2
      have ht_notin_I : t ∉ I := by
        intro ht_in_I
        have ht0_le : t₀ ≤ t := csInf_le hI_bdd ht_in_I
        have hlt : t < t₀ := by linarith [hδ_pos]
        exact (lt_irrefl _ (lt_of_le_of_lt ht0_le hlt))
      refine ⟨AffineMap.lineMap (k := ℝ) p q t, ?_, ?_⟩
      · -- distance to z < ε
        apply hε_sub
        rw [Metric.mem_ball, dist_eq_norm_vsub]
        have hdiff : t₀ - t = δ := by simp [ht_def]
        have hnn : 0 ≤ t₀ - t := by simpa [hdiff] using hδ_pos.le
        have habs : |t - t₀| = δ := by
          have : |t - t₀| = |t₀ - t| := by simp [abs_sub_comm]
          simp [this, hdiff]
          exact le_of_le_of_eq hnn hdiff
        have hvsub :
          (AffineMap.lineMap (k := ℝ) p q t) -ᵥ z = (t - t₀) • (q -ᵥ p) := by
          calc
            (AffineMap.lineMap (k := ℝ) p q t) -ᵥ z
                = ((AffineMap.lineMap (k := ℝ) p q t) -ᵥ p) - ((AffineMap.lineMap (k := ℝ) p q t₀) -ᵥ p) := by
                  simpa [hz_def, sub_eq_add_neg]
                    using
                      (vsub_sub_vsub_cancel_right
                        (AffineMap.lineMap (k := ℝ) p q t)
                        (AffineMap.lineMap (k := ℝ) p q t₀)
                        p).symm
            _ = t • (q -ᵥ p) - t₀ • (q -ᵥ p) := by
                  simp_rw [@AffineMap.lineMap_vsub_left]
            _ = (t - t₀) • (q -ᵥ p) := by
                  simp [sub_smul]
        have hnorm :
            ‖(AffineMap.lineMap (k := ℝ) p q t) -ᵥ z‖
              = |t - t₀| * ‖q -ᵥ p‖ := by
          simp_rw [hvsub, norm_smul, Real.norm_eq_abs]
        calc
          ‖(AffineMap.lineMap (k := ℝ) p q t) -ᵥ z‖
              = |t - t₀| * ‖q -ᵥ p‖ := hnorm
          _ = δ * ‖q -ᵥ p‖ := by simp [habs]
          _ ≤ (ε / (2 * ‖q -ᵥ p‖ + 1)) * ‖q -ᵥ p‖ := by
                have hδ_le : δ ≤ ε / (2 * ‖q -ᵥ p‖ + 1) := min_le_left _ _
                exact mul_le_mul_of_nonneg_right hδ_le (norm_nonneg _)
          _ < ε := by
                have : 0 < ‖q -ᵥ p‖ := hqp_pos
                field_simp; nlinarith [this]
      · -- outside s
        exact fun h_in_s => ht_notin_I ⟨ht_mem_Icc, h_in_s⟩

open Module LinearMap ContinuousLinearMap FiniteDimensional

/-- Pencil of Hyperplanes (functional form with linear maps):
Let `W` be a subspace of codimension 2 in a finite-dimensional vector space `E`.
Then there exist two linearly independent linear functionals `f₁`, `f₂` on `E` whose kernels both contain `W`. -/
lemma exists_linearly_independent_functionals_of_codim_2
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (W : Subspace ℝ E) (h_codim : finrank ℝ (E ⧸ W) = 2) :
    ∃ f₁ f₂ : E →ₗ[ℝ] ℝ,
      LinearIndependent ℝ ![f₁, f₂] ∧ W ≤ LinearMap.ker f₁ ∧ W ≤ LinearMap.ker f₂ := by
  classical
  -- Work on the quotient
  set Q := E ⧸ W
  have h_dual_dim : finrank ℝ (Module.Dual ℝ Q) = 2 := by
    -- dual of a finite-dimensional space has the same finrank
    simpa [Subspace.dual_finrank_eq] using congrArg id h_codim
  -- A basis of Dual Q indexed by Fin 2
  let b0 := Module.finBasis ℝ (Module.Dual ℝ Q)
  have : (Fin (finrank ℝ (Module.Dual ℝ Q))) ≃ Fin 2 :=
    Fin.castOrderIso h_dual_dim
  let b : Basis (Fin 2) ℝ (Module.Dual ℝ Q) := b0.reindex this
  -- Pick the two basis vectors as functionals on Q
  let g₁ : Module.Dual ℝ Q := b ⟨0, by decide⟩
  let g₂ : Module.Dual ℝ Q := b ⟨1, by decide⟩
  have hg_li : LinearIndependent ℝ ![g₁, g₂] := by
    -- identify ![g₁, g₂] with the basis viewed as a function Fin 2 → _
    have hfun : (fun i : Fin 2 => b i) = ![g₁, g₂] := by
      funext i
      fin_cases i <;> simp [g₁, g₂]
    simpa [hfun] using b.linearIndependent
  -- Lift to functionals on E via precomposition with mkQ
  let f₁ : E →ₗ[ℝ] ℝ := g₁.comp W.mkQ
  let f₂ : E →ₗ[ℝ] ℝ := g₂.comp W.mkQ
  refine ⟨f₁, f₂, ?_, ?_, ?_⟩
  -- Linear independence of [f₁, f₂]
  · apply Fintype.linearIndependent_iff.mpr
    intro c hc
    have hcQ : c 0 • g₁ + c 1 • g₂ = 0 := by
      apply LinearMap.ext
      intro y
      rcases Submodule.mkQ_surjective W y with ⟨v, rfl⟩
      have := congrArg (fun (h : E →ₗ[ℝ] ℝ) => h v) hc
      simpa [f₁, f₂, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    have hcQsum : ∑ i, c i • ![g₁, g₂] i = 0 := by
      simpa [Fin.sum_univ_two] using hcQ
    exact (Fintype.linearIndependent_iff.mp hg_li) c hcQsum
-- W ≤ ker f₁
  · intro w hw
    have hm : (Submodule.mkQ W) w = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hw
    show g₁ ((Submodule.mkQ W) w) = 0
    rw [hm, map_zero]
  · intro w hw
    have hm : (Submodule.mkQ W) w = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hw
    show g₂ ((Submodule.mkQ W) w) = 0
    rw [hm, map_zero]

/-- A non-empty, proper, closed, convex subset `s` of a hyperplane `H` must have a
    non-empty boundary relative to `H`. -/
lemma exists_relative_boundary_point_of_closed_convex_in_hyperplane
    (H : AffineSubspace ℝ E)
    {s : Set E} (hs_subset : s ⊆ (H : Set E)) (hs_closed : IsClosed s) (_ : Convex ℝ s)
    (hs_nonempty : s.Nonempty) (hs_proper : s ≠ (H : Set E)) :
    (frontier s ∩ (H : Set E)).Nonempty := by
  -- Since s is a proper subset of H, there exists a point p in H but not in s.
  have h_ss : s ⊂ (H : Set E) := by
    exact HasSubset.Subset.ssubset_of_ne hs_subset hs_proper
  obtain ⟨p, hp_in_H, hp_outside_s⟩ := Set.exists_of_ssubset h_ss
  -- Since s is non-empty, there exists a point q in s.
  obtain ⟨q, hq_in_s⟩ := hs_nonempty
  -- Consider the segment [p, q]. Let I be the set of t in [0,1] for which lineMap p q t ∈ s.
  let I := {t ∈ Icc (0 : ℝ) 1 | AffineMap.lineMap (k := ℝ) p q t ∈ s}
  have hI_nonempty : I.Nonempty :=
    ⟨1, ⟨by norm_num, by simpa [AffineMap.lineMap_apply_one] using hq_in_s⟩⟩
  -- Let t₀ be the infimum of I and set z := lineMap p q t₀.
  let t₀ := sInf I
  let z := AffineMap.lineMap (k := ℝ) p q t₀
  -- The map t ↦ lineMap p q t is continuous. The set s is closed. So the preimage is closed, hence I is closed.
  have hI_closed : IsClosed I := by
    have hf : Continuous (fun t : ℝ => AffineMap.lineMap (k := ℝ) p q t) := by
      simpa using AffineMap.lineMap_continuous
    simpa [I, Set.preimage, Set.mem_setOf_eq] using
      (isClosed_Icc.inter (hs_closed.preimage hf))
  -- Since I is closed, non-empty, and bounded below, its infimum t₀ is in I.
  have hI_bdd : BddBelow I := ⟨0, fun t ht => ht.1.1⟩
  have ht₀_in_I : t₀ ∈ I := by
    simpa [t₀] using (hI_closed.csInf_mem hI_nonempty hI_bdd)
  -- This means the point z is in s.
  have hz_in_s : z ∈ s := ht₀_in_I.2
  -- z is in H because it's on a segment between two points of H.
  have hz_in_H : z ∈ (H : Set E) := by
    -- segment[p,q] ⊆ H
    have hseg : segment ℝ p q ⊆ (H : Set E) :=
      (H.convex).segment_subset hp_in_H (hs_subset hq_in_s)
    -- and z ∈ segment[p,q] since t₀ ∈ [0,1]
    have hz_seg : z ∈ segment ℝ p q := by
      rcases ht₀_in_I.1 with ⟨h0, h1⟩
      -- segment = image of lineMap on Icc 0 1
      have : z ∈ (fun t => AffineMap.lineMap (k := ℝ) p q t) '' Icc (0 : ℝ) 1 :=
        ⟨t₀, ⟨h0, h1⟩, rfl⟩
      simpa [segment_eq_image_lineMap] using this
    exact hseg hz_seg
  -- Build the witness x := z with z ∈ frontier s and z ∈ H
  refine ⟨z, ?hz_frontier, hz_in_H⟩
  -- Show z ∈ frontier s via closure s and closure sᶜ
  rw [frontier_eq_closure_inter_closure]
  constructor
  · -- z ∈ closure s
    -- Claim: t₀ ∈ closure I
    have ht₀_closure_I : t₀ ∈ closure I := by
      apply mem_closure_iff_nhds.2
      intro U hU
      obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.1 hU
      -- Find t ∈ I with t < t₀ + ε (since t₀ = inf I)
      have : ∃ t ∈ I, t < t₀ + ε := by
        by_contra! h
        -- Then t₀ + ε is a lower bound of I, hence t₀ + ε ≤ sInf I = t₀, contradicting ε > 0.
        have hle : t₀ + ε ≤ t₀ := by
          simpa [t₀] using (le_csInf hI_nonempty h)
        linarith
      obtain ⟨t, ht_mem, ht_lt⟩ := this
      refine ⟨t, ?_, ht_mem⟩
      apply hε_sub
      have : dist t₀ t < ε := by
        have hle : t₀ ≤ t := csInf_le hI_bdd ht_mem
        have hlt : t - t₀ < ε := by linarith
        have hnn : 0 ≤ t - t₀ := sub_nonneg.mpr hle
        have habs : |t - t₀| < ε := by simpa [abs_of_nonneg hnn] using hlt
        simpa [Real.dist_eq, abs_sub_comm] using habs
      exact mem_ball_comm.mp this
    -- Since lineMap is continuous and t₀ ∈ closure I, we have z ∈ closure (lineMap p q '' I)
    have hcont : Continuous (fun t : ℝ => AffineMap.lineMap (k := ℝ) p q t) := by
      simpa using (AffineMap.lineMap_continuous)
    have hz_cl : z ∈ closure (AffineMap.lineMap (k := ℝ) p q '' I) := by
      -- from t₀ ∈ closure I and continuity of lineMap, we get f '' closure I ⊆ closure (f '' I)
      have hsubset :
          (fun t : ℝ => AffineMap.lineMap (k := ℝ) p q t) '' closure I ⊆
            closure (AffineMap.lineMap (k := ℝ) p q '' I) :=
        image_closure_subset_closure_image hcont
      have hz_im : z ∈ (fun t : ℝ => AffineMap.lineMap (k := ℝ) p q t) '' closure I := by
        refine ⟨t₀, ht₀_closure_I, ?_⟩
        simp [z]
      exact hsubset hz_im
    -- Since lineMap p q '' I ⊆ s, we have z ∈ closure s
    refine closure_mono (by
      intro x hx; rcases hx with ⟨t, ht, rfl⟩
      exact ht.2) hz_cl
  · -- z ∈ closure sᶜ, via an ε–δ argument.
    apply mem_closure_iff_nhds.2
    intro U hU
    obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.mem_nhds_iff.1 hU
    by_cases h0 : t₀ = 0
    · -- Then z = p, and p ∉ s lies in every neighborhood of z
      refine ⟨p, ?_, ?_⟩
      · apply hε_sub
        have : dist z p = 0 := by simp [z, h0, AffineMap.lineMap_apply_zero]
        simpa [Metric.mem_ball, dist_comm] using lt_of_le_of_lt (le_of_eq this) hε_pos
      · exact hp_outside_s
    · -- Take t slightly smaller than t₀
      have h0_pos : 0 < t₀ := lt_of_le_of_ne (ht₀_in_I.1.1) (Ne.symm h0)
      -- set A = ‖q -ᵥ p‖ + 1 > 0
      set A : ℝ := ‖q -ᵥ p‖ + 1
      have hA_pos : 0 < A := by have := norm_nonneg (q -ᵥ p); nlinarith
      set δ := min (ε / (2 * A)) (t₀ / 2) with hδ_def
      have hδ_pos : 0 < δ := by
        have h1 : 0 < ε / (2 * A) := by
          have : 0 < 2 * A := by nlinarith [hA_pos]
          exact div_pos hε_pos this
        have h2 : 0 < t₀ / 2 := by nlinarith [h0_pos]
        exact lt_min_iff.mpr ⟨h1, h2⟩
      set t := t₀ - δ with ht_def
      have ht_mem_Icc : t ∈ Icc (0 : ℝ) 1 := by
        constructor
        · -- 0 ≤ t
          have : δ ≤ t₀ / 2 := min_le_right _ _
          have : 0 ≤ t₀ - δ := by linarith
          simpa [ht_def] using this
        · -- t ≤ 1
          have : t ≤ t₀ := by linarith [hδ_pos.le]
          exact this.trans ht₀_in_I.1.2
      have ht_notin_I : t ∉ I := by
        intro ht_in_I
        have ht0_le : t₀ ≤ t := csInf_le hI_bdd ht_in_I
        have hlt : t < t₀ := by linarith [hδ_pos]
        exact (lt_irrefl _ (lt_of_le_of_lt ht0_le hlt))
      refine ⟨AffineMap.lineMap (k := ℝ) p q t, ?_, ?_⟩
      · -- distance to z < ε
        apply hε_sub
        rw [Metric.mem_ball, dist_eq_norm_sub]
        -- compute the difference of lineMap at t and t₀
        have hvsub :
          (AffineMap.lineMap (k := ℝ) p q t) -ᵥ z = (t - t₀) • (q -ᵥ p) := by
          calc
            (AffineMap.lineMap (k := ℝ) p q t) -ᵥ z
                = ((AffineMap.lineMap (k := ℝ) p q t) -ᵥ p) - ((AffineMap.lineMap (k := ℝ) p q t₀) -ᵥ p) := by
                  simpa [z, sub_eq_add_neg]
                    using
                      (vsub_sub_vsub_cancel_right
                        (AffineMap.lineMap (k := ℝ) p q t)
                        (AffineMap.lineMap (k := ℝ) p q t₀)
                        p).symm
            _ = t • (q -ᵥ p) - t₀ • (q -ᵥ p) := by
                  simp_rw [@AffineMap.lineMap_vsub_left]
            _ = (t - t₀) • (q -ᵥ p) := by
                  simp [sub_smul]
        have hnorm :
            ‖(AffineMap.lineMap (k := ℝ) p q t) -ᵥ z‖
              = |t - t₀| * ‖q -ᵥ p‖ := by
          simp_rw [hvsub, norm_smul, Real.norm_eq_abs]
        -- switch to subtraction form to match the goal
        have hnorm' :
            ‖(AffineMap.lineMap (k := ℝ) p q t) - z‖
              = |t - t₀| * ‖q - p‖ := by
          simpa [vsub_eq_sub] using hnorm
        have hdiff : |t - t₀| = δ := by
          have : t₀ - t = δ := by simp [ht_def, sub_eq_add_neg]
          have hnn : 0 ≤ t₀ - t := by have := hδ_pos.le; simp only [sub_nonneg, ge_iff_le]; exact sub_le_self t₀ this
          calc
            |t - t₀| = |t₀ - t| := by simp [abs_sub_comm]
            _ = δ := by simp [this]; exact le_of_le_of_eq hnn this
        -- bound by ε
        have hδ_le : δ ≤ ε / (2 * A) := min_le_left _ _
        have hEpos : 0 ≤ ε / (2 * A) := by
          have : 0 ≤ 2 * A := by nlinarith [hA_pos.le]
          exact div_nonneg hε_pos.le this
        have hbound₁ : δ * ‖q -ᵥ p‖ ≤ (ε / (2 * A)) * ‖q -ᵥ p‖ :=
          mul_le_mul_of_nonneg_right hδ_le (norm_nonneg _)
        have hbound₂ : (ε / (2 * A)) * ‖q -ᵥ p‖ ≤ (ε / (2 * A)) * A := by
          have : ‖q -ᵥ p‖ ≤ A := by
            have : 0 ≤ (1 : ℝ) := by exact le_of_lt (zero_lt_one)
            have : ‖q -ᵥ p‖ ≤ ‖q -ᵥ p‖ + 1 := le_add_of_nonneg_right this
            simp [A]
          exact mul_le_mul_of_nonneg_left this hEpos
        have h2A_ne : 2 * A ≠ 0 := by exact mul_ne_zero two_ne_zero (ne_of_gt hA_pos)
        have hδmul_le : ‖q - p‖ * δ ≤ ε / 2 := by
          have hle : δ * ‖q -ᵥ p‖ ≤ (ε / (2 * A)) * A := hbound₁.trans hbound₂
          -- First, rewrite to match A * (ε / (2 * A)) on the RHS.
          have hle' : ‖q - p‖ * δ ≤ A * (ε / (2 * A)) := by
            simpa [vsub_eq_sub, mul_comm] using hle
          -- Then convert A * (ε / (2 * A)) to ε / 2.
          have hred : A * (ε / (2 * A)) = ε / 2 := by
            have : (ε / (2 * A)) * A = ε / 2 := by
              field_simp [h2A_ne, A]
            simpa [mul_comm] using this
          simpa [hred] using hle'
        -- finally, strict inequality
        have hlt : ‖q - p‖ * δ < ε := by
          have : ε / 2 < ε := by nlinarith
          exact lt_of_le_of_lt hδmul_le this
        simpa [hnorm', hdiff, mul_comm] using hlt
      · -- outside s
        exact fun h_in_s => ht_notin_I ⟨ht_mem_Icc, h_in_s⟩

open Set AffineSubspace
open scoped InnerProductSpace RealInnerProductSpace Affine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- In a finite-dimensional real inner product space, a nonempty, closed, convex set with
    empty interior is contained in an affine hyperplane. -/
lemma exists_affine_hyperplane_of_nonempty_of_interior_empty
    {s : Set E}
    (hs_convex : Convex ℝ s) (hs_nonempty : s.Nonempty) (_ : IsClosed s)
    (hs_int_empty : interior s = (∅ : Set E)) :
    ∃ H : AffineSubspace ℝ E, IsClosed (H : Set E) ∧
      (finrank ℝ (E ⧸ H.direction)) = 1 ∧
      s ⊆ (H : Set E) := by
  classical
  -- Let `A` be the affine span of `s`.
  set A : AffineSubspace ℝ E := affineSpan ℝ s
  have hs_sub_A : s ⊆ (A : Set E) := by
    simpa [A] using (subset_spanPoints ℝ s)
  -- If `A = ⊤`, then `interior s` is nonempty, contradiction.
  have hA_proper : (A : Set E) ≠ Set.univ := by
    intro hA_univ
    have hA_top : A = (⊤ : AffineSubspace ℝ E) := by
      apply SetLike.ext'
      simpa using hA_univ
    have hint : (interior s).Nonempty :=
      (Convex.interior_nonempty_iff_affineSpan_eq_top (V := E) (s := s) hs_convex).2
        (by simpa [A] using hA_top)
    simp [hs_int_empty] at hint
  -- Set the direction subspace.
  set U : Subspace ℝ E := A.direction
  -- Show `U ≠ ⊤`. If `U = ⊤`, then `A = ⊤` (using a base point from `s`).
  have hU_proper : U ≠ ⊤ := by
    intro hU
    -- pick a point a ∈ s ⊆ A
    rcases hs_nonempty with ⟨a, ha_s⟩
    have haA : a ∈ (A : Set E) := hs_sub_A ha_s
    -- Show (A : Set E) = univ
    have hA_univ : (A : Set E) = Set.univ := by
      ext x; constructor
      · intro _; trivial
      · intro _
        -- since U = ⊤, (x -ᵥ a) ∈ U
        have hx_dir : (x -ᵥ a) ∈ U := by
          have : (x -ᵥ a) ∈ (⊤ : Submodule ℝ E) := by simp
          simp [hU]
        -- then (x -ᵥ a) +ᵥ a ∈ A, hence x ∈ A
        have hx_mem : (x -ᵥ a) +ᵥ a ∈ A := A.vadd_mem_of_mem_direction hx_dir haA
        simpa [vsub_vadd] using hx_mem
    exact hA_proper hA_univ
  -- Work in the quotient Q := E ⧸ U and take a nonzero functional on Q.
  set Q := E ⧸ U
  have hpos : 0 < finrank ℝ Q := by
    classical
    -- pick v ∉ U since U ≠ ⊤
    have hExists : ∃ v : E, v ∉ U := by
      by_contra h
      have hall : ∀ v : E, v ∈ U := by
        intro v; by_contra hv; exact h ⟨v, hv⟩
      have : U = ⊤ := by
        ext x
        constructor
        · intro _; trivial
        · intro _; exact hall x
      exact hU_proper this
    rcases hExists with ⟨v, hv⟩
    have hvQ_ne : U.mkQ v ≠ (0 : Q) := by
      simpa [Submodule.Quotient.mk_eq_zero] using hv
    have : ∃ w : Q, w ≠ 0 := ⟨U.mkQ v, hvQ_ne⟩
    simp only [ne_eq] at this
    exact finrank_pos_iff_exists_ne_zero.mpr this
  let b : Basis (Fin (finrank ℝ Q)) ℝ Q := Module.finBasis ℝ Q
  let gQ : Module.Dual ℝ Q := b.coord ⟨0, hpos⟩
  -- Lift to a linear functional on E by precomposing with the quotient map.
  let g : E →ₗ[ℝ] ℝ := gQ.comp U.mkQ
  -- g is nonzero: evaluate at a preimage of the basis vector b ⟨0, _⟩ to get value 1.
  have hg_ne : g ≠ 0 := by
    classical
    obtain ⟨v, hv⟩ := Submodule.mkQ_surjective U (b ⟨0, hpos⟩)
    have h1 : g v = gQ (b ⟨0, hpos⟩) := by
      simp [g, LinearMap.comp_apply]
      simp_all only [coe_affineSpan, ne_eq, spanPoints_nonempty, direction_eq_top_iff_of_nonempty, Submodule.mkQ_apply,
        Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same, A, U, Q, b, gQ]
    have h2 : gQ (b ⟨0, hpos⟩) = 1 := by
      simp [gQ]
    intro hg
    have : 0 = 1 := by
      have hv1 : g v = 1 := h1.trans h2
      simp [hg] at hv1
    exact zero_ne_one this
  -- U ≤ ker g
  have hU_le_ker : U ≤ LinearMap.ker g := by
    intro u hu
    have hmk : U.mkQ u = 0 := by
      simpa [Submodule.Quotient.mk_eq_zero] using hu
    -- rewrite g u via the quotient and use hmk
    have : g u = gQ 0 := by
      simpa [g, LinearMap.comp_apply] using congrArg (fun x => gQ x) hmk
    simpa [map_zero] using this
  -- Pick a base point a ∈ A from s to describe the affine hyperplane {x | g (x - a) = 0}.
  rcases hs_nonempty with ⟨a, ha_s⟩
  have haA : a ∈ (A : Set E) := hs_sub_A ha_s
  -- Define the hyperplane H := { x | g (x - a) = 0 }.
  let H : AffineSubspace ℝ E :=
  { carrier := { x | g (x - a) = 0 }
    smul_vsub_vadd_mem := by
      intro c p1 p2 p3 hp1 hp2 hp3
      have hp1' : g (p1 - a) = 0 := hp1
      have hp2' : g (p2 - a) = 0 := hp2
      have hp3' : g (p3 - a) = 0 := hp3
      have h_sub : g (p1 - p2) = 0 := by
        calc
          g (p1 - p2)
              = g ((p1 - a) + (a - p2)) := by rw [@sub_add_sub_cancel]
          _ = g (p1 - a) + g (a - p2) := by simp
          _ = 0 := by
            have h_ap2 : g (a - p2) = 0 := by
              calc g (a - p2) = g (-(p2 - a)) := by rw [@neg_sub]
                _ = -g (p2 - a) := by simp
                _ = 0 := by simp [hp2']
            simp [hp1', h_ap2]
      have : g (c • (p1 - p2) + (p3 - a)) = 0 := by
        simp [LinearMap.map_add, h_sub, hp3']
      show c • (p1 -ᵥ p2) +ᵥ p3 ∈ { x | g (x - a) = 0 }
      simp_all only [coe_affineSpan, ne_eq, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_sub, Basis.coord_apply, map_sub, Finsupp.coe_sub, Pi.sub_apply, mem_setOf_eq,
        Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, vsub_eq_sub, vadd_eq_add, zero_add, A, U, g, Q,
        gQ, b] }
  -- s ⊆ H
  have hs_sub_H : s ⊆ (H : Set E) := by
    intro x hx
    have hxA : x ∈ (A : Set E) := hs_sub_A hx
    -- x - a ∈ U since x, a ∈ A
    have hx_dir : x -ᵥ a ∈ U := by
      -- vsub_mem_direction : for x,a ∈ A, x -ᵥ a ∈ A.direction
      simpa [A, vsub_eq_sub] using (A.vsub_mem_direction hxA haA)
    -- hence g (x - a) = 0 because U ≤ ker g
    have : g (x - a) = 0 := by
      have hx_dir' : x - a ∈ U := by simpa [vsub_eq_sub] using hx_dir
      exact (LinearMap.mem_ker.mp (hU_le_ker hx_dir'))
    -- membership in H
    simpa [H] using this
  -- H is closed as a preimage of {0} under a continuous map.
  have hH_closed : IsClosed (H : Set E) := by
    have hcont : Continuous fun x : E => g (x - a) :=
      (g.continuous_of_finiteDimensional).comp (continuous_id.sub continuous_const)
    have : IsClosed ((fun x : E => g (x - a)) ⁻¹' ({0} : Set ℝ)) :=
      IsClosed.preimage hcont isClosed_singleton
    simpa [H, Set.preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] using this
  -- Identify the direction of H with ker g.
  have hdir_eq : H.direction = LinearMap.ker g := by
    -- First inclusion: H.direction ⊆ ker g.
    have h₁ : H.direction ≤ LinearMap.ker g := by
      intro v hv
      -- a ∈ H (since g (a - a) = g 0 = 0)
      have haH : a ∈ (H : Set E) := by
        show g (a - a) = 0
        simp
      -- v +ᵥ a ∈ H
      have hvaH : v +ᵥ a ∈ (H : Set E) := H.vadd_mem_of_mem_direction hv haH
      -- therefore g v = 0
      have : g ((v +ᵥ a) - a) = 0 := hvaH
      have : g v = 0 := by simpa [vadd_vsub_assoc, vsub_eq_sub] using this
      exact LinearMap.mem_ker.mpr this
    -- Second inclusion: ker g ⊆ H.direction.
    have h₂ : LinearMap.ker g ≤ H.direction := by
      intro v hv
      -- a ∈ H and v +ᵥ a ∈ H (since g v = 0)
      have haH : a ∈ (H : Set E) := by
        show g (a - a) = 0
        simp
      have hvH : v +ᵥ a ∈ (H : Set E) := by
        have : g v = 0 := (LinearMap.mem_ker.mp hv)
        show g ((v +ᵥ a) - a) = 0
        simpa [vadd_vsub_assoc, vsub_eq_sub] using this
      -- Hence (v +ᵥ a) -ᵥ a ∈ H.direction, i.e., v ∈ H.direction.
      convert H.vsub_mem_direction hvH haH using 1
      simp only [vadd_eq_add, vsub_eq_sub, add_sub_cancel_right]
    exact le_antisymm h₁ h₂
  -- The quotient by H.direction has finrank 1 (since range g = ⊤).
  have h_codim_one : finrank ℝ (E ⧸ H.direction) = 1 := by
    -- E ⧸ ker g ≃ range g, hence equal finranks
    have hfinrank :
        finrank ℝ (E ⧸ LinearMap.ker g) = finrank ℝ (LinearMap.range g) := by
      simpa using (LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange g))
    classical
    obtain ⟨v, hv⟩ := Submodule.mkQ_surjective U (b ⟨0, hpos⟩)
    have hgv_eq : g v = gQ (b ⟨0, hpos⟩) := by
      simp [g, LinearMap.comp_apply]
      exact congrArg (⇑gQ) hv
    have hgv1 : g v = 1 := by
      have : gQ (b ⟨0, hpos⟩) = 1 := by
        simp [gQ]
      exact hgv_eq.trans this
    have hsurj : Function.Surjective g := by
      intro r
      refine ⟨r • v, ?_⟩
      simp [hgv1]
    have hRangeTop : LinearMap.range g = ⊤ := by
      -- surjective ⇒ range = ⊤
      apply top_unique
      intro y _
      rcases hsurj y with ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    have hquot_one : finrank ℝ (E ⧸ LinearMap.ker g) = 1 := by
      calc
        finrank ℝ (E ⧸ LinearMap.ker g)
            = finrank ℝ (LinearMap.range g) := by simpa using hfinrank
        _ = finrank ℝ (⊤ : Submodule ℝ ℝ) := by rw [hRangeTop]
        _ = finrank ℝ ℝ := by
              simp
        _ = 1 := by simp
    rw [hdir_eq]
    exact hquot_one
  refine ⟨H, hH_closed, h_codim_one, hs_sub_H⟩

-- Frontier points are not in the interior
lemma not_mem_interior_of_mem_frontier {E : Type*} [TopologicalSpace E] {s : Set E} {z : E}
    (hz : z ∈ frontier s) : z ∉ interior s := by
  have hz' : z ∈ closure s \ interior s := by simp_all only [closure_diff_interior]
  exact hz'.2

open Set Filter Topology InnerProductSpace RealInnerProductSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every set is contained in its double inner dual. -/
lemma subset_innerDual_innerDual (S : Set E) :
    S ⊆ ((ProperCone.innerDual ((ProperCone.innerDual S : Set E)) : ProperCone ℝ E) : Set E) := by
  intro y hy
  change ∀ x ∈ ((ProperCone.innerDual S : ProperCone ℝ E) : Set E), 0 ≤ ⟪x, y⟫_ℝ
  intro x hx
  have : 0 ≤ ⟪y, x⟫_ℝ := (ProperCone.mem_innerDual.mp hx) hy
  simpa [real_inner_comm] using this

/-- The cone of rays from `z` to `s` sits inside its double inner dual. -/
lemma rayCone_subset_doubleDual (s : Set E) (z : E) :
    {d : E | ∃ y ∈ s, ∃ t : ℝ, 0 ≤ t ∧ d = t • (y - z)}
      ⊆ ((ProperCone.innerDual
            ((ProperCone.innerDual {d : E | ∃ y ∈ s, ∃ t : ℝ, 0 ≤ t ∧ d = t • (y - z)} : Set E))
          : ProperCone ℝ E) : Set E) := by
  simpa using
    (subset_innerDual_innerDual
      (S := {d : E | ∃ y ∈ s, ∃ t : ℝ, 0 ≤ t ∧ d = t • (y - z)}))


open Set AffineSubspace
open Set Filter Topology InnerProductSpace RealInnerProductSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Supporting vector at a boundary point of a closed convex set when `interior s` is nonempty. -/
theorem exists_supporting_hyperplane_of_closed_convex_of_nonempty_interior
  {s : Set E} (hs_conv : Convex ℝ s) (_hs_closed : IsClosed s)
  {z : E} (_ : z ∈ s) (hz_not_int : z ∉ interior s)
  (hInt : (interior s).Nonempty) :
  ∃ v : E, v ≠ 0 ∧ ∀ y ∈ s, ⟪y - z, v⟫ ≤ 0 := by
  classical
  -- interior s is open convex, z ∉ interior s
  have h_int_open : IsOpen (interior s) := isOpen_interior
  have h_int_conv : Convex ℝ (interior s) := hs_conv.interior
  -- Separate z from interior s: ∃ f₀ with f₀ z < f₀ x for all x ∈ interior s
  obtain ⟨f₀, hlt₀⟩ :=
    geometric_hahn_banach_point_open (ht₁ := h_int_conv) (ht₂ := h_int_open) (disj := hz_not_int)
  -- Flip the sign so that we get g x < g z for interior points x
  let g : E →L[ℝ] ℝ := -f₀
  -- g ≠ 0 since there is strict inequality at some interior point
  obtain ⟨x₀, hx₀⟩ := hInt
  have hg_ne : g ≠ 0 := by
    have hx_lt : g x₀ < g z := by
      have h := hlt₀ x₀ hx₀
      simpa [g] using (neg_lt_neg_iff.mpr h)
    intro hg
    have H : (0 : ℝ) < 0 := by
      simp [hg] at hx_lt
    simpa using H.false
  -- Riesz representation v with g x = ⟪x, v⟫
  let v : E := (InnerProductSpace.toDual ℝ E).symm g
  have hv_ne : v ≠ 0 := by
    intro hv
    -- (toDual v) = 0 → g = 0 via apply_symm_apply
    have hmap : (InnerProductSpace.toDual ℝ E) v = 0 :=
      (InnerProductSpace.toDual ℝ E).map_eq_zero_iff.mpr hv
    have hTo : (InnerProductSpace.toDual ℝ E) v = g := by
      simp [v]
    exact hg_ne (by simpa [hTo] using hmap)
  -- For any y ∈ s, build points in interior s approaching y, and pass to the limit
  have h_le_all : ∀ y ∈ s, g y ≤ g z := by
    intro y hy
    -- openSegment y x₀ ⊆ interior s for convex s with x₀ ∈ interior s and y ∈ s
    have hopenSeg : openSegment ℝ y x₀ ⊆ interior s :=
      Convex.openSegment_self_interior_subset_interior hs_conv hy hx₀
    --  hs_conv.openSegment_subset_interior hy hx₀
    -- Take tₙ = (n+2)⁻¹ → 0; pₙ := (1 - tₙ) y + tₙ x₀ ∈ interior s
    let t : ℕ → ℝ := fun n => (n + 2 : ℝ)⁻¹
    have ht_pos : ∀ n, 0 < t n := by
      intro n
      have : 0 < (n : ℝ) + 2 := by
        exact add_pos_of_nonneg_of_pos (by exact_mod_cast Nat.cast_nonneg n) (by norm_num)
      simpa [t, add_comm, add_left_comm, add_assoc] using inv_pos.mpr this
    have ht_lt_one : ∀ n, t n < (1 : ℝ) := by
      intro n
      -- 2 ≤ n+2 ⇒ (n+2)⁻¹ ≤ 1/2 < 1
      have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.cast_nonneg n
        linarith
      have hle : t n ≤ (1 / 2 : ℝ) := by
        have hpos2 : 0 < (2 : ℝ) := by norm_num
        simpa [t, add_comm, add_left_comm, add_assoc] using
          (one_div_le_one_div_of_le hpos2 hn2)
      exact lt_of_le_of_lt hle (by norm_num : (1 / 2 : ℝ) < 1)
    have hp_mem : ∀ n, ((1 - t n) • y + t n • x₀) ∈ interior s := by
      intro n
      have : (1 - t n) • y + t n • x₀ ∈ openSegment ℝ y x₀ := by
        -- openSegment ℝ y x₀ = {a • y + b • x₀ | 0 < a ∧ 0 < b ∧ a + b = 1}
        refine ⟨1 - t n, t n, ?_, ?_, ?_, rfl⟩
        · exact sub_pos.mpr (ht_lt_one n)
        · exact ht_pos n
        · have : 1 - t n + t n = (1 : ℝ) := by
            simp [sub_eq_add_neg]
          simp [add_comm]
      exact hopenSeg this
    -- pₙ → y
    have htendsto0 : Tendsto t atTop (𝓝 0) := by
      -- (n ↦ n+2) tends to atTop; compose with inverse tends to 0
      have h2 : Tendsto (fun n : ℕ => n + 2) atTop atTop :=
        tendsto_atTop_atTop_of_monotone
          (f := fun n : ℕ => n + 2)
          (by
            intro a b h; exact add_le_add_right h 2)
          (by
            intro b; exact ⟨b, Nat.le_add_right _ _⟩)
      have hcomp :
          (fun n : ℕ => (↑n + 2 : ℝ)⁻¹)
            = ((fun n : ℕ => (↑n : ℝ)⁻¹) ∘ fun n : ℕ => n + 2) := by
        funext n; simp [Function.comp, Nat.cast_add, Nat.cast_ofNat]
      simpa [t, hcomp] using (tendsto_inverse_atTop_nhds_zero_nat.comp h2)
    have h_tendsto_y :
        Tendsto (fun n : ℕ => (1 - t n) • y + t n • x₀) atTop (𝓝 y) := by
      have h1 : Tendsto t atTop (𝓝 0) := htendsto0
      have h2 : Tendsto (fun n : ℕ => 1 - t n) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds.sub h1)
      have hA :
          Tendsto (fun n : ℕ => (1 - t n) • y) atTop (𝓝 ((1 : ℝ) • y)) := by
        simpa using
          (h2.smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)))
      have hB :
          Tendsto (fun n : ℕ => t n • x₀) atTop (𝓝 (0 : E)) := by
        have h :=
          (h1.smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => (x₀ : E)) atTop (𝓝 (x₀ : E))))
        simpa [zero_smul] using
          (h :
            Tendsto (fun n : ℕ => (t n : ℝ) • (x₀ : E)) atTop (𝓝 ((0 : ℝ) • (x₀ : E))))
      have hsum :
          Tendsto (fun n : ℕ => (1 - t n) • y + t n • x₀) atTop
            (𝓝 (((1 : ℝ) • y) + (0 : E))) := by
        simpa using hA.add hB
      simpa [one_smul, zero_smul, add_zero] using hsum
    -- Strict inequality on interior points, then pass to the limit
    have h_ev_lt : ∀ᶠ n in atTop, g ((1 - t n) • y + t n • x₀) < g z := by
      refine Filter.Eventually.of_forall (fun n => ?_)
      have hsep := hlt₀ _ (hp_mem n)
      simpa [g] using (neg_lt_neg_iff.mpr hsep)
    have h_ev_le : ∀ᶠ n in atTop, g ((1 - t n) • y + t n • x₀) ≤ g z :=
      h_ev_lt.mono (fun _ hn => le_of_lt hn)
    have hg_tendsto : Tendsto (fun n => g ((1 - t n) • y + t n • x₀)) atTop (𝓝 (g y)) :=
      (g.continuous.tendsto _).comp h_tendsto_y
    exact le_of_tendsto_of_tendsto hg_tendsto tendsto_const_nhds h_ev_le
  -- Turn into inner-product inequality via Riesz
  refine ⟨v, hv_ne, ?_⟩
  intro y hy
  have hv_eq : (InnerProductSpace.toDual ℝ E) v = g := by
    simp [v]
  have hv_repr : ∀ x, g x = ⟪x, v⟫ := by
    intro x
    have hx : g x = ((InnerProductSpace.toDual ℝ E) v) x := by
      simpa using congrArg (fun f : E →L[ℝ] ℝ => f x) hv_eq.symm
    simpa [InnerProductSpace.toDual_apply, real_inner_comm] using hx
  -- g (y - z) ≤ 0, hence ⟪y - z, v⟫ ≤ 0
  have : g (y - z) ≤ 0 := by
    have : g y ≤ g z := h_le_all y hy
    simpa [map_sub] using sub_nonpos.mpr this
  simpa [hv_repr] using this

/-- Classical supporting hyperplane theorem in finite-dimensional real inner product spaces. -/
theorem exists_supporting_hyperplane_of_closed_convex_finiteDimensional
  [FiniteDimensional ℝ E]
  {s : Set E} (hs_conv : Convex ℝ s) (hs_closed : IsClosed s)
  {z : E} (hz_mem : z ∈ s) (hz_not_int : z ∉ interior s) :
  ∃ v : E, v ≠ 0 ∧ ∀ y ∈ s, ⟪y - z, v⟫ ≤ 0 := by
  classical
  by_cases hInt : (interior s).Nonempty
  · -- Reduce to the nonempty interior case
    exact exists_supporting_hyperplane_of_closed_convex_of_nonempty_interior
      hs_conv hs_closed hz_mem hz_not_int hInt
  · -- interior s = ∅: s is contained in an affine hyperplane; its normal supports with equality
    have hs_nonempty : s.Nonempty := ⟨z, hz_mem⟩
    have hIntEmpty : interior s = (∅ : Set E) := by
      classical
      by_contra hne; have : (interior s).Nonempty := by simpa [Set.nonempty_iff_ne_empty] using hne
      exact hInt this
    -- From previous API: s ⊆ H where H is a closed affine hyperplane (codim 1)
    obtain ⟨H, _Hclosed, hcodim1, hs_sub_H⟩ :=
      exists_affine_hyperplane_of_nonempty_of_interior_empty
        (E := E) (s := s) hs_conv hs_nonempty hs_closed hIntEmpty
    -- Build a nonzero linear functional g annihilating H.direction
    set U : Subspace ℝ E := H.direction
    set Q := E ⧸ U
    have hpos : 0 < finrank ℝ Q := by simpa [Q] using (by simp [hcodim1])
    let b : Basis (Fin (finrank ℝ Q)) ℝ Q := Module.finBasis ℝ Q
    let gQ : Module.Dual ℝ Q := b.coord ⟨0, hpos⟩
    let g : E →ₗ[ℝ] ℝ := gQ.comp U.mkQ
    -- g ≠ 0
    have hg_ne : g ≠ 0 := by
      classical
      obtain ⟨v0, hv0⟩ := Submodule.mkQ_surjective U (b ⟨0, hpos⟩)
      have hgv : g v0 = gQ (b ⟨0, hpos⟩) := by
        simpa [g, LinearMap.comp_apply] using congrArg (fun w => gQ w) hv0
      have hgv1 : g v0 = 1 := by simpa [gQ] using hgv
      intro hg
      simp [hg] at hgv1
    -- Turn g into a vector v via Riesz
    let gCLM : E →L[ℝ] ℝ := ⟨g, LinearMap.continuous_of_finiteDimensional g⟩
    let v : E := (InnerProductSpace.toDual ℝ E).symm gCLM
    have hv_ne : v ≠ 0 := by
      intro hv
      -- identify (toDual v) with the CLM built from g
      have h_toDual_eq :
          (InnerProductSpace.toDual ℝ E) v = gCLM := by
        have h :=
          (LinearIsometryEquiv.apply_symm_apply (InnerProductSpace.toDual ℝ E) gCLM)
        simp only [LinearIsometryEquiv.apply_symm_apply] at h
        exact LinearIsometryEquiv.apply_symm_apply (toDual ℝ E) gCLM
      -- from v = 0 deduce (toDual v) = 0, hence g = 0
      have h_zero : (InnerProductSpace.toDual ℝ E) v = 0 :=
        (InnerProductSpace.toDual ℝ E).map_eq_zero_iff.mpr hv
      have hCLM_zero : gCLM = 0 := by
        have h' := h_zero
        simp [h_toDual_eq] at h'
        exact h'
      have : g = 0 := by
        -- extract the linear map from the equality of CLMs
        simpa using congrArg ContinuousLinearMap.toLinearMap hCLM_zero
      exact hg_ne this
    -- For y,z ∈ s ⊆ H, we have y - z ∈ U, hence g(y - z) = 0, i.e., ⟪y - z, v⟫ = 0
    refine ⟨v, hv_ne, ?_⟩
    intro y hy
    have hyH : y ∈ (H : Set E) := hs_sub_H hy
    have hzH : z ∈ (H : Set E) := hs_sub_H hz_mem
    have hU_y : y -ᵥ z ∈ U := H.vsub_mem_direction hyH hzH
    have : g (y - z) = 0 := by
      -- y - z = vsub, and g kills U since U ≤ ker g
      have hmem : y - z ∈ U := by simpa [vsub_eq_sub] using hU_y
      -- First, note U ≤ ker g
      have hU_le_ker : U ≤ LinearMap.ker g := by
        intro u hu
        have hmk : U.mkQ u = 0 := by
          simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hu
        -- show g u = 0 by reducing via the quotient and using gQ 0 = 0
        refine LinearMap.mem_ker.mpr ?_
        have : gQ ((Submodule.mkQ U) u) = 0 := by
          simp [hmk]
        simpa [g, LinearMap.comp_apply] using this
      -- hence g (y - z) = 0
      simpa [LinearMap.mem_ker] using (hU_le_ker hmem)
    -- identify g with ⟪·, v⟫ via Riesz
    have hv_repr : ∀ x, g x = ⟪x, v⟫ := by
      intro x
      have h_toDual_eq :
          (InnerProductSpace.toDual ℝ E) v = gCLM := by
        have h :=
          (LinearIsometryEquiv.apply_symm_apply (InnerProductSpace.toDual ℝ E) gCLM)
        simp only [LinearIsometryEquiv.apply_symm_apply] at h
        exact LinearIsometryEquiv.apply_symm_apply (toDual ℝ E) gCLM
      have hx : ((InnerProductSpace.toDual ℝ E) v) x = g x := by
        have h := h_toDual_eq
        have : ((InnerProductSpace.toDual ℝ E) v) x = gCLM x := by simp [h]
        simpa [gCLM]
      simpa [InnerProductSpace.toDual_apply, real_inner_comm] using hx.symm
    have : ⟪y - z, v⟫ = 0 := by simpa [hv_repr, map_sub] using this
    exact this.le

/-- Functional form: supporting functional in the nonempty interior case. -/
lemma exists_supporting_hyperplane_closed_convex_of_nonempty_interior
    {s : Set E} (hs_conv : Convex ℝ s) (hs_closed : IsClosed s)
    {z : E} (hz_in_s : z ∈ s) (hz_not_int : z ∉ interior s)
    (hInt : (interior s).Nonempty) :
    ∃ g : E →L[ℝ] ℝ, g ≠ 0 ∧ ∀ y ∈ s, g y ≤ g z := by
  obtain ⟨v, hv_ne, hv⟩ :=
    exists_supporting_hyperplane_of_closed_convex_of_nonempty_interior
      hs_conv hs_closed hz_in_s hz_not_int hInt
  let g : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) v
  have hg_ne : g ≠ 0 := by
    intro h; exact hv_ne ((InnerProductSpace.toDual ℝ E).map_eq_zero_iff.1 h)
  refine ⟨g, hg_ne, ?_⟩
  intro y hy
  -- From ⟪y - z, v⟫ ≤ 0, deduce g y - g z ≤ 0, hence g y ≤ g z.
  have gyz_sub : g y - g z ≤ 0 := by
    have hv' : ⟪v, y - z⟫ ≤ 0 := by
      simpa [real_inner_comm] using (hv y hy)
    have hyz_inner_sub : ⟪v, y⟫ - ⟪v, z⟫ ≤ 0 := by
      simpa [inner_sub_right] using hv'
    simpa [g, InnerProductSpace.toDual_apply] using hyz_inner_sub
  exact sub_nonpos.mp gyz_sub

/-- Functional form: finite-dimensional classical supporting hyperplane theorem. -/
lemma exists_supporting_hyperplane_closed_convex_finiteDimensional
    [FiniteDimensional ℝ E]
    {s : Set E} (hs_conv : Convex ℝ s) (hs_closed : IsClosed s)
    {z : E} (hz_in_s : z ∈ s) (hz_not_int : z ∉ interior s) :
    ∃ g : E →L[ℝ] ℝ, g ≠ 0 ∧ ∀ y ∈ s, g y ≤ g z := by
  obtain ⟨v, hv_ne, hv⟩ :=
    exists_supporting_hyperplane_of_closed_convex_finiteDimensional
      hs_conv hs_closed hz_in_s hz_not_int
  let g : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) v
  have hg_ne : g ≠ 0 := by
    intro h; exact hv_ne ((InnerProductSpace.toDual ℝ E).map_eq_zero_iff.1 h)
  refine ⟨g, hg_ne, ?_⟩
  intro y hy
  have h' := hv y hy
  -- From ⟪y - z, v⟫ ≤ 0, deduce g (y - z) ≤ 0, hence g y ≤ g z
  have gyz' : g (y - z) ≤ 0 := by
    have : g (y - z) = ⟪v, y - z⟫ := by
      simp [g, InnerProductSpace.toDual_apply]
    rw [this]
    simpa [real_inner_comm] using h'
  have gyz_sub : g y - g z ≤ 0 := by
    simpa [map_sub] using gyz'
  exact sub_nonpos.mp gyz_sub

lemma exists_support_hyperplane_of_mem_frontier
    [FiniteDimensional ℝ E]
    {s : Set E} (hs_conv : Convex ℝ s) (hs_closed : IsClosed s)
    {z : E} (hz_frontier : z ∈ frontier s) :
    ∃ g : E →L[ℝ] ℝ, g ≠ 0 ∧ ∀ y ∈ s, g y ≤ g z := by
  have hz_in_s : z ∈ s := hs_closed.closure_eq ▸ frontier_subset_closure hz_frontier
  have hz_not_int : z ∉ interior s := not_mem_interior_of_mem_frontier hz_frontier
  exact exists_supporting_hyperplane_closed_convex_finiteDimensional
    hs_conv hs_closed hz_in_s hz_not_int
