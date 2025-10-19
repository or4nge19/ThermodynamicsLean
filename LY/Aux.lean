import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.TangentCone
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Data.Real.StarOrdered
import LY.ForMathlib.TangentCone

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter Topology

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Riesz representation: Every linear functional is given by inner product. -/
lemma inner_dual_representation [FiniteDimensional ℝ E] (φ : E →L[ℝ] ℝ) :
    ∃ v : E, ∀ x, φ x = ⟪x, v⟫_ℝ := by
  refine ⟨(InnerProductSpace.toDual ℝ E).symm φ, ?_⟩
  intro x
  have hx : ⟪(InnerProductSpace.toDual ℝ E).symm φ, x⟫_ℝ = φ x := by simp
  rw [real_inner_comm] at hx; exact hx.symm
-- [Mathlib.Analysis.InnerProductSpace.Dual]

/-- If two nonzero vectors define the same closed half-space, they are positive scalar multiples. -/
lemma normals_pos_scalar_of_equal_halfspaces [FiniteDimensional ℝ E] {v w : E}
    (hv : v ≠ 0) --(hw : w ≠ 0)
    (hEq : {z : E | 0 ≤ ⟪z, v⟫_ℝ} = {z : E | 0 ≤ ⟪z, w⟫_ℝ}) :
    ∃ c : ℝ, 0 < c ∧ w = c • v := by
  have ker_eq : {z : E | ⟪z, v⟫_ℝ = 0} = {z : E | ⟪z, w⟫_ℝ = 0} := by
    ext z
    constructor <;> intro hz
    · have hz0 : ⟪z, v⟫_ℝ = 0 := hz
      have hz_in_v : 0 ≤ ⟪z, v⟫_ℝ := by
        simp [hz0]
      have hnegz_in_v : 0 ≤ ⟪-z, v⟫_ℝ := by
        simp [inner_neg_left, hz0]
      have hz_in_w : 0 ≤ ⟪z, w⟫_ℝ := by
        have : z ∈ {z : E | 0 ≤ ⟪z, v⟫_ℝ} := hz_in_v
        have : z ∈ {z : E | 0 ≤ ⟪z, w⟫_ℝ} := by simpa [hEq] using this
        exact this
      have hnegz_in_w : 0 ≤ ⟪-z, w⟫_ℝ := by
        have : -z ∈ {z : E | 0 ≤ ⟪z, v⟫_ℝ} := hnegz_in_v
        have : -z ∈ {z : E | 0 ≤ ⟪z, w⟫_ℝ} := by simpa [hEq] using this
        exact this
      have h1 : ⟪z, w⟫_ℝ ≤ 0 := by simpa [inner_neg_left] using hnegz_in_w
      have h2 : 0 ≤ ⟪z, w⟫_ℝ := hz_in_w
      have hz0' : ⟪z, w⟫_ℝ = 0 := le_antisymm h1 h2
      simp [hz0']
    · have hz0 : ⟪z, w⟫_ℝ = 0 := hz
      have hz_in_w : 0 ≤ ⟪z, w⟫_ℝ := by
        simp [hz0]
      have hnegz_in_w : 0 ≤ ⟪-z, w⟫_ℝ := by
        simp [inner_neg_left, hz0]
      have hz_in_v : 0 ≤ ⟪z, v⟫_ℝ := by
        have : z ∈ {z : E | 0 ≤ ⟪z, w⟫_ℝ} := hz_in_w
        have : z ∈ {z : E | 0 ≤ ⟪z, v⟫_ℝ} := by simpa [hEq] using this
        exact this
      have hnegz_in_v : 0 ≤ ⟪-z, v⟫_ℝ := by
        have : -z ∈ {z : E | 0 ≤ ⟪z, w⟫_ℝ} := hnegz_in_w
        have : -z ∈ {z : E | 0 ≤ ⟪z, v⟫_ℝ} := by simpa [hEq] using this
        exact this
      have h1 : ⟪z, v⟫_ℝ ≤ 0 := by simpa [inner_neg_left] using hnegz_in_v
      have h2 : 0 ≤ ⟪z, v⟫_ℝ := hz_in_v
      have hz0' : ⟪z, v⟫_ℝ = 0 := le_antisymm h1 h2
      simp [hz0']
  set c := ⟪v, w⟫_ℝ / ⟪v, v⟫_ℝ
  have linear_relation : ∀ z, ⟪z, w⟫_ℝ = c * ⟪z, v⟫_ℝ := by
    intro z
    set a := ⟪z, v⟫_ℝ / ⟪v, v⟫_ℝ
    set z_perp := z - a • v
    have hvv_ne : ⟪v, v⟫_ℝ ≠ 0 := inner_self_ne_zero.2 hv
    have hz_perp_v : ⟪z_perp, v⟫_ℝ = 0 := by
      calc
        ⟪z_perp, v⟫_ℝ
            = ⟪z, v⟫_ℝ - a * ⟪v, v⟫_ℝ := by
                simp [z_perp, inner_sub_left, inner_smul_left]
        _ = ⟪z, v⟫_ℝ - (⟪z, v⟫_ℝ / ⟪v, v⟫_ℝ) * ⟪v, v⟫_ℝ := rfl
        _ = ⟪z, v⟫_ℝ - ⟪z, v⟫_ℝ := by
              have : (⟪z, v⟫_ℝ / ⟪v, v⟫_ℝ) * ⟪v, v⟫_ℝ = ⟪z, v⟫_ℝ := by
                simp [div_eq_mul_inv, hvv_ne]
              simp [this]
        _ = 0 := by simp
    have hz_perp_w : ⟪z_perp, w⟫_ℝ = 0 := by
      have : z_perp ∈ {z : E | ⟪z, v⟫_ℝ = 0} := by simp [hz_perp_v]
      have : z_perp ∈ {z : E | ⟪z, w⟫_ℝ = 0} := by simpa [ker_eq] using this
      simpa using this
    calc
      ⟪z, w⟫_ℝ
          = ⟪a • v + z_perp, w⟫_ℝ := by
              have hsum : a • v + z_perp = z := by
                simp [z_perp, add_left_comm, sub_eq_add_neg]
              simp [hsum]
      _ = a * ⟪v, w⟫_ℝ := by
            simp [inner_add_left, inner_smul_left, hz_perp_w]
      _ = (⟪z, v⟫_ℝ / ⟪v, v⟫_ℝ) * ⟪v, w⟫_ℝ := rfl
      _ = (⟪z, v⟫_ℝ * ⟪v, w⟫_ℝ) / ⟪v, v⟫_ℝ := by
            rw [div_mul_eq_mul_div]
      _ = (⟪v, w⟫_ℝ * ⟪z, v⟫_ℝ) / ⟪v, v⟫_ℝ := by
            ac_rfl
      _ = (⟪v, w⟫_ℝ / ⟪v, v⟫_ℝ) * ⟪z, v⟫_ℝ := by
            rw [← div_mul_eq_mul_div]
      _ = c * ⟪z, v⟫_ℝ := rfl
  have hc_pos : 0 < c := by
    have hv_in_v : v ∈ {z : E | 0 ≤ ⟪z, v⟫_ℝ} := by
      have hsq : 0 ≤ ‖v‖ ^ 2 := by positivity
      simp [real_inner_self_eq_norm_sq]
    have hv_in_w : v ∈ {z : E | 0 ≤ ⟪z, w⟫_ℝ} := by simpa [hEq] using hv_in_v
    have hvw_nonneg : 0 ≤ ⟪v, w⟫_ℝ := hv_in_w
    have hvv_pos : 0 < ⟪v, v⟫_ℝ := by
      have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hsq : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hnv
      simpa [real_inner_self_eq_norm_sq] using hsq
    have hneg_v_notin_v : -v ∉ {z : E | 0 ≤ ⟪z, v⟫_ℝ} := by
      have : ⟪-v, v⟫_ℝ < 0 := by
        simpa [inner_neg_left] using hvv_pos
      exact (not_le.mpr this)
    have hneg_v_notin_w : -v ∉ {z : E | 0 ≤ ⟪z, w⟫_ℝ} := by
      simpa [hEq] using hneg_v_notin_v
    have : ⟪-v, w⟫_ℝ < 0 := lt_of_not_ge hneg_v_notin_w
    have hvw_pos : 0 < ⟪v, w⟫_ℝ := by
      have : -⟪v, w⟫_ℝ < 0 := by simpa [inner_neg_left] using this
      linarith
    exact div_pos hvw_pos hvv_pos
  have : w = c • v := by
    have h_perp : ∀ z, ⟪z, w - c • v⟫_ℝ = 0 := by
      intro z
      have h := linear_relation z
      have : ⟪z, w⟫_ℝ - c * ⟪z, v⟫_ℝ = 0 := sub_eq_zero.mpr h
      simpa [inner_sub_right, inner_smul_right] using this
    have : ⟪w - c • v, w - c • v⟫_ℝ = 0 := h_perp _
    have : ‖w - c • v‖ = 0 := by
      simpa [real_inner_self_eq_norm_sq, sq_eq_zero_iff] using this
    have : w - c • v = 0 := by simpa [norm_eq_zero] using this
    exact (sub_eq_zero.mp this)
  exact ⟨c, hc_pos, this⟩
-- [LY.ForMathlib.TangentCone, Mathlib.Analysis.InnerProductSpace.Orthonormal]

/-- Version for shifted half-spaces. -/
lemma normals_pos_scalar_of_equal_halfspaces_shifted [FiniteDimensional ℝ E]
    {x v w : E} (hv : v ≠ 0) --(hw : w ≠ 0)
    (hEq : {y : E | 0 ≤ ⟪y - x, v⟫_ℝ} = {y : E | 0 ≤ ⟪y - x, w⟫_ℝ}) :
    ∃ c : ℝ, 0 < c ∧ w = c • v := by
  have : {z : E | 0 ≤ ⟪z, v⟫_ℝ} = {z : E | 0 ≤ ⟪z, w⟫_ℝ} := by
    ext z
    constructor <;> intro hz
    · have hz' : z + x ∈ {y : E | 0 ≤ ⟪y - x, v⟫_ℝ} := by
        simpa using hz
      have hz'' : z + x ∈ {y : E | 0 ≤ ⟪y - x, w⟫_ℝ} := by simpa [hEq] using hz'
      simpa using hz''
    · have hz' : z + x ∈ {y : E | 0 ≤ ⟪y - x, w⟫_ℝ} := by
        simpa using hz
      have hz'' : z + x ∈ {y : E | 0 ≤ ⟪y - x, v⟫_ℝ} := by simpa [hEq] using hz'
      simpa using hz''
  exact normals_pos_scalar_of_equal_halfspaces hv this
-- [LY.ForMathlib.TangentCone, Mathlib.Analysis.InnerProductSpace.Orthonormal]

/-- A small rewrite helper for translating from unshifted to shifted half-spaces. -/
private lemma inner_sub_add_left_cancel (x z v : E) :
    ⟪(z + x) - x, v⟫_ℝ = ⟪z, v⟫_ℝ := by simp [add_comm]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- If `v` is a supporting normal at `x` for `s`, then `v` lies in the inner dual of the
positive cone generated by the differences `y - x` with `y ∈ s`. -/
lemma support_normal_mem_innerDual_posCone
    {s : Set E} {x v : E}
    (hv_support : ∀ y ∈ s, 0 ≤ ⟪y - x, v⟫_ℝ) :
    v ∈ ProperCone.innerDual
      {d : E | ∃ y ∈ s, ∃ t : ℝ, 0 ≤ t ∧ d = t • (y - x)} := by
  change ∀ ⦃d : E⦄,
      d ∈ {d : E | ∃ y ∈ s, ∃ t : ℝ, 0 ≤ t ∧ d = t • (y - x)} → 0 ≤ ⟪d, v⟫_ℝ
  intro d hd
  rcases hd with ⟨y, hy, t, ht, rfl⟩
  have hy' : 0 ≤ ⟪y - x, v⟫_ℝ := hv_support y hy
  simpa [real_inner_smul_left, mul_comm] using mul_nonneg ht hy'
-- [Mathlib.Analysis.Convex.Cone.InnerDual]
end InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
/-- The (Bouligand) normal cone at `x` to `s` as an inner dual of the tangent cone. -/
def normalConeAt (s : Set E) (x : E) : ProperCone ℝ E :=
  ProperCone.innerDual (tangentConeAt ℝ s x)
-/

/-- The (Bouligand) normal cone at `x` to `s` as an inner dual of the positive tangent cone. -/
def normalConeAt (s : Set E) (x : E) : ProperCone ℝ E :=
  ProperCone.innerDual (posTangentConeAt s x)

/-- The positive ray generated by `u`. -/
def isPositiveRay (u : E) : Set E := { y : E | ∃ c : ℝ, 0 ≤ c ∧ y = c • u }

omit [CompleteSpace E] in
/-- The positive tangent cone is a subset of the Bouligand tangent cone. -/
lemma posTangentConeAt_subset_tangentConeAt (s : Set E) (x : E) :
    posTangentConeAt s x ⊆ tangentConeAt ℝ s x := by
  intro y hy
  rcases hy with ⟨c, d, hd_event, hc_lim, hcd_lim⟩
  refine ⟨c, d, hd_event, ?_, hcd_lim⟩
  exact tendsto_abs_atTop_atTop.comp hc_lim

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A supporting normal (w.r.t. the shifted half-space at `x`) lies in the normal cone. -/
theorem support_normal_mem_normalConeAt
    {s : Set E} {x v : E}
    (hv_support : ∀ y ∈ s, 0 ≤ ⟪y - x, v⟫_ℝ) :
    v ∈ (normalConeAt s x : Set E) := by
  -- normalConeAt is the inner dual of posTangentConeAt
  change ∀ ⦃d : E⦄, d ∈ posTangentConeAt s x → 0 ≤ ⟪d, v⟫_ℝ
  intro d hd
  -- Extract witnesses
  rcases hd with ⟨c, d', hd', hc, hcd⟩
  -- eventually ⟪d' n, v⟫ ≥ 0 from support inequality
  have h_inner_nonneg : ∀ᶠ n in Filter.atTop, 0 ≤ ⟪d' n, v⟫_ℝ := by
    have : ∀ᶠ n in Filter.atTop, x + d' n ∈ s := hd'
    refine this.mono (fun n hn => ?_)
    simpa [add_comm, add_left_comm, add_assoc, add_sub_cancel] using hv_support (x + d' n) hn
  -- continuity: ⟪(c n) • d' n, v⟫ → ⟪d, v⟫
  have h_tend : Tendsto (fun n => ⟪(c n) • d' n, v⟫_ℝ) atTop (𝓝 ⟪d, v⟫_ℝ) := by
    have hcont : Continuous fun z : E => ⟪z, v⟫_ℝ := (continuous_id.inner continuous_const)
    exact (hcont.tendsto d).comp hcd
  -- since c : ℕ → ℝ with c → +∞, we have eventually 0 ≤ c n
  have hc_nonneg : ∀ᶠ n in Filter.atTop, 0 ≤ c n :=
    hc.eventually (Filter.eventually_ge_atTop 0)
  -- Combine to get eventually 0 ≤ ⟪(c n) • d' n, v⟫
  have h_smul_nonneg : ∀ᶠ n in Filter.atTop, 0 ≤ ⟪(c n : ℝ) • d' n, v⟫_ℝ := by
    filter_upwards [hc_nonneg, h_inner_nonneg] with n hcn hdn
    have : 0 ≤ (c n : ℝ) * ⟪d' n, v⟫_ℝ := mul_nonneg hcn hdn
    simpa [real_inner_smul_left] using this
  -- Pass to the limit: 0 ≤ ⟪d, v⟫
  exact ge_of_tendsto h_tend h_smul_nonneg

theorem innerDual_halfspace_eq_ray {u : E} (hu : u ≠ 0) :
    (ProperCone.innerDual {d : E | 0 ≤ ⟪d, u⟫_ℝ} : Set E) = isPositiveRay u := by
  classical
  ext v; constructor
  · intro hv_in_dual
    -- decompose v into the component along u and the orthogonal component
    set c : ℝ := ⟪v, u⟫_ℝ / ⟪u, u⟫_ℝ
    set v_perp : E := v - c • u
    have h_uu_pos : 0 < ⟪u, u⟫_ℝ := by
      have : 0 < ‖u‖ := norm_pos_iff.mpr hu
      simpa [real_inner_self_eq_norm_sq] using sq_pos_of_pos this
    have h_perp : ⟪v_perp, u⟫_ℝ = 0 := by
      -- (⟪v,u⟫ / ⟪u,u⟫) * ⟪u,u⟫ = ⟪v,u⟫
      have hcu : c * ⟪u, u⟫_ℝ = ⟪v, u⟫_ℝ := by
        have hne : ⟪u, u⟫_ℝ ≠ 0 := ne_of_gt h_uu_pos
        unfold c
        calc
          (⟪v, u⟫_ℝ / ⟪u, u⟫_ℝ) * ⟪u, u⟫_ℝ
              = (⟪v, u⟫_ℝ * ⟪u, u⟫_ℝ) / ⟪u, u⟫_ℝ := by
                  rw [div_mul_eq_mul_div]
              _ = ⟪v, u⟫_ℝ := by
                  simp [hne]
      -- ⟪v - c•u, u⟫ = ⟪v,u⟫ - c*⟪u,u⟫ = 0
      simp [v_perp, inner_sub_left, inner_smul_left, hcu]
    -- u lies in the defining halfspace
    have hu_in_halfspace : u ∈ {d : E | 0 ≤ ⟪d, u⟫_ℝ} := by
      simp [real_inner_self_nonneg]
    -- c ≥ 0 from hv_in_dual applied to u
    have h_c_nonneg : 0 ≤ c := by
      have h_uv_nonneg : 0 ≤ ⟪u, v⟫_ℝ := hv_in_dual hu_in_halfspace
      have hnum : 0 ≤ ⟪v, u⟫_ℝ := by simpa [real_inner_comm] using h_uv_nonneg
      exact div_nonneg hnum (le_of_lt h_uu_pos)
    -- test with the vector -v_perp (which is orthogonal to u)
    have h_test_in_halfspace : -v_perp ∈ {d : E | 0 ≤ ⟪d, u⟫_ℝ} := by
      -- ⟪-v_perp, u⟫ = 0
      simp [inner_neg_left, h_perp]
    have h_v_perp_v_nonneg : 0 ≤ ⟪-v_perp, v⟫_ℝ := hv_in_dual h_test_in_halfspace
    -- compute ⟪-v_perp, v⟫ = -‖v_perp‖^2 using v = c•u + v_perp and orthogonality
    have h_inner_computation : ⟪-v_perp, v⟫_ℝ = -‖v_perp‖ ^ 2 := by
      have hv_decomp : v = c • u + v_perp := by
        simp [v_perp, add_left_comm, sub_eq_add_neg]
      simp [hv_decomp, inner_add_right, inner_smul_right, h_perp, real_inner_self_eq_norm_sq]
    -- conclude v_perp = 0
    have h_v_perp_zero : v_perp = 0 := by
      have hle : ‖v_perp‖ ^ 2 ≤ 0 := by
        have : 0 ≤ -‖v_perp‖ ^ 2 := by simpa [h_inner_computation] using h_v_perp_v_nonneg
        linarith
      have hge : 0 ≤ ‖v_perp‖ ^ 2 := by positivity
      have hsq0 : ‖v_perp‖ ^ 2 = 0 := le_antisymm hle hge
      have : ‖v_perp‖ = 0 := by simpa [sq_eq_zero_iff] using hsq0
      simpa [norm_eq_zero] using this
    -- hence v is on the positive ray generated by u
    refine ⟨c, h_c_nonneg, ?_⟩
    calc v = v_perp + c • u := by simp [v_perp]
        _ = 0 + c • u := by rw [h_v_perp_zero]
        _ = c • u := by simp
  · rintro ⟨c, hc_nonneg, rfl⟩
    intro d hd_in_halfspace
    have : 0 ≤ c * ⟪d, u⟫_ℝ := mul_nonneg hc_nonneg hd_in_halfspace
    simpa [real_inner_smul_right] using this

end InnerProduct
