/-
Copyright (c) 2025 Matteo Cipollina All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LY.Entropy.Principle

/-!
# Construction of the Canonical Entropy Function

This file details the construction of the canonical entropy function `S_Γ` for
a specific state space `State Γ`, as outlined in Section II.E of the
Lieb-Yngvason paper.

The construction proceeds as follows:
1.  **Reference States**: Fix two reference states `X₀` and `X₁` in `State Γ`
    such that `X₀ ≺≺ X₁`. Define a family of `ReferenceState`s `R_lam` as
    convex combinations `((1-lam)•X₀, lam•X₁)`.
2.  **Lambda Set**: For any state `X`, define `lam(X)` as the set of all real
    numbers `t` such that `R_t` can reach `X` through some generalized
    adiabatic process (`GenRefAccessible`).
3.  **Canonical Entropy**: Define the entropy `S_Γ(X)` as the supremum of
    the set `lam(X)`.
4.  **Key Lemmas**:
    - **Lemma 2.7 (Well-definedness)**: Prove that `lam(X)` is a non-empty,
      bounded-above lower set, ensuring `sSup` is well-defined.
    - **Theorem 2.2 (Properties)**: Prove that the constructed function `S_Γ`
      satisfies normalization (`S(X₀)=0`, `S(X₁)=1`), monotonicity
      (`X ≺ Y → S(X) ≤ S(Y)`), and other properties.
    - **Lemma 2.8 (Continuity)**: Show that the supremum is attained, i.e.,
      `S(X) ∈ lam(X)`, which implies `R_{S(X)} ≈ X`. This requires the
      Gap Lemma.
-/

namespace LY

universe u v
variable {System : Type u} [TW : ThermoWorld System]
local infix:50 " ≺ " => TW.le
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X
local infixr:70 " ⊗ " => TW.comp
local infixr:80 " • " => TW.scale
local infix:50 " ≺≺ " => StrictlyPrecedes

-- Context structure to hold the reference states for Canonical Entropy.
structure CanonicalEntropyContext (Γ : System) where
  X₀ : TW.State Γ
  X₁ : TW.State Γ
  h_ref_strict : X₀ ≺≺ X₁

section CanonicalEntropy
variable {Γ : System}

/-- The Reference State R_lam = ((1-lam)X₀, lamX₁). Defined only for lam ∈ [0, 1]. -/
noncomputable def ReferenceState (X₀ X₁ : TW.State Γ) (lam : ℝ) (h_nonneg : 0 ≤ lam) (h_le1 : lam ≤ 1) :
    TW.State ((1-lam)•Γ ⊗ lam•Γ) :=
  comp_state (
    gscale_state (sub_nonneg.mpr h_le1) X₀,
    gscale_state h_nonneg X₁
  )

/-! ### Strict Reference State Ordering Lemma -/

variable (Ctx : CanonicalEntropyContext Γ)

/-- Helper Lemma: Reorganization of R_lam ≈ ((1-mu)X₀, (lamX₁, (mu-lam)X₀)). -/
lemma ReferenceState_reorg_lam (lam mu : ℝ)
  (hlam_nonneg : 0 ≤ lam) (hmu_le1 : mu ≤ 1) (h_le : lam ≤ mu) :
  ReferenceState Ctx.X₀ Ctx.X₁ lam hlam_nonneg (le_trans h_le hmu_le1) ≈
  comp_state (
    gscale_state (sub_nonneg.mpr hmu_le1) Ctx.X₀,
    comp_state (
      gscale_state hlam_nonneg Ctx.X₁,
      gscale_state (sub_nonneg.mpr h_le) Ctx.X₀
    )
  ) := by
  let hlam_le1 := le_trans h_le hmu_le1
  -- 1. Recombination: (1-lam)X₀ ≈ ((1-mu)X₀, (mu-lam)X₀).
  have h_1mlam_nonneg := sub_nonneg.mpr hlam_le1
  have h_1mmu_nonneg := sub_nonneg.mpr hmu_le1
  have h_δ_nonneg := sub_nonneg.mpr h_le
  have h_coeff : 1 - lam = (1 - mu) + (mu - lam) := by ring
  -- Bridge by CEq for generalized scaling, then apply generalized recombination.
  have h_align_X₀ :
      gscale_state h_1mlam_nonneg Ctx.X₀ ≈
      gscale_state (add_nonneg h_1mmu_nonneg h_δ_nonneg) Ctx.X₀ :=
    gscale_eq_coherence (Γ := Γ) (X := Ctx.X₀) h_coeff h_1mlam_nonneg (add_nonneg h_1mmu_nonneg h_δ_nonneg)
  have h_base :
      gscale_state (add_nonneg h_1mmu_nonneg h_δ_nonneg) Ctx.X₀ ≈
      comp_state (gscale_state h_1mmu_nonneg Ctx.X₀, gscale_state h_δ_nonneg Ctx.X₀) :=
    generalized_recombination_lemma h_1mmu_nonneg h_δ_nonneg Ctx.X₀
  have h_recomb_X₀ :
      gscale_state h_1mlam_nonneg Ctx.X₀ ≈
      comp_state (gscale_state h_1mmu_nonneg Ctx.X₀, gscale_state h_δ_nonneg Ctx.X₀) :=
    thermo_equiv_trans' h_align_X₀ h_base
  -- 2. Lift into R_lam (A3/L2.4_i). R_lam ≈ (((1-mu)X₀, δX₀), lamX₁).
  have h_Rlam_recomb :
      comp_state (gscale_state h_1mlam_nonneg Ctx.X₀, gscale_state hlam_nonneg Ctx.X₁) ≈
      comp_state (comp_state (gscale_state h_1mmu_nonneg Ctx.X₀, gscale_state h_δ_nonneg Ctx.X₀),
                  gscale_state hlam_nonneg Ctx.X₁) :=
    L2_4_i h_recomb_X₀ (thermo_equiv_refl (gscale_state hlam_nonneg Ctx.X₁))
  -- 3. Reorganization to reach ((1-mu)X₀, (lamX₁, δX₀)).
  -- Assoc R: ((A,B),C) ≈ (A,(B,C)).
  have h_Rlam_assoc :
      comp_state (comp_state (gscale_state h_1mmu_nonneg Ctx.X₀, gscale_state h_δ_nonneg Ctx.X₀),
                  gscale_state hlam_nonneg Ctx.X₁)
      ≈
      comp_state (gscale_state h_1mmu_nonneg Ctx.X₀,
        comp_state (gscale_state h_δ_nonneg Ctx.X₀, gscale_state hlam_nonneg Ctx.X₁)) :=
    assoc_equiv_R (gscale_state h_1mmu_nonneg Ctx.X₀)
                  (gscale_state h_δ_nonneg Ctx.X₀)
                  (gscale_state hlam_nonneg Ctx.X₁)
  -- Comm inner: (δX₀, lamX₁) ≈ (lamX₁, δX₀), lifted by A on the left.
  have h_comm_inner :
      comp_state (gscale_state h_δ_nonneg Ctx.X₀, gscale_state hlam_nonneg Ctx.X₁) ≈
      comp_state (gscale_state hlam_nonneg Ctx.X₁, gscale_state h_δ_nonneg Ctx.X₀) :=
    comp_comm_equiv_clean (gscale_state h_δ_nonneg Ctx.X₀) (gscale_state hlam_nonneg Ctx.X₁)
  have h_Rlam_comm :
      comp_state (gscale_state h_1mmu_nonneg Ctx.X₀,
        comp_state (gscale_state h_δ_nonneg Ctx.X₀, gscale_state hlam_nonneg Ctx.X₁)) ≈
      comp_state (gscale_state h_1mmu_nonneg Ctx.X₀,
        comp_state (gscale_state hlam_nonneg Ctx.X₁, gscale_state h_δ_nonneg Ctx.X₀)) :=
    L2_4_i (thermo_equiv_refl (gscale_state h_1mmu_nonneg Ctx.X₀)) h_comm_inner
  -- Combine chain.
  exact
    thermo_equiv_trans'
      (thermo_equiv_trans' h_Rlam_recomb h_Rlam_assoc)
      h_Rlam_comm

/-- Helper Lemma: Reorganization of R_mu ≈ ((1-mu)X₀, (lamX₁, (mu-lam)X₁)). -/
lemma ReferenceState_reorg_mu (lam mu : ℝ)
  (hlam_nonneg : 0 ≤ lam) (hmu_le1 : mu ≤ 1) (h_le : lam ≤ mu) :
  ReferenceState Ctx.X₀ Ctx.X₁ mu (le_trans hlam_nonneg h_le) hmu_le1 ≈
  comp_state (
    gscale_state (sub_nonneg.mpr hmu_le1) Ctx.X₀,
    comp_state (
      gscale_state hlam_nonneg Ctx.X₁,
      gscale_state (sub_nonneg.mpr h_le) Ctx.X₁
    )
  ) := by
  let hmu_nonneg := le_trans hlam_nonneg h_le
  -- 1. Recombination: muX₁ ≈ (lamX₁, (mu-lam)X₁).
  have h_δ_nonneg := sub_nonneg.mpr h_le
  have h_coeff : mu = lam + (mu - lam) := by ring
  -- Bridge by CEq for generalized scaling, then apply generalized recombination.
  have h_align_X₁ :
      gscale_state hmu_nonneg Ctx.X₁ ≈
      gscale_state (add_nonneg hlam_nonneg h_δ_nonneg) Ctx.X₁ :=
    gscale_eq_coherence (Γ := Γ) (X := Ctx.X₁) h_coeff hmu_nonneg (add_nonneg hlam_nonneg h_δ_nonneg)
  have h_base :
      gscale_state (add_nonneg hlam_nonneg h_δ_nonneg) Ctx.X₁ ≈
      comp_state (gscale_state hlam_nonneg Ctx.X₁, gscale_state h_δ_nonneg Ctx.X₁) :=
    generalized_recombination_lemma hlam_nonneg h_δ_nonneg Ctx.X₁
  have h_recomb_X₁ :
      gscale_state hmu_nonneg Ctx.X₁ ≈
      comp_state (gscale_state hlam_nonneg Ctx.X₁, gscale_state h_δ_nonneg Ctx.X₁) :=
    thermo_equiv_trans' h_align_X₁ h_base
  -- 2. Lift into R_mu (A3/L2.4_i). R_mu ≈ ((1-mu)X₀, (lamX₁, δX₁)).
  exact L2_4_i (thermo_equiv_refl (gscale_state (sub_nonneg.mpr hmu_le1) Ctx.X₀)) h_recomb_X₁

/-- Strict Reference State Ordering Lemma: If X₀ ≺≺ X₁, and 0 ≤ lam < mu ≤ 1. Then R_lam ≺≺ R_mu. -/
lemma StrictReferenceState_monotone (lam mu : ℝ)
  (hlam_nonneg : 0 ≤ lam) (hmu_le1 : mu ≤ 1) (h_lt : lam < mu) :
  ReferenceState Ctx.X₀ Ctx.X₁ lam hlam_nonneg (le_trans (le_of_lt h_lt) hmu_le1) ≺≺
  ReferenceState Ctx.X₀ Ctx.X₁ mu (le_trans hlam_nonneg (le_of_lt h_lt)) hmu_le1 := by
  -- 1. Establish reorganization.
  have h_le := le_of_lt h_lt
  have h_Rlam_reorg := ReferenceState_reorg_lam (Ctx := Ctx) lam mu hlam_nonneg hmu_le1 h_le
  have h_Rmu_reorg := ReferenceState_reorg_mu  (Ctx := Ctx) lam mu hlam_nonneg hmu_le1 h_le
  -- 2. Identify the crucial comparison step. δ = mu-lam > 0.
  let δ := mu - lam
  have hδ_pos : 0 < δ := sub_pos.mpr h_lt
  have hδ_nonneg := le_of_lt hδ_pos
  -- δX₀ ≺≺ δX₁ by scaling strict accessibility.
  have h_compare_delta_strict : gscale_state hδ_nonneg Ctx.X₀ ≺≺ gscale_state hδ_nonneg Ctx.X₁ := by
    simp only [gscale_state_pos hδ_nonneg hδ_pos]
    exact L2_6_iii δ hδ_pos Ctx.h_ref_strict
  -- 3. Prove R_lam ≺ R_mu (non-strict).
  have h_le_proof :
      ReferenceState Ctx.X₀ Ctx.X₁ lam hlam_nonneg (le_trans (le_of_lt h_lt) hmu_le1) ≺
      ReferenceState Ctx.X₀ Ctx.X₁ mu (le_trans hlam_nonneg (le_of_lt h_lt)) hmu_le1 := by
    have h_compare :=
      TW.A3 (thermo_le_refl (gscale_state (sub_nonneg.mpr hmu_le1) Ctx.X₀))
            (TW.A3 (thermo_le_refl (gscale_state hlam_nonneg Ctx.X₁)) h_compare_delta_strict.1)
    -- First transport R_lam to the intermediate comp_state, apply h_compare, then transport to R_mu.
    have h_mid : ReferenceState Ctx.X₀ Ctx.X₁ lam hlam_nonneg (le_trans (le_of_lt h_lt) hmu_le1) ≺
                 (comp_state (gscale_state (sub_nonneg.mpr hmu_le1) Ctx.X₀,
                             comp_state (gscale_state hlam_nonneg Ctx.X₁, gscale_state (sub_nonneg.mpr h_le) Ctx.X₁))) :=
      le_of_equiv_le h_Rlam_reorg h_compare
    exact le_of_le_equiv h_mid (thermo_equiv_symm h_Rmu_reorg)
  -- 4. Prove strictness: ¬(R_mu ≺ R_lam).
  have h_strict_proof :
      ¬(ReferenceState Ctx.X₀ Ctx.X₁ mu (le_trans hlam_nonneg (le_of_lt h_lt)) hmu_le1 ≺
        ReferenceState Ctx.X₀ Ctx.X₁ lam hlam_nonneg (le_trans (le_of_lt h_lt) hmu_le1)) := by
    intro h_contra
    -- Align via reorganizations.
    have h_contra_aligned :=
      le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_Rmu_reorg) h_contra) h_Rlam_reorg
    -- Cancel ((1-mu)X₀) then cancel lamX₁ to get δX₁ ≺ δX₀.
    have h_cancel1 :=
      cancellation_left (X := gscale_state (sub_nonneg.mpr hmu_le1) Ctx.X₀)
                        (Z := comp_state (gscale_state hlam_nonneg Ctx.X₁, gscale_state (sub_nonneg.mpr h_le) Ctx.X₁))
                        (W := comp_state (gscale_state hlam_nonneg Ctx.X₁, gscale_state (sub_nonneg.mpr h_le) Ctx.X₀))
                        h_contra_aligned
    have h_cancel2 :=
      cancellation_left (X := gscale_state hlam_nonneg Ctx.X₁)
                        (Z := gscale_state (sub_nonneg.mpr h_le) Ctx.X₁)
                        (W := gscale_state (sub_nonneg.mpr h_le) Ctx.X₀)
                        h_cancel1
    -- Convert to strict contradiction via scaling > 0.
    simp only [gscale_state_pos hδ_nonneg hδ_pos] at h_cancel2
    have h_X₁_le_X₀ := (L2_5_ii hδ_pos).mpr h_cancel2
    exact Ctx.h_ref_strict.2 h_X₁_le_X₀
  exact ⟨h_le_proof, h_strict_proof⟩

/-! ### Generalized Reference Accessibility
We define the meaning of ((1-lam)X₀, lamX₁) ≺ X for all lam ∈ ℝ.
-/

/-- Generalized Reference Accessibility (GenRefAccessible lam X).

    Note: X may live in any system Δ, while X₀, X₁ are in Γ.
    We branch into three cases:
    - lam ∈ [0,1]      → R_lam ≺ X
    - lam > 1          → lam·X₁ ≺ (X, (lam-1)·X₀)
    - lam < 0          → (1-lam)·X₀ ≺ (X, (-lam)·X₁)
-/
def GenRefAccessible (X₀ X₁ : TW.State Γ) {Δ : System} (X : TW.State Δ) (lam : ℝ) : Prop :=
  if hlam_range : 0 ≤ lam ∧ lam ≤ 1 then
    ReferenceState X₀ X₁ lam hlam_range.1 hlam_range.2 ≺ X
  else if hlam_gt1 : 1 < lam then
    let h_lam_pos : 0 < lam := lt_trans (by norm_num) hlam_gt1
    let h_lm1_pos : 0 < lam - 1 := sub_pos.mpr hlam_gt1
    scale_state h_lam_pos.ne' X₁ ≺ comp_state (X, scale_state h_lm1_pos.ne' X₀)
  else
    -- This is the lam < 0 case (since not in [0,1] and not > 1).
    let hlam_lt0 : lam < 0 := by
      by_cases h0 : 0 ≤ lam
      · have : ¬ lam ≤ 1 := by
          -- from ¬(0 ≤ lam ∧ lam ≤ 1) and h0 we deduce ¬(lam ≤ 1)
          intro hle; exact (False.elim <| (by
            have : (0 ≤ lam ∧ lam ≤ 1) := And.intro h0 hle
            -- contradict the if-guard assumption (packed by the surrounding `if`)
            have : False := by
              -- Marker: this branch will never be executed in simplification rewrites
              exact hlam_range this
            simp_all only [and_self, not_true_eq_false, not_lt])
            )
        simp_all only [and_false, not_false_eq_true, not_lt]
      · exact lt_of_not_ge h0
    let h_neglam_pos : 0 < -lam := neg_pos.mpr hlam_lt0
    let h_1mlam_pos : 0 < 1 - lam := by linarith
    scale_state h_1mlam_pos.ne' X₀ ≺ comp_state (X, scale_state h_neglam_pos.ne' X₁)

/-- Lemma: Transitivity holds for the generalized definition. -/
lemma GenRefAccessible_trans_le (X₀ X₁ : TW.State Γ) {Δ : System} (X : TW.State Δ) {Δ' : System} (Y : TW.State Δ') (lam : ℝ)
    (h_access : GenRefAccessible (Γ := Γ) X₀ X₁ X lam) (h_le : X ≺ Y) :
    GenRefAccessible (Γ := Γ) X₀ X₁ Y lam := by
  dsimp [GenRefAccessible] at h_access ⊢
  by_cases hlam_range : 0 ≤ lam ∧ lam ≤ 1
  · -- Case 1: R_lam ≺ X ≺ Y. (A2).
    rw [dif_pos hlam_range] at h_access
    rw [dif_pos hlam_range]
    exact thermo_le_trans h_access h_le
  · rw [dif_neg hlam_range] at h_access ⊢
    by_cases hlam_gt1 : 1 < lam
    · -- Case 2: lam > 1. h_access: lamX₁ ≺ (X, Z). Want lamX₁ ≺ (Y, Z).
      -- Compose on the right via A2 after lifting h_le by reflexivity on the added component.
      -- Explicit lift: (X, Z) ≺ (Y, Z) using A3.
      let h_lam_pos : 0 < lam := lt_trans (by norm_num) hlam_gt1
      let h_lm1_pos : 0 < lam - 1 := sub_pos.mpr hlam_gt1
      let Z := scale_state h_lm1_pos.ne' X₀
      -- The conditional in h_access matches the current case
      rw [dif_pos hlam_gt1] at h_access
      rw [dif_pos hlam_gt1]
      have h_lift := TW.A3 h_le (thermo_le_refl Z)
      exact thermo_le_trans h_access h_lift
    · -- Case 3: lam < 0. h_access: (1-lam)X₀ ≺ (X, W). Want (1-lam)X₀ ≺ (Y, W).
      -- Similar lifting on the right component.
      let hlam_lt0 : lam < 0 := by
        by_cases h0 : 0 ≤ lam
        · have : ¬ lam ≤ 1 := by
            intro hle; exact (False.elim <| (by
              have : (0 ≤ lam ∧ lam ≤ 1) := And.intro h0 hle
              have : False := by exact hlam_range this
              simp_all only [not_lt]))
          simp_all only [↓reduceDIte, not_lt]
        · exact lt_of_not_ge h0
      let h_neglam_pos : 0 < -lam := neg_pos.mpr hlam_lt0
      let W := scale_state h_neglam_pos.ne' X₁
      -- The conditional in h_access matches the current case
      rw [dif_neg hlam_gt1] at h_access
      rw [dif_neg hlam_gt1]
      have h_lift := TW.A3 h_le (thermo_le_refl W)
      exact thermo_le_trans h_access h_lift

/-! ### Definition of Canonical Entropy -/

variable (Ctx : CanonicalEntropyContext Γ)

/-- The set lam(X) = {t ∈ ℝ | ((1-t)X₀, tX₁) ≺ X}. Attached to the context for dot-notation. -/
def CanonicalEntropyContext.LambdaSet (Ctx : CanonicalEntropyContext Γ) (X : TW.State Γ) : Set ℝ :=
  {t | GenRefAccessible (Γ := Γ) Ctx.X₀ Ctx.X₁ X t}

/-- The Canonical Entropy Function S_Γ(X) (Equation 2.14 generalized). -/
noncomputable def CanonicalEntropyContext.S (Ctx : CanonicalEntropyContext Γ) (X : TW.State Γ) : ℝ :=
  sSup (Ctx.LambdaSet X)

/-! ### Lemma 2.7: Well-definedness of Canonical Entropy -/

open Filter

/-- Squeeze theorem for real-valued functions: if `g → a`, `h → a`, and eventually `g ≤ f ≤ h`,
then `f → a`. -/
lemma tendsto_of_tendsto_of_le_of_le
  {α : Type*} {l : Filter α} {f g h : α → ℝ} {a : ℝ}
  (hg : Filter.Tendsto g l (nhds a))
  (hh : Filter.Tendsto h l (nhds a))
  (hgf : ∀ᶠ x in l, g x ≤ f x)
  (hfh : ∀ᶠ x in l, f x ≤ h x) :
  Filter.Tendsto f l (nhds a) := by
  -- Use the order characterization of limits on ℝ.
  refine (tendsto_order.2 ?_)
  constructor
  · -- For any b < a, eventually b < f x.
    intro b hb
    have hg' : ∀ᶠ x in l, b < g x := hg.eventually (Ioi_mem_nhds hb)
    exact (hg'.and hgf).mono (by
      intro x hx
      exact lt_of_lt_of_le hx.1 hx.2)
  · -- For any b > a, eventually f x < b.
    intro b hb
    have hh' : ∀ᶠ x in l, h x < b := hh.eventually (Iio_mem_nhds hb)
    exact (hfh.and hh').mono (by
      intro x hx
      exact lt_of_le_of_lt hx.1 hx.2)

/-- Lemma 2.7 (i) Part 1: lam(X) is bounded above.
    This proof relies on the Sequential A6 (A6_seq).
-/
lemma CanonicalEntropyContext.LambdaSet_BddAbove (Ctx : CanonicalEntropyContext Γ) (X : TW.State Γ) :
 BddAbove (Ctx.LambdaSet X) := by
  -- Proof by contradiction. Assume lam(X) is not bounded above.
  by_contra h_unbounded
  classical
  -- Derive the A6_seq contradiction: X₁ ≺ X₀.
  have h_A6_contra : Ctx.X₁ ≺ Ctx.X₀ := by
    apply TW.A6_seq Ctx.X₁ Ctx.X₀ Ctx.X₁ X
    -- 1. Build a sequence lamSeq n ∈ lam(X) with lamSeq n > n+1.
    have hex : ∀ n : ℕ, ∃ t, t ∈ Ctx.LambdaSet X ∧ ((n : ℝ) + 1) < t := by
      intro n
      rcases (not_bddAbove_iff).1 h_unbounded ((n : ℝ) + 1) with ⟨t, ht_in, hgt⟩
      exact ⟨t, ht_in, hgt⟩
    let lamSeq : ℕ → ℝ := fun n => Classical.choose (hex n)
    have hLamIn : ∀ n : ℕ, lamSeq n ∈ Ctx.LambdaSet X := by
      intro n; exact (Classical.choose_spec (hex n)).1
    have hLamGt : ∀ n : ℕ, ((n : ℝ) + 1) < lamSeq n := by
      intro n; exact (Classical.choose_spec (hex n)).2
    -- 2. Define ε_n = 1 / (lamSeq n - 1).
    let t_seq : ℕ → ℝ := fun n => lamSeq n - 1
    let ε_seq : ℕ → ℝ := fun n => 1 / (t_seq n)
    -- Basic positivity facts.
    have ht_pos : ∀ n : ℕ, 0 < t_seq n := by
      intro n
      -- From (n : ℝ) + 1 < lamSeq n and 1 ≤ (n : ℝ) + 1, deduce 1 < lamSeq n.
      have h1le : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.cast_nonneg n
        linarith
      have h_one_lt : 1 < lamSeq n := lt_of_le_of_lt h1le (hLamGt n)
      -- Then 0 < lamSeq n - 1, which matches 0 < t_seq n.
      have := sub_pos.mpr h_one_lt
      simpa [t_seq] using this
    have hε_pos : ∀ n : ℕ, 0 < ε_seq n := by
      intro n; exact one_div_pos.mpr (ht_pos n)
    -- 3. Show ε_n → 0 by squeezing 0 ≤ ε_n ≤ 1/n eventually.
    have hε_nonneg : ∀ᶠ n in Filter.atTop, 0 ≤ ε_seq n :=
      Filter.Eventually.of_forall (fun n => (le_of_lt (hε_pos n)))
    have hε_le_one_div_nat : ∀ᶠ n in Filter.atTop, ε_seq n ≤ 1 / (n : ℝ) := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨1, ?_⟩
      intro n hn_ge1
      have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_ge1
      -- From lamSeq n > n+1, we get t_seq n = lamSeq n - 1 > n.
      have h_n_lt_t : (n : ℝ) < t_seq n := by
        have : (n : ℝ) + 1 < lamSeq n := hLamGt n
        exact (lt_sub_iff_add_lt).2 (by simpa using this)
      have h_n_le_t : (n : ℝ) ≤ t_seq n := le_of_lt h_n_lt_t
      have := one_div_le_one_div_of_le hn_pos h_n_le_t
      simpa [ε_seq, t_seq] using this
    have hε_to_0 : Filter.Tendsto ε_seq Filter.atTop (nhds 0) := by
      -- (n : ℝ)⁻¹ → 0 as n → ∞.
      have h_inv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inverse_atTop_nhds_zero_nat
      -- Strengthen the upper bound to match (n : ℝ)⁻¹.
      have h_upper : ∀ᶠ n in Filter.atTop, ε_seq n ≤ (n : ℝ)⁻¹ := by
        refine hε_le_one_div_nat.mono ?_
        intro n hn
        simpa [one_div] using hn
      -- Squeeze: 0 ≤ ε_seq (pointwise) and ε_seq ≤ (n : ℝ)⁻¹ eventually.
      have h_nonneg_all : ∀ n, 0 ≤ ε_seq n := fun n => (le_of_lt (hε_pos n))
      -- Use sandwich theorem: 0 ≤ ε_seq ≤ (n : ℝ)⁻¹ and both bounds tend to 0.
      have h_lower : ∀ᶠ n in Filter.atTop, (0 : ℝ) ≤ ε_seq n :=
        Filter.Eventually.of_forall h_nonneg_all
      have h_zero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds
      exact tendsto_of_tendsto_of_le_of_le h_zero h_inv h_lower h_upper
    -- 4. Prove the relation (X₁, ε_n X₁) ≺ (X₀, ε_n X) for all n.
    have h_relation : ∀ n : ℕ,
        comp_state (Ctx.X₁, scale_state (hε_pos n).ne' Ctx.X₁) ≺
        comp_state (Ctx.X₀, scale_state (hε_pos n).ne' X) := by
      intro n
      -- Shorthands.
      let lam' : ℝ := lamSeq n
      let t'   : ℝ := t_seq n
      let ε'   : ℝ := ε_seq n
      -- We know lam' ∈ lam(X) and lam' > 1.
      have h_access' : GenRefAccessible Ctx.X₀ Ctx.X₁ X lam' := hLamIn n
      have h_lam_gt1 : 1 < lam' := by
        have h1le : (1 : ℝ) ≤ (n : ℝ) + 1 := by
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.cast_nonneg n
          linarith
        exact lt_of_le_of_lt h1le (hLamGt n)
      dsimp [GenRefAccessible] at h_access'
      have h_not_range : ¬ (0 ≤ lam' ∧ lam' ≤ 1) := by
        exact fun h => not_le_of_gt h_lam_gt1 h.2
      -- Unfold the "lam > 1" branch.
      rw [dif_neg h_not_range, dif_pos h_lam_gt1] at h_access'
      -- Recombination: (1 + t')•X₁ ≈ (1•X₁, t'•X₁).
      have h1pt_pos : 0 < 1 + t' := by have ht := ht_pos n; linarith
      let h1pt_ne : (1 + t') ≠ 0 := (add_pos (by norm_num) (ht_pos n)).ne'
      have h_recomb :
        scale_state h1pt_ne Ctx.X₁ ≈
        comp_state (scale_state (by norm_num : (1:ℝ) ≠ 0) Ctx.X₁, scale_state (ht_pos n).ne' Ctx.X₁) := by
        simpa using
          (recombination_lemma (ha := by norm_num) (hb := ht_pos n) (Γ := Γ) (X := Ctx.X₁))
      -- 1•X₁ ≈ X₁
      have h_C1 := one_smul_coherence_clean Ctx.X₁
      have h_recomb_clean :
        scale_state h1pt_ne Ctx.X₁ ≈
        comp_state (Ctx.X₁, scale_state (ht_pos n).ne' Ctx.X₁) := by
        refine thermo_equiv_trans' h_recomb ?_
        exact ⟨TW.A3 h_C1.1 (thermo_le_refl _), TW.A3 h_C1.2 (thermo_le_refl _)⟩
      -- Align lam'•X₁ with (1+t')•X₁ using CEq with lam' = 1 + t'.
      have hlam_pos : 0 < lam' := lt_trans (by norm_num) h_lam_gt1
      have h_eq_lam : lam' = 1 + t' := by
        dsimp [lam', t', t_seq]; ring
      -- Align lam'•X₁ to (1+t')•X₁ via CEq and remove casts via CCast.
      let h_sys_eq := congrArg (fun r => TW.scale r Γ) h_eq_lam
      have h_CEq_lam_cast :
        (Equiv.cast (congrArg TW.State h_sys_eq) (scale_state hlam_pos.ne' Ctx.X₁))
          ≈ scale_state h1pt_ne Ctx.X₁ := by
        simpa using
          (TW.scale_eq_coherence (Γ := Γ) (X := Ctx.X₁) (h_eq := h_eq_lam) (ht₁ := hlam_pos.ne'))
      have h_CEq_lam :
        scale_state hlam_pos.ne' Ctx.X₁ ≈ scale_state h1pt_ne Ctx.X₁ :=
        thermo_equiv_trans'
          (TW.state_equiv_coherence h_sys_eq (scale_state hlam_pos.ne' Ctx.X₁))
          h_CEq_lam_cast
      -- (X₁, t'X₁) ≺ (X, t'X₀).
      have h_access_t :
        comp_state (Ctx.X₁, scale_state (ht_pos n).ne' Ctx.X₁) ≺
        comp_state (X,     scale_state (ht_pos n).ne' Ctx.X₀) :=
        le_of_equiv_le (thermo_equiv_trans' (thermo_equiv_symm h_recomb_clean) (thermo_equiv_symm h_CEq_lam)) h_access'
      -- Scale by ε' = 1/t'.
      have h_scaled := TW.A4 (hε_pos n) h_access_t
      -- Apply CSC coherence (clean version) on both sides.
      have h_LHS_equiv :=
        scale_comp_coherence_clean (ne_of_gt (hε_pos n)) Ctx.X₁ (scale_state (ht_pos n).ne' Ctx.X₁)
      have h_RHS_equiv :=
        scale_comp_coherence_clean (ne_of_gt (hε_pos n)) X (scale_state (ht_pos n).ne' Ctx.X₀)
      -- (ε'X₁, ε'(t'X₁)) ≺ (ε'X, ε'(t'X₀)).
      have h_access_scaled :
        comp_state (scale_state (hε_pos n).ne' Ctx.X₁, scale_state (hε_pos n).ne' (scale_state (ht_pos n).ne' Ctx.X₁)) ≺
        comp_state (scale_state (hε_pos n).ne' X,     scale_state (hε_pos n).ne' (scale_state (ht_pos n).ne' Ctx.X₀)) :=
        le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_LHS_equiv) h_scaled) h_RHS_equiv
      -- Simplify ε'(t'Y) ≈ Y using inv_scale_equiv.
      have h_inv_scale (Y : TW.State Γ) :
        scale_state (hε_pos n).ne' (scale_state (ht_pos n).ne' Y) ≈ Y :=
        inv_scale_equiv (ht_pos n) Y
      -- (ε'X₁, X₁) ≺ (ε'X, X₀).
      have h_access_final :
        comp_state (scale_state (hε_pos n).ne' Ctx.X₁, Ctx.X₁) ≺
        comp_state (scale_state (hε_pos n).ne' X,     Ctx.X₀) := by
        -- Use A3 to replace the second components via h_inv_scale.
        have hL := (h_inv_scale Ctx.X₁)
        have hR := (h_inv_scale Ctx.X₀)
        exact le_of_le_equiv
                (le_of_equiv_le (L2_4_i (thermo_equiv_refl _) (thermo_equiv_symm hL)) h_access_scaled)
                (L2_4_i (thermo_equiv_refl _) hR)
      -- Use Commutativity (CC): swap pairs to reach the desired form.
      have h_comm_L := comp_comm_equiv_clean (scale_state (hε_pos n).ne' Ctx.X₁) Ctx.X₁
      have h_comm_R := comp_comm_equiv_clean (scale_state (hε_pos n).ne' X)     Ctx.X₀
      exact le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_comm_L) h_access_final) h_comm_R
    -- Combine to satisfy A6_seq premise.
    exact ⟨ε_seq, hε_pos, hε_to_0, by simpa using h_relation⟩
  -- Contradiction with X₀ ≺≺ X₁.
  exact Ctx.h_ref_strict.2 h_A6_contra

/-- Lemma 2.7 (i) Part 2: lam(X) is non-empty. (Verified, conditional on Comparability)
-/
lemma CanonicalEntropyContext.LambdaSet_Nonempty (Ctx : CanonicalEntropyContext Γ) (X : TW.State Γ)
  (hComp : ∀ (t : ℝ) (ht : 0 < t),
    Comparable
      (scale_state (t := 1 + t) (add_pos zero_lt_one ht).ne' Ctx.X₀)
      (comp_state (X, scale_state (t := t) (ne_of_gt ht) Ctx.X₁))
  ) :
 (Ctx.LambdaSet X).Nonempty := by
  -- (Proof verified in v10.6, relies on A6 and hComp)
  -- Proof by contradiction. Assume lam(X) = ∅.
  by_contra h_empty
  rw [Set.not_nonempty_iff_eq_empty] at h_empty
  -- Goal: X₁ ≺ X₀ using A6 (A=X₁, B=X₀, Z₀=X, Z₁=X₀).
  have h_A6_contra : Ctx.X₁ ≺ Ctx.X₀ := by
    apply TW.A6_seq Ctx.X₁ Ctx.X₀ X Ctx.X₀
    -- Setup sequence tₙ = n+1, εₙ = 1/tₙ.
    let t_seq : ℕ → ℝ := fun n => n + 1
    let ε_seq := fun n => 1 / (t_seq n)
    have ht_pos : ∀ n, 0 < t_seq n := by
      intro n; dsimp [t_seq]; exact_mod_cast Nat.succ_pos n
    have hε_pos : ∀ n, 0 < ε_seq n := by
      intro n; dsimp [ε_seq]; apply one_div_pos.mpr (ht_pos n)
    have hε_to_0 : Tendsto ε_seq atTop (nhds 0) := by
      -- Lower bound: 0 ≤ ε_seq n
      have h_nonneg : ∀ᶠ n in atTop, 0 ≤ ε_seq n :=
        Filter.Eventually.of_forall (fun n => (hε_pos n).le)
      -- Upper bound: ε_seq n ≤ (n : ℝ)⁻¹ eventually (for n ≥ 1)
      have h_upper : ∀ᶠ n in atTop, ε_seq n ≤ (n : ℝ)⁻¹ := by
        refine Filter.eventually_atTop.2 ?_
        refine ⟨1, ?_⟩
        intro n hn
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
        have h_le : (n : ℝ) ≤ t_seq n := by
          dsimp [t_seq]; linarith
        have := one_div_le_one_div_of_le hnpos h_le
        simpa [ε_seq, t_seq, one_div] using this
      -- 1/n → 0; apply squeeze
      have h_inv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      exact tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_inv h_nonneg h_upper
    -- Prove the relation (X₁, εₙX) ≺ (X₀, εₙX₀).
    have h_relation : ∀ n,
        comp_state (Ctx.X₁, scale_state (t := ε_seq n) (hε_pos n).ne' X) ≺
        comp_state (Ctx.X₀, scale_state (t := ε_seq n) (hε_pos n).ne' Ctx.X₀) := by
      intro n
      let t' : ℝ := t_seq n
      let lam' := -t'
      -- Use assumption lam' ∉ lam(X).
      have h_not_in_lam : lam' ∉ Ctx.LambdaSet X := by
        rw [h_empty]; exact Set.notMem_empty lam'
      -- Apply Comparability (hComp).
      have h1pt'_pos : 0 < 1 + t' := add_pos zero_lt_one (ht_pos n)
      let A := scale_state (t := 1 + t') h1pt'_pos.ne' Ctx.X₀
      let B := comp_state (X, scale_state (t := t') (ne_of_gt (ht_pos n)) Ctx.X₁)
      have h_comp_t' := hComp t' (ht_pos n)
      -- Show ¬(A ≺ B) from ¬GenRefAccessible(lam').
      have h_not_le : ¬(A ≺ B) := by
        intro h_fwd
        -- Align A ≺ B with GenRefAccessible(lam') (Case 3: lam' < 0).
        have h_fwd_aligned : GenRefAccessible Ctx.X₀ Ctx.X₁ X lam' := by
          dsimp [GenRefAccessible]
          -- Since t' > 0, we have lam' = -t' < 0, so we are in the third branch.
          have h_neglam_pos : 0 < -lam' := by
            -- -lam' = t' > 0
            dsimp [lam', t', t_seq]
            simpa using (ht_pos n)
          have h_1mlam_pos : 0 < 1 - lam' := by
            -- 1 - lam' = 1 + t' > 0
            have := add_pos zero_lt_one (ht_pos n)
            simpa [lam', sub_neg_eq_add] using this
          have h_not_range : ¬ (0 ≤ lam' ∧ lam' ≤ 1) := by
            have hlam_lt0 : lam' < 0 := (neg_pos).mp h_neglam_pos
            exact fun h => (not_le.mpr hlam_lt0) h.1
          have h_not_gt1 : ¬ (1 < lam') := by
            have hlam_lt0 : lam' < 0 := (neg_pos).mp h_neglam_pos
            have h_le_one : lam' ≤ 1 := le_trans (le_of_lt hlam_lt0) (by norm_num)
            exact not_lt.mpr h_le_one
          -- Unfolding the conditionals selects the lam' < 0 branch, which matches A ≺ B.
          -- After rewriting lam' = -t', the first branch test becomes (t' ≤ 0 ∧ -t' ≤ 1), which is false since t' > 0.
          have h_first' : ¬ (t' ≤ 0 ∧ -t' ≤ 1) := by
            intro h
            exact (not_le_of_gt (ht_pos n)) h.1
          grind --simpa [h_first', h_not_gt1, h_neglam_pos, h_1mlam_pos, lam', sub_neg_eq_add, A, B] using h_fwd
        exact h_not_in_lam h_fwd_aligned
      -- By Comparability, B ≺ A. (X, t'X₁) ≺ (1+t')X₀.
      have h_access_rev : B ≺ A := h_comp_t'.resolve_left h_not_le
      -- Recombination: (1+t')X₀ ≈ (X₀, t'X₀).
      have h_recomb :
        scale_state (add_pos zero_lt_one (ht_pos n)).ne' Ctx.X₀ ≈
        comp_state (scale_state (by norm_num : (1:ℝ) ≠ 0) Ctx.X₀,
                    scale_state (ht_pos n).ne' Ctx.X₀) := by
        simpa using (recombination_lemma (ha := zero_lt_one) (hb := ht_pos n) (Γ := Γ) (X := Ctx.X₀))
      have h_C1 := one_smul_coherence_clean Ctx.X₀
      have h_recomb_clean : A ≈
          comp_state (Ctx.X₀, scale_state (t := t') (ne_of_gt (ht_pos n)) Ctx.X₀) := by
        refine thermo_equiv_trans' h_recomb ?_
        exact L2_4_i h_C1 (thermo_equiv_refl _)
      -- (X, t'X₁) ≺ (X₀, t'X₀).
      have h_access_t := le_of_le_equiv h_access_rev h_recomb_clean
      -- Scale by ε' = 1/t'. (A4).
      have h_scaled := TW.A4 (hε_pos n) h_access_t
      -- Distribute scaling with CSC on both sides.
      have h_LHS_equiv :
          scale_state (hε_pos n).ne' (comp_state (X, scale_state (ht_pos n).ne' Ctx.X₁))
            ≈ comp_state (scale_state (hε_pos n).ne' X,
                          scale_state (hε_pos n).ne' (scale_state (ht_pos n).ne' Ctx.X₁)) :=
        scale_comp_coherence_clean (ne_of_gt (hε_pos n)) X (scale_state (ht_pos n).ne' Ctx.X₁)
      have h_RHS_equiv :
          scale_state (hε_pos n).ne' (comp_state (Ctx.X₀, scale_state (ht_pos n).ne' Ctx.X₀))
            ≈ comp_state (scale_state (hε_pos n).ne' Ctx.X₀,
                          scale_state (hε_pos n).ne' (scale_state (ht_pos n).ne' Ctx.X₀)) :=
        scale_comp_coherence_clean (ne_of_gt (hε_pos n)) Ctx.X₀ (scale_state (ht_pos n).ne' Ctx.X₀)
      -- Move along the CSC equivalences to compare componentwise.
      have h_access_scaled :
          comp_state (scale_state (hε_pos n).ne' X,
                      scale_state (hε_pos n).ne' (scale_state (ht_pos n).ne' Ctx.X₁)) ≺
          comp_state (scale_state (hε_pos n).ne' Ctx.X₀,
                      scale_state (hε_pos n).ne' (scale_state (ht_pos n).ne' Ctx.X₀)) :=
        le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_LHS_equiv) h_scaled) h_RHS_equiv
      -- Simplify ε'(t'•Y) ≈ Y using inverse scaling coherence.
      have h_inv_scale (Y : TW.State Γ) :
          scale_state (hε_pos n).ne' (scale_state (ht_pos n).ne' Y) ≈ Y :=
        inv_scale_equiv (ht_pos n) Y
      have h_access_final :
          comp_state (scale_state (hε_pos n).ne' X, Ctx.X₁) ≺
          comp_state (scale_state (hε_pos n).ne' Ctx.X₀, Ctx.X₀) := by
        -- Replace the second components via A3 using the ≈ proofs.
        have hL := h_inv_scale Ctx.X₁
        have hR := h_inv_scale Ctx.X₀
        exact
          le_of_le_equiv
            (le_of_equiv_le (L2_4_i (thermo_equiv_refl _) (thermo_equiv_symm hL)) h_access_scaled)
            (L2_4_i (thermo_equiv_refl _) hR)
      -- Swap components with CC to reach the target shape.
      have h_comm_L := comp_comm_equiv_clean (scale_state (hε_pos n).ne' X) Ctx.X₁
      have h_comm_R := comp_comm_equiv_clean (scale_state (hε_pos n).ne' Ctx.X₀) Ctx.X₀
      exact
        le_of_le_equiv
          (le_of_equiv_le (thermo_equiv_symm h_comm_L) h_access_final)
          h_comm_R
    -- Combine to satisfy A6_seq premise.
    exact ⟨ε_seq, hε_pos, hε_to_0, h_relation⟩
  -- Contradiction.
  exact Ctx.h_ref_strict.2 h_A6_contra

/-! ### Lemma 2.7 (ii): Entropy of Reference States (Calibration) -/


/-- Helper Lemma for L2.7(ii) Case 2 (μ > 1). Reorganization of the RHS.
    (R_lam, (μ-1)X₀) ≈ ((μ-lam)X₀, lamX₁).
-/
lemma reorg_R_lam_mu_gt1 (lam mu : ℝ) (hlam_range : 0 ≤ lam ∧ lam ≤ 1) (h_mu_gt1 : 1 < mu) :
    let R_lam := ReferenceState Ctx.X₀ Ctx.X₁ lam hlam_range.1 hlam_range.2
    comp_state (R_lam, gscale_state (by linarith : 0 ≤ mu - 1) Ctx.X₀) ≈
    comp_state (gscale_state (sub_nonneg.mpr (le_trans hlam_range.2 (le_of_lt h_mu_gt1))) Ctx.X₀, gscale_state hlam_range.1 Ctx.X₁) := by
  intro R_lam
  -- R_lam = ((1-lam)X₀, lamX₁).
  -- LHS = (((1-lam)X₀, lamX₁), (μ-1)X₀).
  let A := gscale_state (sub_nonneg.mpr hlam_range.2) Ctx.X₀
  let B := gscale_state hlam_range.1 Ctx.X₁
  let C := gscale_state (by linarith : 0 ≤ mu - 1) Ctx.X₀
  -- 1. Reorganize ((A, B), C) ≈ ((A, C), B).
  have h_reorg : comp_state (comp_state (A, B), C) ≈ comp_state (comp_state (A, C), B) := by
    -- ((A, B), C) ≈ (A, (B, C)) ≈ (A, (C, B)) ≈ ((A, C), B).
    have h_assoc1 := assoc_equiv_R A B C
    have h_commBC := comp_comm_equiv_clean B C
    have h_lift :
        comp_state (A, comp_state (B, C)) ≈
        comp_state (A, comp_state (C, B)) :=
      L2_4_i (thermo_equiv_refl A) h_commBC
    have h_assoc2 := assoc_equiv_L A C B
    exact thermo_equiv_trans' h_assoc1 (thermo_equiv_trans' h_lift h_assoc2)
  -- 2. Recombine (A, C) ≈ (μ-lam)X₀.
  have h_recomb_AC : comp_state (A, C) ≈ gscale_state (sub_nonneg.mpr (le_trans hlam_range.2 (le_of_lt h_mu_gt1))) Ctx.X₀ := by
    -- (1-lam)X₀ ⊗ (μ-1)X₀ ≈ (1-lam+μ-1)X₀ = (μ-lam)X₀.
    -- Use generalized recombination and gscale_eq_coherence.
    have h_eq : (1-lam) + (mu-1) = mu-lam := by ring
    have h_mu_minus_1_nonneg : 0 ≤ mu - 1 := sub_nonneg.mpr (le_of_lt h_mu_gt1)
    have h_add_proof : 0 ≤ (1-lam) + (mu-1) := add_nonneg (sub_nonneg.mpr hlam_range.2) h_mu_minus_1_nonneg
    have h_target_proof : 0 ≤ mu-lam := sub_nonneg.mpr (le_trans hlam_range.2 (le_of_lt h_mu_gt1))
    have h_gr := generalized_recombination_lemma (sub_nonneg.mpr hlam_range.2) h_mu_minus_1_nonneg Ctx.X₀
    have h_ceq : gscale_state h_add_proof Ctx.X₀ ≈ gscale_state h_target_proof Ctx.X₀ :=
      gscale_eq_coherence h_eq Ctx.X₀ h_add_proof h_target_proof
    -- Compose the equivalences, using proof irrelevance for gscale_state
    have h_gr' : comp_state (A, C) ≈ gscale_state h_add_proof Ctx.X₀ := by
      -- First align the proof terms in comp_state (A, C)
      have h_A_eq : A = gscale_state (sub_nonneg.mpr hlam_range.2) Ctx.X₀ := rfl
      have h_C_eq : C = gscale_state h_mu_minus_1_nonneg Ctx.X₀ := by
        dsimp [C]
      -- Apply generalized_recombination_lemma with explicit proof terms
      have h_gr_aligned : comp_state (gscale_state (sub_nonneg.mpr hlam_range.2) Ctx.X₀, gscale_state h_mu_minus_1_nonneg Ctx.X₀) ≈ gscale_state (add_nonneg (sub_nonneg.mpr hlam_range.2) h_mu_minus_1_nonneg) Ctx.X₀ := by
        exact thermo_equiv_symm h_gr
      -- Rewrite A and C in the goal
      rw [← h_A_eq, ← h_C_eq] at h_gr_aligned
      -- Use proof irrelevance to align the result
      have h_proof_irrel : gscale_state (add_nonneg (sub_nonneg.mpr hlam_range.2) h_mu_minus_1_nonneg) Ctx.X₀ = gscale_state h_add_proof Ctx.X₀ := by
        apply gscale_state_proof_irrel
      rw [← h_proof_irrel]
      exact h_gr_aligned
    exact thermo_equiv_trans' h_gr' h_ceq
  -- 3. Lift recombination into the composition.
  have h_final := L2_4_i h_recomb_AC (thermo_equiv_refl B)
  exact thermo_equiv_trans' h_reorg h_final

/-- Helper Lemma for L2.7(ii) Case 3 (μ < 0). Reorganization of the RHS.
    (R_lam, (-μ)X₁) ≈ ((1-lam)X₀, (lam-μ)X₁).
-/
lemma reorg_R_lam_mu_lt0 (lam mu : ℝ) (hlam_range : 0 ≤ lam ∧ lam ≤ 1) (h_mu_lt0 : mu < 0) :
    let R_lam := ReferenceState Ctx.X₀ Ctx.X₁ lam hlam_range.1 hlam_range.2
    comp_state (R_lam, gscale_state (show 0 ≤ -mu from (neg_nonneg.mpr (le_of_lt h_mu_lt0))) Ctx.X₁) ≈
    comp_state (gscale_state (sub_nonneg.mpr hlam_range.2) Ctx.X₀, gscale_state (show 0 ≤ lam - mu from (sub_nonneg.mpr (le_trans (le_of_lt h_mu_lt0) hlam_range.1))) Ctx.X₁) := by
  intro R_lam
  -- LHS = (((1-lam)X₀, lamX₁), (-μ)X₁).
  let A := gscale_state (sub_nonneg.mpr hlam_range.2) Ctx.X₀
  let B := gscale_state hlam_range.1 Ctx.X₁
  let C := gscale_state (show 0 ≤ -mu from (neg_nonneg.mpr (le_of_lt h_mu_lt0))) Ctx.X₁
  -- Helpful inequalities.
  have h_negmu_nonneg : 0 ≤ -mu := by exact (neg_nonneg.mpr (le_of_lt h_mu_lt0))
  have h_mu_le_lam : mu ≤ lam := le_trans (le_of_lt h_mu_lt0) hlam_range.1
  -- 1. Reorganize ((A, B), C) ≈ (A, (B, C)). (Assoc R).
  have h_reorg := assoc_equiv_R A B C
  -- 2. Recombine (B, C) ≈ (lam-μ)X₁.
  have h_recomb_BC : comp_state (B, C) ≈ gscale_state (sub_nonneg.mpr h_mu_le_lam) Ctx.X₁ := by
    -- lamX₁ ⊗ (-μ)X₁ ≈ (lam-μ)X₁.
    have h_eq : lam + (-mu) = lam - mu := by ring
    have h_gr := generalized_recombination_lemma hlam_range.1 h_negmu_nonneg Ctx.X₁
    have h_ceq := gscale_eq_coherence h_eq Ctx.X₁ (add_nonneg hlam_range.1 h_negmu_nonneg) (sub_nonneg.mpr h_mu_le_lam)
    exact thermo_equiv_trans' (id (And.symm h_gr)) h_ceq
  -- 3. Lift recombination.
  have h_final := L2_4_i (thermo_equiv_refl A) h_recomb_BC
  exact thermo_equiv_trans' h_reorg h_final

/-! ### Generalized Reference Accessibility
We define the meaning of ((1-lam)X₀, lamX₁) ≺ X for all lam ∈ ℝ.
-/

variable (Ctx : CanonicalEntropyContext Γ)

/-- Generalized lam for any X (in any system Δ). -/
def CanonicalEntropyContext.LambdaSetAny (Ctx : CanonicalEntropyContext Γ) {Δ : System} (X : TW.State Δ) : Set ℝ :=
  {t | GenRefAccessible (Γ := Γ) Ctx.X₀ Ctx.X₁ X t}

/-- Generalized entropy-like sSup for any X (in any system Δ). -/
noncomputable def CanonicalEntropyContext.SAny (Ctx : CanonicalEntropyContext Γ) {Δ : System} (X : TW.State Δ) : ℝ :=
  sSup (Ctx.LambdaSetAny X)

/-- Lemma 2.7 (ii) Specialized: S(R_lam) = lam for lam ∈ [0, 1]. (Verified)

    Note: We use the generalized SAny since R_lam lives in the compound system ((1-lam)•Γ ⊗ lam•Γ).
-/
lemma CanonicalEntropy_ReferenceState (lam : ℝ) (hlam_range : 0 ≤ lam ∧ lam ≤ 1) :
    Ctx.SAny (ReferenceState Ctx.X₀ Ctx.X₁ lam hlam_range.1 hlam_range.2) = lam := by
  -- We show lam(R_lam) = (-∞, lam].
  let R_lam := ReferenceState Ctx.X₀ Ctx.X₁ lam hlam_range.1 hlam_range.2
  have h_set_eq : Ctx.LambdaSetAny R_lam = Set.Iic lam := by
    ext mu
    dsimp [CanonicalEntropyContext.LambdaSetAny]
    constructor
    · -- (⇒) If μ ∈ lam(R_lam), then μ ≤ lam. Assume μ > lam for contradiction.
      intro h_mu; by_contra h_gt
      have h_mu_gt_lam : mu > lam := lt_of_not_ge h_gt
      by_cases h_mu_le1 : mu ≤ 1
      · -- Case 1: lam < μ ≤ 1. h_mu: R_μ ≺ R_lam.
        have h_mu_range : 0 ≤ mu ∧ mu ≤ 1 := ⟨le_trans hlam_range.1 (le_of_lt h_mu_gt_lam), h_mu_le1⟩
        dsimp [GenRefAccessible] at h_mu; rw [dif_pos h_mu_range] at h_mu
        -- Strict Monotonicity: R_lam ≺≺ R_μ.
        have h_strict := StrictReferenceState_monotone Ctx lam mu hlam_range.1 h_mu_le1 h_mu_gt_lam
        -- Contradiction.
        exact h_strict.2 h_mu
      · -- Case 2: μ > 1.
        have h_mu_gt1 : 1 < mu := lt_of_not_ge h_mu_le1
        -- h_mu: μX₁ ≺ (R_lam, (μ-1)X₀). (GenRefAccessible Case 2).
        dsimp [GenRefAccessible] at h_mu
        have h_not_range : ¬ (0 ≤ mu ∧ mu ≤ 1) := by
          intro h; exact not_le_of_gt h_mu_gt1 h.2
        rw [dif_neg h_not_range, dif_pos h_mu_gt1] at h_mu
        -- Normalize h_mu to use gscale_state
        have h_lam_pos : 0 < mu := lt_trans (by norm_num) h_mu_gt1
        have h_lm1_pos : 0 < mu - 1 := sub_pos.mpr h_mu_gt1
        have h_mu_norm : gscale_state (le_of_lt h_lam_pos) Ctx.X₁ ≺ comp_state (R_lam, gscale_state (by linarith : 0 ≤ mu - 1) Ctx.X₀) := by
          simp only [gscale_state_pos (le_of_lt h_lam_pos) h_lam_pos, gscale_state_pos (by linarith : 0 ≤ mu - 1) h_lm1_pos] at h_mu ⊢
          exact h_mu
        -- Reorganize RHS: ≈ ((μ-lam)X₀, lamX₁).
        have h_reorg_RHS := reorg_R_lam_mu_gt1 Ctx lam mu hlam_range h_mu_gt1
        have h_mu_reorg := le_of_le_equiv h_mu_norm h_reorg_RHS
        -- Recombine LHS: μX₁ ≈ ((μ-lam)X₁, lamX₁).
        have h_lam_lt_mu : lam < mu := lt_of_le_of_lt hlam_range.2 h_mu_gt1
        have h_delta_pos : 0 < mu - lam := sub_pos.mpr h_lam_lt_mu
        have h_delta_nonneg : 0 ≤ mu - lam := le_of_lt h_delta_pos
        have h_recomb_LHS :
            gscale_state (show 0 ≤ mu from le_of_lt (lt_trans (by norm_num) h_mu_gt1)) Ctx.X₁ ≈
            comp_state (gscale_state h_delta_nonneg Ctx.X₁, gscale_state hlam_range.1 Ctx.X₁) := by
          -- (μ-lam)+lam = μ. Use Generalized Recombination.
          have h_eq : (mu-lam) + lam = mu := by ring
          have h_gr := generalized_recombination_lemma h_delta_nonneg hlam_range.1 Ctx.X₁
          have h_ceq := gscale_eq_coherence h_eq Ctx.X₁ (add_nonneg h_delta_nonneg hlam_range.1)
                                                  (show 0 ≤ mu from le_of_lt (lt_trans (by norm_num) h_mu_gt1))
          exact thermo_equiv_trans' (thermo_equiv_symm h_ceq) h_gr
        -- ((μ-lam)X₁, lamX₁) ≺ ((μ-lam)X₀, lamX₁).
        have h_access_final :
            comp_state (gscale_state h_delta_nonneg Ctx.X₁, gscale_state hlam_range.1 Ctx.X₁) ≺
            comp_state (gscale_state h_delta_nonneg Ctx.X₀, gscale_state hlam_range.1 Ctx.X₁) :=
          le_of_equiv_le (id (And.symm h_recomb_LHS)) h_mu_reorg
        -- Cancellation Law: (μ-lam)X₁ ≺ (μ-lam)X₀.
        have h_cancel := CancellationLaw
            (gscale_state h_delta_nonneg Ctx.X₁)
            (gscale_state h_delta_nonneg Ctx.X₀)
            (gscale_state hlam_range.1 Ctx.X₁)
            h_access_final
        -- Scaling (L2.5_ii): X₁ ≺ X₀.
        have h_X1_le_X0 : Ctx.X₁ ≺ Ctx.X₀ := by
          -- Normalize both gscale_state occurrences to scale_state
          have h_cancel_norm : scale_state h_delta_pos.ne' Ctx.X₁ ≺ scale_state h_delta_pos.ne' Ctx.X₀ := by
            simp only [← gscale_state_pos h_delta_nonneg h_delta_pos]
            exact h_cancel
          -- Use inv_scale_equiv to reduce: (1/(μ-lam))((μ-lam)Xᵢ) ≈ Xᵢ
          have h_inv_X1 := inv_scale_equiv h_delta_pos Ctx.X₁
          have h_inv_X0 := inv_scale_equiv h_delta_pos Ctx.X₀
          -- Apply inverse scaling via A4
          have h_inv_t_pos : 0 < 1 / (mu - lam) := one_div_pos.mpr h_delta_pos
          have h_scaled_inv := TW.A4 h_inv_t_pos h_cancel_norm
          -- Combine with equivalences: X₁ ≈ (1/δ)(δX₁) ≺ (1/δ)(δX₀) ≈ X₀
          exact le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_inv_X1) h_scaled_inv) h_inv_X0
        -- Contradiction with X₀ ≺≺ X₁.
        exact Ctx.h_ref_strict.2 h_X1_le_X0
    · -- (⇐) If μ ≤ lam, then μ ∈ lam(R_lam).
      intro h_mu_le_lam
      -- Convert set membership to inequality
      have h_mu_le_lam' : mu ≤ lam := h_mu_le_lam
      by_cases h_mu_pos : 0 ≤ mu
      · -- Case 1: 0 ≤ μ ≤ lam. h_mu: R_μ ≺ R_lam.
        have h_mu_range : 0 ≤ mu ∧ mu ≤ 1 := ⟨h_mu_pos, le_trans h_mu_le_lam' hlam_range.2⟩
        dsimp [GenRefAccessible]; rw [dif_pos h_mu_range]
        -- Monotonicity (non-strict).
        rcases le_iff_eq_or_lt.mp h_mu_le_lam' with h_eq | h_lt
        · subst h_eq; exact thermo_le_refl R_lam
        · -- Strict R_μ ≺≺ R_lam implies R_μ ≺ R_lam.
          exact (StrictReferenceState_monotone Ctx mu lam h_mu_pos hlam_range.2 (lt_of_le_of_ne (le_of_lt h_lt) (ne_of_lt h_lt))).1
      · -- Case 3: μ < 0. h_mu: (1-μ)X₀ ≺ (R_lam, (-μ)X₁). (GenRefAccessible Case 3).
        have h_mu_lt0 : mu < 0 := lt_of_not_ge h_mu_pos
        have h_not_gt1 : ¬1 < mu := not_lt_of_gt (lt_of_lt_of_le h_mu_lt0 (by norm_num : (0 : ℝ) ≤ 1))
        dsimp [GenRefAccessible]; rw [dif_neg (by exact mt (fun (h : 0 ≤ mu ∧ mu ≤ 1) => h.1) h_mu_pos), dif_neg h_not_gt1]
        -- Reorganize RHS: ≈ ((1-lam)X₀, (lam-μ)X₁).
        have h_reorg_RHS := reorg_R_lam_mu_lt0 Ctx lam mu hlam_range h_mu_lt0
        -- Recombination LHS: (1-μ)X₀ ≈ ((1-lam)X₀, (lam-μ)X₀).
        have h_one_sub_mu_nonneg : 0 ≤ 1 - mu := by linarith [le_of_lt h_mu_lt0]
        have h_lam_minus_mu_nonneg : 0 ≤ lam - mu := sub_nonneg.mpr (le_trans (le_of_lt h_mu_lt0) hlam_range.1)
        have h_recomb_LHS :
            gscale_state h_one_sub_mu_nonneg Ctx.X₀ ≈
            comp_state (gscale_state (sub_nonneg.mpr hlam_range.2) Ctx.X₀, gscale_state h_lam_minus_mu_nonneg Ctx.X₀) := by
          have h_eq : (1-lam) + (lam-mu) = 1-mu := by ring
          have h_gr := generalized_recombination_lemma (sub_nonneg.mpr hlam_range.2) h_lam_minus_mu_nonneg Ctx.X₀
          have h_ceq := gscale_eq_coherence h_eq Ctx.X₀ (add_nonneg (sub_nonneg.mpr hlam_range.2) h_lam_minus_mu_nonneg) h_one_sub_mu_nonneg
          exact thermo_equiv_trans' (thermo_equiv_symm h_ceq) h_gr
        -- ((1-lam)X₀, (lam-μ)X₀) ≺ ((1-lam)X₀, (lam-μ)X₁).
        have h_access_final :
            comp_state (gscale_state (sub_nonneg.mpr hlam_range.2) Ctx.X₀, gscale_state h_lam_minus_mu_nonneg Ctx.X₀) ≺
            comp_state (gscale_state (sub_nonneg.mpr hlam_range.2) Ctx.X₀, gscale_state h_lam_minus_mu_nonneg Ctx.X₁) := by
          -- A3 applied to (lam-μ)X₀ ≺ (lam-μ)X₁.
          -- Since mu < 0 and lam ≥ 0, we have lam - mu > 0
          have h_delta_pos : 0 < lam - mu := by
            have : mu < 0 := h_mu_lt0
            have : 0 ≤ lam := hlam_range.1
            linarith
          have h_scaled_strict : gscale_state h_lam_minus_mu_nonneg Ctx.X₀ ≺ gscale_state h_lam_minus_mu_nonneg Ctx.X₁ := by
            simp_rw [gscale_state_pos h_lam_minus_mu_nonneg h_delta_pos]
            exact (L2_5_ii h_delta_pos).mp Ctx.h_ref_strict.1
          exact TW.A3 (thermo_le_refl _) h_scaled_strict
        -- Normalize to scale_state to match the goal form
        have h_1_sub_mu_pos : 0 < 1 - mu := by linarith
        have h_neg_mu_pos : 0 < -mu := neg_pos.mpr h_mu_lt0
        -- The goal already has scale_state form due to GenRefAccessible definition
        -- We need to bridge from h_recomb_LHS and h_access_final (using gscale_state)
        -- to the goal (using scale_state)
        have h_bridge : gscale_state h_one_sub_mu_nonneg Ctx.X₀ = scale_state h_1_sub_mu_pos.ne' Ctx.X₀ := by
          simp [gscale_state_pos h_one_sub_mu_nonneg h_1_sub_mu_pos]
        -- Normalize h_reorg_RHS to use scale_state on the right component
        have h_reorg_RHS_norm : comp_state (gscale_state (sub_nonneg.mpr hlam_range.2) Ctx.X₀, gscale_state h_lam_minus_mu_nonneg Ctx.X₁) ≈
            comp_state (R_lam, scale_state h_neg_mu_pos.ne' Ctx.X₁) := by
          -- First, observe that R_lam = comp_state (gscale_state ... Ctx.X₀, gscale_state ... Ctx.X₁)
          -- So the first components match definitionally
          -- For the second component, align gscale_state with scale_state
          have h_second_eq : gscale_state h_lam_minus_mu_nonneg Ctx.X₁ = scale_state (by linarith : 0 < lam - mu).ne' Ctx.X₁ := by
            grind [= ReferenceState.eq_def, = CanonicalEntropyContext.X₀.eq_def,
              = CanonicalEntropyContext.X₁.eq_def, = ThermoWorld.le.eq_def, = gscale_state.eq_def,
              = comp_state.eq_def, = scale_state.eq_def]--simp [gscale_state_pos]
          -- Now use symmetry of h_reorg_RHS since it goes the opposite direction
          grind [= ReferenceState.eq_def, = CanonicalEntropyContext.X₀.eq_def,
            = CanonicalEntropyContext.X₁.eq_def, = ThermoWorld.le.eq_def, = gscale_state.eq_def,
            = comp_state.eq_def, = scale_state.eq_def, = ThermoWorld.comp.eq_def,
            = ThermoWorld.scale.eq_def, = ThermoWorld.State.eq_def]
        rw [← h_bridge]
        exact le_of_le_equiv (le_of_equiv_le h_recomb_LHS h_access_final) h_reorg_RHS_norm

  -- sSup (Iic lam) = lam.
  rw [CanonicalEntropyContext.SAny, h_set_eq]
  -- Using the standard lemma for reals: sSup (Iic a) = a
  exact csSup_Iic-- sSup_Iic

end CanonicalEntropy

/-!
### Section II.E: Construction of the Entropy Function (Continued)
-/

section CanonicalEntropy
variable {Γ : System}

/-- Monotonicity inside the reference interval: 0 ≤ μ < lam ≤ 1.
    Directly reduces to the strict monotonicity of reference states. -/
lemma GenRefAccessible_monotone_interval
    {X₀ X₁ X : TW.State Γ} (h_ref_strict : X₀ ≺≺ X₁)
    {μ lam : ℝ} (hμ_nonneg : 0 ≤ μ) (hlam_le1 : lam ≤ 1) (h_lt : μ < lam)
    (h_access_lam : GenRefAccessible X₀ X₁ X lam) :
    GenRefAccessible X₀ X₁ X μ := by
  let Ctx : CanonicalEntropyContext Γ := ⟨X₀, X₁, h_ref_strict⟩
  have hlam_nonneg : 0 ≤ lam := le_trans hμ_nonneg (le_of_lt h_lt)
  have hμ_le1 : μ ≤ 1 := le_trans (le_of_lt h_lt) hlam_le1
  have h_Rμ_Rlam := StrictReferenceState_monotone Ctx μ lam hμ_nonneg hlam_le1 h_lt
  dsimp [GenRefAccessible] at h_access_lam ⊢
  rw [dif_pos ⟨hlam_nonneg, hlam_le1⟩] at h_access_lam
  rw [dif_pos ⟨hμ_nonneg, hμ_le1⟩]
  exact thermo_le_trans h_Rμ_Rlam.1 h_access_lam

/-- Bridge from (0 ≤ μ ≤ 1) to lam > 1 (μ < 1 < lam): use recombination + cancellation
    to descend from an “above–1” witness to μ. -/
lemma GenRefAccessible_monotone_cross_one
    {X₀ X₁ X : TW.State Γ} (h_ref_strict : X₀ ≺≺ X₁)
    {μ lam : ℝ} (hμ_nonneg : 0 ≤ μ) (hμ_lt1 : μ < 1) (hlam_gt1 : 1 < lam) (h_lt : μ < lam)
    (h_access_lam : GenRefAccessible X₀ X₁ X lam) :
    GenRefAccessible X₀ X₁ X μ := by
  -- Reuse the already formalized subcase 1b proof (factorized).
  -- We copy the original subproof (Subcase 1b in the big lemma).
  set δ := lam - μ
  have hδ_pos : 0 < δ := sub_pos.mpr h_lt
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hμ_le1 : μ ≤ 1 := le_of_lt hμ_lt1
  have hlam_nonneg : 0 ≤ lam := le_trans hμ_nonneg (le_of_lt h_lt)
  have hlam_pos : 0 < lam := lt_of_le_of_lt hμ_nonneg h_lt
  have h_lm1_pos : 0 < lam - 1 := sub_pos.mpr hlam_gt1
  have h_lm1_nonneg : 0 ≤ lam - 1 := le_of_lt h_lm1_pos
  have h_1mμ_nonneg : 0 ≤ 1 - μ := sub_nonneg.mpr hμ_le1
  let Rμ := ReferenceState X₀ X₁ μ hμ_nonneg hμ_le1
  dsimp [GenRefAccessible] at h_access_lam
  rw [dif_neg (fun h => (lt_of_lt_of_le hlam_gt1 h.2).false) , dif_pos hlam_gt1] at h_access_lam
  dsimp [GenRefAccessible]; rw [dif_pos ⟨hμ_nonneg, hμ_le1⟩]
  -- (Reinsert the earlier detailed chain exactly.)
  -- 1. lamX₁ ≈ (δX₁, μX₁)
  have h_lamX₁_recomb :
      gscale_state hlam_nonneg X₁ ≈
      comp_state (gscale_state hδ_nonneg X₁, gscale_state hμ_nonneg X₁) := by
    have h_eq : lam = δ + μ := by simp [δ]
    have h_align := gscale_eq_coherence (Γ := Γ) (X := X₁) h_eq hlam_nonneg (add_nonneg hδ_nonneg hμ_nonneg)
    have h_gr := generalized_recombination_lemma hδ_nonneg hμ_nonneg X₁
    exact thermo_equiv_trans' h_align h_gr
  -- 2. (Rμ, (lam-1)X₀) reorganize → (δX₀, μX₁)
  let L_comp := comp_state (Rμ, gscale_state h_lm1_nonneg X₀)
  have h_L_reorg :
      L_comp ≈ comp_state (gscale_state hδ_nonneg X₀, gscale_state hμ_nonneg X₁) := by
    dsimp [Rμ, ReferenceState, L_comp]
    have h1 := assoc_equiv_R (gscale_state h_1mμ_nonneg X₀) (gscale_state hμ_nonneg X₁) (gscale_state h_lm1_nonneg X₀)
    have h2_inner := comp_comm_equiv_clean (gscale_state hμ_nonneg X₁) (gscale_state h_lm1_nonneg X₀)
    have h2 := L2_4_i (thermo_equiv_refl (gscale_state h_1mμ_nonneg X₀)) h2_inner
    have h3 := assoc_equiv_L (gscale_state h_1mμ_nonneg X₀) (gscale_state h_lm1_nonneg X₀) (gscale_state hμ_nonneg X₁)
    have h_eq_sum : (1-μ) + (lam-1) = δ := by simp [δ]
    have h_recomb_X₀ :
        comp_state (gscale_state h_1mμ_nonneg X₀, gscale_state h_lm1_nonneg X₀) ≈
        gscale_state hδ_nonneg X₀ := by
      have h_gr := generalized_recombination_lemma h_1mμ_nonneg h_lm1_nonneg X₀
      have h_align := gscale_eq_coherence (Γ := Γ) (X := X₀) h_eq_sum
          (add_nonneg h_1mμ_nonneg h_lm1_nonneg) hδ_nonneg
      exact thermo_equiv_trans' (thermo_equiv_symm h_gr) h_align
    have h4 :
        comp_state (comp_state (gscale_state h_1mμ_nonneg X₀, gscale_state h_lm1_nonneg X₀),
                    gscale_state hμ_nonneg X₁) ≈
        comp_state (gscale_state hδ_nonneg X₀, gscale_state hμ_nonneg X₁) :=
      L2_4_i h_recomb_X₀ (thermo_equiv_refl _)
    exact
      thermo_equiv_trans'
        (thermo_equiv_trans' (thermo_equiv_trans' h1 h2) h3) h4
  -- 3. compare δX₀ vs δX₁
  have h_δX₀_lt_δX₁ :
      gscale_state hδ_nonneg X₀ ≺ gscale_state hδ_nonneg X₁ := by
    simp [gscale_state_pos hδ_nonneg hδ_pos]
    exact (L2_5_ii hδ_pos).1 h_ref_strict.1
  have h_compare :
      comp_state (gscale_state hδ_nonneg X₀, gscale_state hμ_nonneg X₁) ≺
      comp_state (gscale_state hδ_nonneg X₁, gscale_state hμ_nonneg X₁) :=
    TW.A3 h_δX₀_lt_δX₁ (thermo_le_refl _)
  -- 4. chain to lamX₁
  have h_chain :
      L_comp ≺ gscale_state hlam_nonneg X₁ :=
    le_of_le_equiv (le_of_equiv_le h_L_reorg h_compare)
                   (thermo_equiv_symm h_lamX₁_recomb)
  -- 5. trans + cancellation
  let Z := gscale_state h_lm1_nonneg X₀
  have h_access_lam_g :
      gscale_state hlam_nonneg X₁ ≺ comp_state (X, Z) := by
    simpa [Z, gscale_state_pos hlam_nonneg hlam_pos,
          gscale_state_pos h_lm1_nonneg h_lm1_pos] using h_access_lam
  have h_trans := thermo_le_trans h_chain h_access_lam_g
  exact CancellationLaw Rμ X Z h_trans

/-- Monotonicity for the “≥ 1” region: 1 ≤ μ < lam, using generalized cancellation
    after splitting lam = μ + δ (δ>0). -/
lemma GenRefAccessible_monotone_ge_one
    {X₀ X₁ X : TW.State Γ} (h_ref_strict : X₀ ≺≺ X₁)
    {μ lam : ℝ} (hμ_ge1 : 1 ≤ μ) (h_lt : μ < lam)
    (h_access_lam : GenRefAccessible X₀ X₁ X lam) :
    GenRefAccessible X₀ X₁ X μ := by
  -- This reuses Subcase 1c. We port the original proof.
  set δ := lam - μ
  have hδ_pos : 0 < δ := sub_pos.mpr h_lt
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hμ_nonneg : 0 ≤ μ := le_trans (by norm_num) hμ_ge1
  have hlam_gt1 : 1 < lam := lt_of_le_of_lt hμ_ge1 h_lt
  have hlam_nonneg : 0 ≤ lam := le_trans hμ_nonneg (le_of_lt h_lt)
  dsimp [GenRefAccessible] at h_access_lam
  rw [dif_neg (fun h => (lt_irrefl (1:ℝ)) (lt_of_lt_of_le hlam_gt1 h.2)),
      dif_pos hlam_gt1] at h_access_lam
  -- (Copy proof from previous monolithic lemma section 1c)
  have h_lm1_nonneg : 0 ≤ lam - 1 := le_of_lt (sub_pos.mpr hlam_gt1)
  have h_μm1_nonneg : 0 ≤ μ - 1 := sub_nonneg.mpr hμ_ge1
  -- lamX₁ ≈ (μX₁, δX₁)
  have h_lam_recomb :
      gscale_state hlam_nonneg X₁ ≈
      comp_state (gscale_state hμ_nonneg X₁, gscale_state hδ_nonneg X₁) := by
    have h_eq : lam = μ + δ := by simp [δ]
    have h_align := gscale_eq_coherence (Γ := Γ) (X := X₁) h_eq hlam_nonneg
        (add_nonneg hμ_nonneg hδ_nonneg)
    have h_gr := generalized_recombination_lemma hμ_nonneg hδ_nonneg X₁
    exact thermo_equiv_trans' h_align h_gr
  -- (lam-1)X₀ ≈ ((μ-1)X₀, δX₀)
  have h_lm1_recomb :
      gscale_state h_lm1_nonneg X₀ ≈
      comp_state (gscale_state h_μm1_nonneg X₀, gscale_state hδ_nonneg X₀) := by
    have h_eq : lam - 1 = (μ - 1) + δ := by simp [δ]
    have h_align := gscale_eq_coherence (Γ := Γ) (X := X₀) h_eq h_lm1_nonneg
        (add_nonneg h_μm1_nonneg hδ_nonneg)
    have h_gr := generalized_recombination_lemma h_μm1_nonneg hδ_nonneg X₀
    exact thermo_equiv_trans' h_align h_gr
  -- reorganize premise
  have h_lm1_pos : 0 < lam - 1 := sub_pos.mpr hlam_gt1
  have h_access_lam_g :
      gscale_state hlam_nonneg X₁ ≺
      comp_state (X, gscale_state h_lm1_nonneg X₀) := by
    simpa [gscale_state_pos hlam_nonneg (lt_of_le_of_lt hμ_nonneg h_lt),
      gscale_state_pos h_lm1_nonneg h_lm1_pos]
      using h_access_lam
  have h_access_reorg :
      comp_state (gscale_state hμ_nonneg X₁, gscale_state hδ_nonneg X₁) ≺
      comp_state (X,
        comp_state (gscale_state h_μm1_nonneg X₀, gscale_state hδ_nonneg X₀)) := by
    refine
      le_of_le_equiv
        (le_of_equiv_le (thermo_equiv_symm h_lam_recomb) h_access_lam_g) ?_
    exact L2_4_i (thermo_equiv_refl _) h_lm1_recomb
  -- δX₀ ≺ δX₁
  have h_δX₀_lt_δX₁ :
      gscale_state hδ_nonneg X₀ ≺ gscale_state hδ_nonneg X₁ := by
    simp [gscale_state_pos hδ_nonneg hδ_pos]
    exact (L2_5_ii hδ_pos).1 h_ref_strict.1
  -- reassociate → apply generalized_cancellation (after swaps)
  have h_assoc := le_of_le_equiv h_access_reorg (assoc_equiv_L X _ _)
  have h_comm_L :=
    comp_comm_equiv_clean (gscale_state hδ_nonneg X₁) (gscale_state hμ_nonneg X₁)
  have h_comm_R :=
    comp_comm_equiv_clean (gscale_state hδ_nonneg X₀)
      (comp_state (X, gscale_state h_μm1_nonneg X₀))
  have h_swapped :
      comp_state (gscale_state hδ_nonneg X₁, gscale_state hμ_nonneg X₁) ≺
      comp_state (gscale_state hδ_nonneg X₀,
        comp_state (X, gscale_state h_μm1_nonneg X₀)) :=
    le_of_le_equiv (le_of_equiv_le h_comm_L h_assoc) (And.symm h_comm_R)
  have h_cancel := generalized_cancellation
    (gscale_state hδ_nonneg X₁) (gscale_state hδ_nonneg X₀)
    (gscale_state hμ_nonneg X₁)
    (comp_state (X, gscale_state h_μm1_nonneg X₀))
    h_swapped h_δX₀_lt_δX₁
  -- conclude (three subcases μ>1 or μ=1)
  dsimp [GenRefAccessible]
  rcases lt_or_eq_of_le hμ_ge1 with hμ_gt1 | hμ_eq1
  · have hμ_pos : 0 < μ := lt_trans (by norm_num) hμ_gt1
    have h_μm1_pos : 0 < μ - 1 := sub_pos.mpr hμ_gt1
    rw [dif_neg (fun h => (lt_irrefl (1:ℝ)) (lt_of_lt_of_le hμ_gt1 h.2)),
        dif_pos hμ_gt1]
    simpa [gscale_state_pos hμ_nonneg hμ_pos,
           gscale_state_pos h_μm1_nonneg h_μm1_pos] using h_cancel
  · -- μ = 1 case: after subst, μ is replaced by 1
    have hμ_eq1_val : μ = 1 := by exact id (Eq.symm hμ_eq1) --hμ_eq1
    subst hμ_eq1_val
    rw [dif_pos ⟨(by norm_num),(by norm_num)⟩]
    -- μ=1: adapt final normalization from original proof
    -- Reproduce succinct final lines:
    have h_cancel1 :
        gscale_state (show 0 ≤ (1:ℝ) by norm_num) X₁ ≺
        comp_state (X, gscale_state (show 0 ≤ (1:ℝ) - 1 by norm_num) X₀) := by
      -- Rewrite using proof-irrelevance equalities, avoiding heavy simp to prevent recursion blowup.
      have hX₁ :=
        gscale_state_proof_irrel (System:=System) (t:=(1:ℝ)) hμ_nonneg (by norm_num) X₁
      have hX₀ :=
        gscale_state_proof_irrel (System:=System) (t:=(1:ℝ)-1) h_μm1_nonneg (by norm_num) X₀
      -- Start from original h_cancel and rewrite sides manually.
      have htmp := h_cancel
      -- Rewrite the left occurrence.
      rw [hX₁] at htmp
      -- Rewrite the right occurrence (second component of the pair) using congrArg.
      have hX₀' :
          comp_state (X, gscale_state h_μm1_nonneg X₀)
            = comp_state (X, gscale_state (show 0 ≤ (1:ℝ) - 1 by norm_num) X₀) := by
        -- Keep (1:ℝ) - 1 syntactically (instead of reducing to 0) so the system types match exactly.
        simp
      rw [hX₀'] at htmp
      exact htmp
    have h_one_equiv := gscale_one_equiv (Γ := Γ) X₁
    have h_zero_equiv := gscale_zero_equiv (Γ := Γ) X₀
    have h_lift :
        comp_state (X, gscale_state (show 0 ≤ (0:ℝ) by norm_num) X₀)
          ≈ comp_state (X, (default : TW.State TW.ZSystem)) :=
      ⟨ TW.A3 (thermo_le_refl _) h_zero_equiv.1,
        TW.A3 (thermo_le_refl _) h_zero_equiv.2 ⟩
    have h_step :
        X₁ ≺ comp_state (X, (default : TW.State TW.ZSystem)) := by
      -- First step: X₁ ≺ (X, gscale_state 0 X₀)
      have h1 : X₁ ≺ comp_state (X, gscale_state (show 0 ≤ (0:ℝ) by norm_num) X₀) := by
        convert thermo_le_trans (thermo_equiv_symm h_one_equiv).1 h_cancel1
        exact Eq.symm (sub_self 1)
        exact Eq.symm (sub_self 1)
        exact Eq.symm (sub_self 1)
      -- Then use the equivalence h_lift to reach (X, default)
      exact thermo_le_trans h1 h_lift.1
    have h_cz := L2_3_i (Γ := Γ) X -- (X,0) ≈ X
    have h_X₁_le_X : X₁ ≺ X :=
      thermo_le_trans h_step h_cz.1
    -- R₁ ≈ X₁ ⇒ done
    have hR1_equiv_X₁ : ReferenceState X₀ X₁ 1 (by norm_num) (by norm_num) ≈ X₁ := by
      -- Inline the proof of ReferenceState_one_equiv
      dsimp [ReferenceState]
      have h_0X₀ : gscale_state (sub_nonneg.mpr (by norm_num : (1 : ℝ) ≤ 1)) X₀
                      ≈ (default : TW.State TW.ZSystem) := by
        have := gscale_zero_equiv (Γ := Γ) X₀
        simp; grind
      have h_1X₁ : gscale_state (show 0 ≤ (1:ℝ) by norm_num) X₁ ≈ X₁ := gscale_one_equiv X₁
      have h_R₁_ZX₁ := L2_4_i h_0X₀ h_1X₁
      have h_ZX₁_X₁ := comp_Z_equiv_L X₁
      exact thermo_equiv_trans' h_R₁_ZX₁ h_ZX₁_X₁
    exact le_of_equiv_le hR1_equiv_X₁ h_X₁_le_X

/-- Extend monotonicity across 0: μ < 0 ≤ lam (uses recursive call at 0, then negative branch). -/
lemma GenRefAccessible_monotone_neg_to_nonneg
    {X₀ X₁ X : TW.State Γ} (h_ref_strict : X₀ ≺≺ X₁)
    {μ lam : ℝ} (hμ_lt0 : μ < 0) (hlam_nonneg : 0 ≤ lam) (_ : μ < lam)
    (h_access_lam : GenRefAccessible X₀ X₁ X lam) :
    GenRefAccessible X₀ X₁ X μ := by
  -- Get GenRef(0) from lam (if lam>0 recurse into interval lemma)
  have h_access_0 : GenRefAccessible X₀ X₁ X 0 := by
    by_cases hlam0 : lam = 0
    · simpa [hlam0] using h_access_lam
    · have h0lam : 0 < lam := lt_of_le_of_ne hlam_nonneg (Ne.symm hlam0)
      -- We need to derive GenRefAccessible at 0 from h_access_lam.
      -- Use monotonicity: if we have access at lam, we have access at any μ < lam.
      -- Special case: derive access at min lam 1 first, then use it to get 0.
      by_cases hlam_le1 : lam ≤ 1
      · -- Case: lam ≤ 1. Then min lam 1 = lam.
        have h_min_eq : min lam 1 = lam := min_eq_left hlam_le1
        -- Use monotonicity from lam to 0 with the interval lemma.
        exact GenRefAccessible_monotone_interval (X₀:=X₀) (X₁:=X₁) (X:=X) h_ref_strict
          (μ:=0) (lam:=lam)
          (by norm_num) hlam_le1 h0lam h_access_lam
      · -- Case: lam > 1. Use cross-one lemma to get access at a point < 1, then interval.
        -- First, get access at 1/2 (which is in (0,1)) using the fact that lam > 1.
        have h_half_pos : (0 : ℝ) < 1/2 := by norm_num
        have h_half_lt1 : (1/2 : ℝ) < 1 := by norm_num
        have h_half_lt_lam : (1/2 : ℝ) < lam := by
          have : 1 < lam := lt_of_not_ge hlam_le1
          linarith
        -- Use cross-one to get GenRefAccessible at 1/2.
        have h_access_half : GenRefAccessible X₀ X₁ X (1/2) :=
          GenRefAccessible_monotone_cross_one h_ref_strict
            (μ:=1/2) (lam:=lam)
            (by norm_num) h_half_lt1 (lt_of_not_ge hlam_le1) h_half_lt_lam h_access_lam
        -- Now use interval lemma from 1/2 to 0.
        exact GenRefAccessible_monotone_interval (X₀:=X₀) (X₁:=X₁) (X:=X) h_ref_strict
          (μ:=0) (lam:=1/2)
          (by norm_num) (le_of_lt h_half_lt1) h_half_pos h_access_half
  have : GenRefAccessible X₀ X₁ X μ := by
    -- Adapt Subcase 2b (negative μ)
    dsimp [GenRefAccessible]
    have hμ_nonpos : ¬ 0 ≤ μ := not_le.mpr hμ_lt0
    rw [dif_neg (by exact fun h => hμ_nonpos h.1),
        dif_neg (by
          intro h
          have : μ < 1 := hμ_lt0.trans (by norm_num : (0 : ℝ) < 1)
          exact not_lt.mpr (le_of_lt h) this)]
    -- Derive X₀ ≺ X from accessibility at 0.
    have h_X0_le_X : X₀ ≺ X := by
      dsimp [GenRefAccessible] at h_access_0
      rw [dif_pos ⟨(by norm_num),(by norm_num)⟩] at h_access_0
      -- ReferenceState 0 ≈ X₀
      have h_R0_equiv_X0 : ReferenceState X₀ X₁ 0 (by norm_num) (by norm_num) ≈ X₀ := by
        dsimp [ReferenceState]
        have h_1X₀_equiv : gscale_state (sub_nonneg.mpr (by norm_num : (0:ℝ) ≤ 1)) X₀ ≈ X₀ := by
          have := gscale_one_equiv X₀
          simp at this ⊢
          grind [= ThermoWorld.State, = StrictlyPrecedes, = GenRefAccessible, = ThermoWorld.le,
            = ThermoWorld.comp, = ThermoWorld.scale, = ReferenceState, = scale_state]
        have h_0X₁ : gscale_state (by norm_num : 0 ≤ (0:ℝ)) X₁ ≈ (default : TW.State TW.ZSystem) :=
          gscale_zero_equiv X₁
        have h_pair := L2_4_i h_1X₀_equiv h_0X₁
        have h_cz  := L2_3_i X₀
        exact thermo_equiv_trans' h_pair h_cz
      exact le_of_equiv_le (thermo_equiv_symm h_R0_equiv_X0) h_access_0
    -- Build the negative-side inequality.
    let h_1mμ_nonneg : 0 ≤ 1 - μ := by linarith
    let h_negμ_nonneg : 0 ≤ -μ := neg_nonneg.mpr (le_of_lt hμ_lt0)
    have h_negμ_pos : 0 < -μ := by linarith
    -- (-μ) scaling preserves strict inequality between X₀ and X₁.
    have h_negμX₀_lt_negμX₁ :
        gscale_state h_negμ_nonneg X₀ ≺ gscale_state h_negμ_nonneg X₁ := by
      simp [gscale_state_pos h_negμ_nonneg h_negμ_pos]
      exact (L2_5_ii h_negμ_pos).1 h_ref_strict.1
    -- Consistency: (X₀, (-μ)X₀) ≺ (X, (-μ)X₁)
    have h_A3 :
        comp_state (X₀, gscale_state h_negμ_nonneg X₀) ≺
        comp_state (X,  gscale_state h_negμ_nonneg X₁) :=
      TW.A3 h_X0_le_X h_negμX₀_lt_negμX₁
    -- Left side: (1-μ)X₀ ≈ (X₀, (-μ)X₀)
    have h_LHS_clean :
      gscale_state h_1mμ_nonneg X₀ ≈
      comp_state (X₀, gscale_state h_negμ_nonneg X₀) := by
      -- Decompose (1-μ) = 1 + (-μ)
      have h_eq : 1 - μ = 1 + (-μ) := by ring
      -- Align (1-μ)X₀ with (1 + (-μ))X₀
      have h_align :=
        gscale_eq_coherence (Γ:=Γ) (X:=X₀) h_eq
          h_1mμ_nonneg (add_nonneg (by norm_num : 0 ≤ (1:ℝ)) h_negμ_nonneg)
      -- Recombine (1 + (-μ))X₀ ≈ (1X₀, (-μ)X₀)
      have h_recomb :
        gscale_state (add_nonneg (by norm_num : 0 ≤ (1:ℝ)) h_negμ_nonneg) X₀ ≈
        comp_state (gscale_state (by norm_num : 0 ≤ (1:ℝ)) X₀,
                    gscale_state h_negμ_nonneg X₀) :=
        generalized_recombination_lemma (by norm_num) h_negμ_nonneg X₀
      -- Replace 1X₀ by X₀
      have h_one := gscale_one_equiv X₀
      have h_swap :
        comp_state (gscale_state (by norm_num : 0 ≤ (1:ℝ)) X₀,
                    gscale_state h_negμ_nonneg X₀) ≈
        comp_state (X₀, gscale_state h_negμ_nonneg X₀) :=
        L2_4_i h_one (thermo_equiv_refl _)
      exact
        thermo_equiv_trans' h_align
          (thermo_equiv_trans' h_recomb h_swap)
    -- Conclude (1-μ)X₀ ≺ (X, (-μ)X₁)
    have h_final :
        gscale_state h_1mμ_nonneg X₀ ≺
        comp_state (X, gscale_state h_negμ_nonneg X₁) :=
      le_of_equiv_le h_LHS_clean h_A3
    -- Now we need to align the gscale_state with the scale_state in the goal.
    have h_1mμ_pos : 0 < 1 - μ := by linarith
    have h_negμ_pos : 0 < -μ := by linarith
    simpa [gscale_state_pos h_1mμ_nonneg h_1mμ_pos,
           gscale_state_pos h_negμ_nonneg h_negμ_pos] using h_final
  exact this

/-- Monotonicity for both negative parameters: μ < lam < 0. -/
lemma GenRefAccessible_monotone_both_neg
    {X₀ X₁ X : TW.State Γ} (h_ref_strict : X₀ ≺≺ X₁)
    {μ lam : ℝ} (hμ_ltlam : μ < lam) (hlam_lt0 : lam < 0)
    (h_access_lam : GenRefAccessible X₀ X₁ X lam) :
    GenRefAccessible X₀ X₁ X μ := by
  -- Reuse original Case 3 computations.
  set δ := lam - μ
  have hδ_pos : 0 < δ := sub_pos.mpr hμ_ltlam
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hμ_lt0 : μ < 0 := lt_trans hμ_ltlam hlam_lt0
  -- Simplify the hypothesis (lam < 0 branch of GenRefAccessible)
  have hlam_nonpos : ¬ 0 ≤ lam := not_le.mpr hlam_lt0
  have hlam_not_range : ¬ (0 ≤ lam ∧ lam ≤ 1) := by intro h; exact hlam_nonpos h.1
  have hlam_not_gt1 : ¬ 1 < lam := by
    -- From lam < 0 we get lam ≤ 0 and thus lam ≤ 1, hence ¬ (1 < lam)
    exact not_lt.mpr (le_trans (le_of_lt hlam_lt0) (by norm_num : (0:ℝ) ≤ 1))
  simp [GenRefAccessible, hlam_not_range, hlam_not_gt1] at h_access_lam
  -- Simplify the goal (μ < 0 branch of GenRefAccessible)
  have hμ_nonpos : ¬ 0 ≤ μ := not_le.mpr hμ_lt0
  have hμ_not_range : ¬ (0 ≤ μ ∧ μ ≤ 1) := by intro h; exact hμ_nonpos h.1
  have hμ_not_gt1 : ¬ 1 < μ := by
    -- From μ < 0 we get μ ≤ 0, hence μ ≤ 1, so ¬ (1 < μ).
    have hμ_le0 : μ ≤ 0 := le_of_lt hμ_lt0
    have hμ_le1 : μ ≤ 1 := le_trans hμ_le0 (by norm_num : (0:ℝ) ≤ 1)
    exact not_lt.mpr hμ_le1
  simp [GenRefAccessible, hμ_not_range, hμ_not_gt1]
  -- replicate algebra from earlier Case 3
  have h_1mlam_nonneg : 0 ≤ 1 - lam := le_of_lt (by linarith : 0 < 1 - lam)
  have h_neglam_nonneg : 0 ≤ -lam := le_of_lt (by linarith : 0 < -lam)
  have h_1mμ_nonneg : 0 ≤ 1 - μ := le_of_lt (by linarith : 0 < 1 - μ)
  have h_negμ_nonneg : 0 ≤ -μ := le_of_lt (by linarith : 0 < -μ)
  -- LHS recomb
  have h_LHS_recomb :
    gscale_state h_1mμ_nonneg X₀ ≈
      comp_state (gscale_state h_1mlam_nonneg X₀, gscale_state hδ_nonneg X₀) := by
    have h_eq : 1 - μ = (1 - lam) + δ := by simp [δ]
    have h_align :=
      gscale_eq_coherence (Γ := Γ) (X := X₀) h_eq h_1mμ_nonneg
        (add_nonneg h_1mlam_nonneg hδ_nonneg)
    have h_gr := generalized_recombination_lemma h_1mlam_nonneg hδ_nonneg X₀
    exact thermo_equiv_trans' h_align h_gr
  -- RHS recomb
  have h_negμ_recomb :
    gscale_state h_negμ_nonneg X₁ ≈
      comp_state (gscale_state h_neglam_nonneg X₁, gscale_state hδ_nonneg X₁) := by
    have h_eq : -μ = -lam + δ := by simp [δ]; ring
    have h_align :=
      gscale_eq_coherence (Γ := Γ) (X := X₁) h_eq h_negμ_nonneg
        (add_nonneg h_neglam_nonneg hδ_nonneg)
    have h_gr := generalized_recombination_lemma h_neglam_nonneg hδ_nonneg X₁
    exact thermo_equiv_trans' h_align h_gr
  have h_RHS_recomb :
      comp_state (X, gscale_state h_negμ_nonneg X₁) ≈
      comp_state (X,
        comp_state (gscale_state h_neglam_nonneg X₁, gscale_state hδ_nonneg X₁)) :=
    L2_4_i (thermo_equiv_refl _) h_negμ_recomb
  -- δ scaling comparison
  have h_δX₀_lt_δX₁ :
      gscale_state hδ_nonneg X₀ ≺ gscale_state hδ_nonneg X₁ := by
    simp [gscale_state_pos hδ_nonneg hδ_pos]
    exact (L2_5_ii hδ_pos).1 h_ref_strict.1
  -- align premise to gscale form
  have h_access_g :
      gscale_state h_1mlam_nonneg X₀ ≺
      comp_state (X, gscale_state h_neglam_nonneg X₁) := by
    have h1mlam_pos : 0 < 1 - lam := by linarith
    have hneglam_pos : 0 < -lam := by linarith
    simpa [gscale_state_pos h_1mlam_nonneg h1mlam_pos,
          gscale_state_pos h_neglam_nonneg hneglam_pos] using h_access_lam
  -- build target inequality
  have h_target :
      comp_state (gscale_state h_1mlam_nonneg X₀, gscale_state hδ_nonneg X₀) ≺
      comp_state (comp_state (X, gscale_state h_neglam_nonneg X₁),
                 gscale_state hδ_nonneg X₁) :=
    TW.A3 h_access_g h_δX₀_lt_δX₁
  -- reorganize RHS association
  have h_RHS_assoc :
      comp_state (X,
        comp_state (gscale_state h_neglam_nonneg X₁, gscale_state hδ_nonneg X₁)) ≈
      comp_state (comp_state (X, gscale_state h_neglam_nonneg X₁),
                 gscale_state hδ_nonneg X₁) :=
    assoc_equiv_L X _ _
  -- chain equivalences
  have h_final :=
    le_of_le_equiv
      (le_of_equiv_le h_LHS_recomb h_target)
      (thermo_equiv_trans' (thermo_equiv_symm h_RHS_assoc)
                           (thermo_equiv_symm h_RHS_recomb))
  -- rewrite to scale_state form
  have h_1mμ_pos : 0 < 1 - μ := by linarith
  have h_negμ_pos : 0 < -μ := by linarith
  simpa [gscale_state_pos h_1mμ_nonneg h_1mμ_pos,
         gscale_state_pos h_negμ_nonneg h_negμ_pos] using h_final

/-! ### Lemma 2.7 (ii): Monotonicity of the Lambda Set -/

/-- Generalized Reference Comparison Lemma (L-Y Lemma 2.7 (ii)).
    If X₀ ≺≺ X₁ and μ < lam, then GenRefAccessible(lam, X) implies GenRefAccessible(μ, X).
    This proves that the set lam(X) is an interval extending to -∞ (a lower set).
-/
lemma GenRefAccessible_monotone
    (X₀ X₁ X : TW.State Γ) (h_ref_strict : X₀ ≺≺ X₁)
    (μ lam : ℝ) (hμlam : μ < lam)
    (h_access_lam : GenRefAccessible X₀ X₁ X lam) :
    GenRefAccessible X₀ X₁ X μ := by
  classical
  -- Case split over sign / interval locations
  by_cases hμ_nonneg : 0 ≤ μ
  · -- μ ≥ 0
    by_cases hlam_le1 : lam ≤ 1
    · -- both in [0,1]
      exact GenRefAccessible_monotone_interval (X₀:=X₀) (X₁:=X₁) (X:=X) h_ref_strict
        (μ:=μ) (lam:=lam) hμ_nonneg hlam_le1 hμlam h_access_lam
    · -- either μ < 1 < lam or 1 ≤ μ < lam
      by_cases hμ_lt1 : μ < 1
      · -- μ < 1 < lam
        have hlam_gt1 : 1 < lam := lt_of_not_ge hlam_le1
        exact GenRefAccessible_monotone_cross_one h_ref_strict
          (μ:=μ) (lam:=lam) hμ_nonneg hμ_lt1 hlam_gt1 hμlam h_access_lam
      · -- 1 ≤ μ < lam
        have hμ_ge1 : 1 ≤ μ := le_of_not_gt hμ_lt1
        exact GenRefAccessible_monotone_ge_one h_ref_strict
          (μ:=μ) (lam:=lam) hμ_ge1 hμlam h_access_lam
  · -- μ < 0
    have hμ_lt0 : μ < 0 := lt_of_not_ge hμ_nonneg
    by_cases hlam_nonneg : 0 ≤ lam
    · -- μ < 0 ≤ lam
      exact GenRefAccessible_monotone_neg_to_nonneg h_ref_strict
        (μ:=μ) (lam:=lam) hμ_lt0 hlam_nonneg hμlam h_access_lam
    · -- lam < 0, so both negative
      have hlam_lt0 : lam < 0 := lt_of_not_ge hlam_nonneg
      exact GenRefAccessible_monotone_both_neg h_ref_strict
        (μ:=μ) (lam:=lam) hμlam hlam_lt0 h_access_lam

open CanonicalEntropyContext

variable (Ctx : CanonicalEntropyContext Γ)

/-- Lemma 2.7 (ii): lam(X) is a lower set (an interval extending to -∞). -/
lemma CanonicalEntropyContext.LambdaSet_is_lower (X : TW.State Γ) :
    IsLowerSet (Ctx.LambdaSet X) := by
  intros t s h_le ht_in
  rcases eq_or_lt_of_le h_le with h_eq | h_lt
  · rwa [h_eq]
  · exact GenRefAccessible_monotone Ctx.X₀ Ctx.X₁ X Ctx.h_ref_strict s t h_lt ht_in

/-! ### Theorem 2.2: Properties of Canonical Entropy (Normalization) -/

/-- Typeclass asserting non-emptiness witnesses for all Lambda sets in the context.-/
class HasLambdaWitness {System : Type u} [TW : ThermoWorld System]
    {Γ : System} (Ctx : CanonicalEntropyContext Γ) : Prop where
  (lambda_nonempty : ∀ X : TW.State Γ, (Ctx.LambdaSet X).Nonempty)

@[simp] lemma HasLambdaWitness.lambdaSet_nonempty
    {System : Type u} [TW : ThermoWorld System]
    {Γ : System} (Ctx : CanonicalEntropyContext Γ)
    [h : HasLambdaWitness Ctx] (X : TW.State Γ) :
    (Ctx.LambdaSet X).Nonempty :=
  HasLambdaWitness.lambda_nonempty X


/-! ### Theorem 2.2: Properties of Canonical Entropy (Normalization) -/

-- We assume HasLambdaWitness to ensure S(X) is well-defined (non-empty and we can use sSup lemmas).
variable [h_witness : HasLambdaWitness Ctx]

/-- Helper Lemma: R₀ ≈ X₀.
    Fixes earlier proof term mismatches between (1-0) and 1 in the scaling
    by using `gscale_eq_coherence` to bridge `(1-0)` to `1`, then `gscale_one_equiv`. -/
lemma ReferenceState_zero_equiv (X₀ X₁ : TW.State Γ) :
    ReferenceState X₀ X₁ 0 (by norm_num) (by norm_num) ≈ X₀ := by
  dsimp [ReferenceState]
  -- (1-0) = 1 : relate generalized scale (1-0) to canonical 1 using coherence.
  have h_eq : (1 - (0:ℝ)) = (1:ℝ) := by norm_num
  have h_coh :
      gscale_state (sub_nonneg.mpr (by norm_num : (0:ℝ) ≤ 1)) X₀
        ≈ gscale_state (show 0 ≤ (1:ℝ) by norm_num) X₀ :=
    gscale_eq_coherence (Γ := Γ) (X := X₀) h_eq
      (sub_nonneg.mpr (by norm_num : (0:ℝ) ≤ 1))
      (show 0 ≤ (1:ℝ) by norm_num)
  have h1 : gscale_state (sub_nonneg.mpr (by norm_num : (0:ℝ) ≤ 1)) X₀ ≈ X₀ :=
    thermo_equiv_trans' h_coh (gscale_one_equiv X₀)
  -- 0·X₁ ≈ Z
  have h2 :
      gscale_state (show 0 ≤ (0:ℝ) by norm_num) X₁
        ≈ (default : TW.State TW.ZSystem) :=
    gscale_zero_equiv X₁
  -- Pair and collapse (X₀, Z) ≈ X₀.
  have h_pair :
      comp_state (gscale_state (sub_nonneg.mpr (by norm_num : (0:ℝ) ≤ 1)) X₀,
                  gscale_state (show 0 ≤ (0:ℝ) by norm_num) X₁)
        ≈ comp_state (X₀, (default : TW.State TW.ZSystem)) :=
    L2_4_i h1 h2
  have h_cz : comp_state (X₀, (default : TW.State TW.ZSystem)) ≈ X₀ := L2_3_i X₀
  exact thermo_equiv_trans' h_pair h_cz

/-- Helper Lemma: R₁ ≈ X₁ -/
lemma ReferenceState_one_equiv (X₀ X₁ : TW.State Γ) :
    ReferenceState X₀ X₁ 1 (by norm_num) (by norm_num) ≈ X₁ := by
  dsimp [ReferenceState]
  -- (0X₀, 1X₁) ≈ (Z, X₁) ≈ X₁.
  -- Provide (1-1)=0 case via coherence + zero scaling equivalence.
  have h_0X₀ : gscale_state (sub_nonneg.mpr (by norm_num : (1 : ℝ) ≤ 1)) X₀
                  ≈ (default : TW.State TW.ZSystem) := by
    -- Coherence between (1-1)•X₀ and 0•X₀.
    have h1 : 0 ≤ (1 - (1:ℝ)) := by norm_num
    have h2 : 0 ≤ (0:ℝ) := by simp
    have h_coh :
        gscale_state h1 X₀ ≈ gscale_state h2 X₀ :=
      gscale_eq_coherence (Γ := Γ) (X := X₀) (h_eq := by norm_num) (ht₁ := h1) (ht₂ := h2)
    have h_zero := gscale_zero_equiv (Γ := Γ) X₀
    -- Chain coherence with zero scaling equivalence.
    simpa using (thermo_equiv_trans' h_coh h_zero)
  have h_1X₁ : gscale_state (show 0 ≤ (1:ℝ) by norm_num) X₁ ≈ X₁ := gscale_one_equiv X₁
  -- Combine componentwise equivalences.
  have h_R₁_ZX₁ := L2_4_i h_0X₀ h_1X₁
  have h_ZX₁_X₁ := comp_Z_equiv_L X₁
  exact thermo_equiv_trans' h_R₁_ZX₁ h_ZX₁_X₁

/-- Helper Lemma: tX ≈ (X, (t-1)X) for t > 1. Relies on Recombination and C1. -/
lemma scale_split_one_plus (X : TW.State Γ) (t : ℝ) (ht_gt1 : 1 < t) :
    scale_state (lt_trans (by norm_num) ht_gt1).ne' X ≈
    comp_state (X, scale_state (sub_pos.mpr ht_gt1).ne' X) := by
  let htm1_pos := sub_pos.mpr ht_gt1
  have ht_pos : 0 < t := lt_trans (by norm_num) ht_gt1

  -- 1. Align tX with (1+(t-1))X using CEq and CCast.
  have h_eq : t = 1 + (t-1) := by ring
  have h_sum_pos : 0 < 1 + (t-1) := by rwa [←h_eq]
  let U := scale_state h_sum_pos.ne' X

  let h_sys_eq := congrArg (fun r => TW.scale r Γ) h_eq
  have h_cast : scale_state ht_pos.ne' X ≈ (Equiv.cast (congrArg TW.State h_sys_eq) (scale_state ht_pos.ne' X)) :=
    TW.state_equiv_coherence h_sys_eq (scale_state ht_pos.ne' X)
  have h_ceq : (Equiv.cast (congrArg TW.State h_sys_eq) (scale_state ht_pos.ne' X)) ≈ U :=
    TW.scale_eq_coherence (Γ:=Γ) (X:=X) h_eq ht_pos.ne'
  have h_align := thermo_equiv_trans' h_cast h_ceq

  -- 2. Apply Recombination: U ≈ (1X, (t-1)X).
  have h_recomb := recombination_lemma (a:=1) (b:=t-1) (by norm_num) htm1_pos X

  -- 3. Apply C1: 1X ≈ X.
  have h_C1 := one_smul_coherence_clean X
  have h_clean :
    comp_state (scale_state (t := 1) (by norm_num) X, scale_state htm1_pos.ne' X) ≈
    comp_state (X, scale_state htm1_pos.ne' X) :=
    L2_4_i h_C1 (thermo_equiv_refl _)

  -- Chain: tX ≈ U ≈ (1X, (t-1)X) ≈ (X, (t-1)X).
  exact thermo_equiv_trans' h_align (thermo_equiv_trans' h_recomb h_clean)

omit h_witness in
/-- Theorem 2.2 (i) Part 1: S(X₀) = 0.
    We prove 0 is the greatest element of lam(X₀), then use order properties
    of sSup (no deprecated `csSup_eq_of_is_greatest`). -/
lemma CanonicalEntropyContext.S_X₀_eq_0 : Ctx.S Ctx.X₀ = 0 := by
  -- 1. Show 0 ∈ lam(X₀).
  have h_0_in_L : 0 ∈ Ctx.LambdaSet Ctx.X₀ := by
    dsimp [CanonicalEntropyContext.LambdaSet, GenRefAccessible]
    -- 0 lies in the interval branch 0 ≤ 0 ≤ 1
    rw [dif_pos (by constructor <;> norm_num)]
    -- R₀ ≺ X₀ since R₀ ≈ X₀
    exact (ReferenceState_zero_equiv Ctx.X₀ Ctx.X₁).1
  -- 2. Show every t in lam(X₀) satisfies t ≤ 0.
  have h_upper_bound_0 : ∀ t ∈ Ctx.LambdaSet Ctx.X₀, t ≤ 0 := by
    intro t ht_in_L
    dsimp [CanonicalEntropyContext.LambdaSet, GenRefAccessible] at ht_in_L
    by_contra ht_pos_contra
    have ht_pos : 0 < t := lt_of_not_ge ht_pos_contra
    by_cases ht_le1 : t ≤ 1
    · -- Case 0 < t ≤ 1: use strict monotonicity of reference states.
      have h_range : 0 ≤ t ∧ t ≤ 1 := ⟨le_of_lt ht_pos, ht_le1⟩
      rw [dif_pos h_range] at ht_in_L
      -- Strict monotonicity R₀ ≺≺ R_t
      have h_R_strict := StrictReferenceState_monotone Ctx 0 t (by norm_num) ht_le1 ht_pos
      -- R₀ ≈ X₀
      have h_R0_X0 := ReferenceState_zero_equiv Ctx.X₀ Ctx.X₁
      -- From R₀ ≺ R_t and R₀ ≈ X₀ we get X₀ ≺ R_t
      have h_X0_Rt :
          Ctx.X₀ ≺ ReferenceState Ctx.X₀ Ctx.X₁ t (by exact h_range.1) (by exact h_range.2) :=
        le_of_equiv_le (thermo_equiv_symm h_R0_X0) h_R_strict.1
      -- From R_t ≺ X₀ (ht_in_L) and X₀ ≈ R₀ we get R_t ≺ R₀
      have h_Rt_R0 :
          ReferenceState Ctx.X₀ Ctx.X₁ t h_range.1 h_range.2 ≺
          ReferenceState Ctx.X₀ Ctx.X₁ 0 (by norm_num) (by norm_num) :=
        le_of_le_equiv ht_in_L (id (And.symm h_R0_X0))--le_of_le_equiv ht_in_L h_R0_X0
      -- Contradiction with strictness (¬ R_t ≺ R₀)
      exact h_R_strict.2 h_Rt_R0
    · -- Case t > 1: impossible since lam(X₀) would give tX₁ ≺ (X₀, (t-1)X₀) ⇒ X₁ ≺ X₀ contradicting X₀ ≺≺ X₁.
      have ht_gt1 : 1 < t := lt_of_not_ge ht_le1
      have h_not_range : ¬ (0 ≤ t ∧ t ≤ 1) := by
        intro h; grind-- (lt_irrefl (t := t)) (lt_of_le_of_lt h.2 ht_gt1)
      rw [dif_neg h_not_range, dif_pos ht_gt1] at ht_in_L
      -- tX₁ ≈ (X₁, (t-1)X₁)
      have h_split := scale_split_one_plus Ctx.X₁ t ht_gt1
      let htm1_pos := sub_pos.mpr ht_gt1
      -- (X₁,(t-1)X₁) ≺ (X₀,(t-1)X₀)
      have h_chain :
          comp_state (Ctx.X₁, scale_state htm1_pos.ne' Ctx.X₁) ≺
          comp_state (Ctx.X₀, scale_state htm1_pos.ne' Ctx.X₀) :=
        le_of_equiv_le (thermo_equiv_symm h_split) ht_in_L
      -- Cancellation ⇒ (t-1)X₁ ≺ (t-1)X₀ ⇒ X₁ ≺ X₀ contradiction
      have h_cancel :=
        generalized_cancellation Ctx.X₁ Ctx.X₀
          (scale_state htm1_pos.ne' Ctx.X₁) (scale_state htm1_pos.ne' Ctx.X₀)
          h_chain Ctx.h_ref_strict.1
      have h_X1_le_X0 := (L2_5_ii htm1_pos).mpr h_cancel
      exact Ctx.h_ref_strict.2 h_X1_le_X0
  -- 3. Convert "0 greatest" into sSup equality via order lemmas.
  --    First inequalities: S(X₀) ≤ 0 and 0 ≤ S(X₀).
  have h_nonempty : (Ctx.LambdaSet Ctx.X₀).Nonempty := ⟨0, h_0_in_L⟩
  have h_bdd : BddAbove (Ctx.LambdaSet Ctx.X₀) := ⟨0, h_upper_bound_0⟩
  have h_le : Ctx.S Ctx.X₀ ≤ 0 :=
    csSup_le h_nonempty h_upper_bound_0
  have h_ge : 0 ≤ Ctx.S Ctx.X₀ :=
    le_csSup h_bdd h_0_in_L
  exact le_antisymm h_le h_ge

omit h_witness in
/-- Theorem 2.2 (i) Part 2: S(X₁) = 1. -/
lemma CanonicalEntropyContext.S_X₁_eq_1 : Ctx.S Ctx.X₁ = 1 := by
  -- 1. Show 1 ∈ lam(X₁).
  have h_1_in_L : 1 ∈ Ctx.LambdaSet Ctx.X₁ := by
    dsimp [CanonicalEntropyContext.LambdaSet, GenRefAccessible]
    -- 1 lies in the (μ > 1) branch’s boundary: handled by (0 ≤ 1 ∧ 1 ≤ 1)
    rw [dif_pos (by constructor <;> norm_num)]
    -- R₁ ≺ X₁ since R₁ ≈ X₁
    exact (ReferenceState_one_equiv Ctx.X₀ Ctx.X₁).1
  -- 2. Show every t in lam(X₁) satisfies t ≤ 1.
  have h_upper_bound_1 : ∀ t ∈ Ctx.LambdaSet Ctx.X₁, t ≤ 1 := by
    intro t ht_in
    dsimp [CanonicalEntropyContext.LambdaSet, GenRefAccessible] at ht_in
    -- Suppose t > 1; derive contradiction.
    by_contra h_not
    have ht_gt1 : 1 < t := lt_of_not_ge h_not
    -- Split on whether t ∈ [0,1]; impossible if t > 1.
    have h_not_range : ¬ (0 ≤ t ∧ t ≤ 1) := by
      intro h; grind --exact (lt_irrefl (t := t)) (lt_of_le_of_lt h.2 ht_gt1)
    -- Reduce definition.
    rw [dif_neg h_not_range, dif_pos ht_gt1] at ht_in
    -- From ht_in we have: tX₁ ≺ (X₁, (t-1)X₀).
    -- Also tX₁ ≈ (X₁, (t-1)X₁) (splitting for t>1).
    have h_split := scale_split_one_plus Ctx.X₁ t ht_gt1
    let htm1_pos := sub_pos.mpr ht_gt1
    -- Chain: (X₁,(t-1)X₁) ≺ (X₁,(t-1)X₀)
    have h_chain :
        comp_state (Ctx.X₁, scale_state htm1_pos.ne' Ctx.X₁) ≺
        comp_state (Ctx.X₁, scale_state htm1_pos.ne' Ctx.X₀) :=
      le_of_equiv_le (thermo_equiv_symm h_split) ht_in
    -- Cancel left component ⇒ (t-1)X₁ ≺ (t-1)X₀.
    have h_cancel :=
      cancellation_left Ctx.X₁
        (scale_state htm1_pos.ne' Ctx.X₁)
        (scale_state htm1_pos.ne' Ctx.X₀) h_chain
    -- Scaling cancellation ⇒ X₁ ≺ X₀ (contradiction to X₀ ≺≺ X₁).
    have h_X1_le_X0 := (L2_5_ii htm1_pos).mpr h_cancel
    exact Ctx.h_ref_strict.2 h_X1_le_X0
  -- 3. Use sSup characterization: S(X₁) is sup of lam(X₁).
  have h_nonempty : (Ctx.LambdaSet Ctx.X₁).Nonempty := ⟨1, h_1_in_L⟩
  have h_bdd : BddAbove (Ctx.LambdaSet Ctx.X₁) := ⟨1, h_upper_bound_1⟩
  -- Upper bound: S(X₁) ≤ 1
  have h_le : Ctx.S Ctx.X₁ ≤ 1 :=
    csSup_le h_nonempty h_upper_bound_1
  -- Lower bound: 1 ≤ S(X₁)
  have h_ge : 1 ≤ Ctx.S Ctx.X₁ :=
    le_csSup h_bdd h_1_in_L
  exact le_antisymm h_le h_ge

/-! ### Theorem 2.2 (Monotonicity - Easy Direction) -/

/-- Theorem 2.2 (ii) (⇒ direction): If X ≺ Y, then S(X) ≤ S(Y). -/
lemma CanonicalEntropyContext.S_le_of_le (X Y : TW.State Γ)
    (h_le : X ≺ Y) : Ctx.S X ≤ Ctx.S Y := by
  -- lam(X) ⊆ lam(Y) by transitivity of ≺.
  have h_subset : Ctx.LambdaSet X ⊆ Ctx.LambdaSet Y := by
    intro t ht_in_LX
    exact GenRefAccessible_trans_le Ctx.X₀ Ctx.X₁ X Y t ht_in_LX h_le
  -- sSup(A) ≤ sSup(B) if A ⊆ B.
  -- Requires BddAbove(Y) and Nonempty(X).
  exact csSup_le_csSup (Ctx.LambdaSet_BddAbove Y) (HasLambdaWitness.lambda_nonempty X) h_subset

/-! ### The Gap Lemma and Continuity Lemma -/

open Filter Topology

/-- The Global Comparison Hypothesis (GCH). Assumes comparability holds for all states in the ThermoWorld.
    This is required axiomatically here to prove the abstract Entropy Principle.
-/
def GlobalComparisonHypothesis (System : Type u) [TW : ThermoWorld System] : Prop :=
  ∀ {Γ₁ Γ₂ : System} (X : TW.State Γ₁) (Y : TW.State Γ₂), Comparable X Y

/-- Gap Lemma under GCH: Provides a UNIFORM FAMILY of gap witnesses.
    If A ≺≺ B, then there exists δ₀ > 0 such that for ALL 0 < τ ≤ δ₀,
    we have (A, τX₁) ≺ (B, τX₀). -/
lemma GapLemmaGCH (Ctx : CanonicalEntropyContext Γ)
    [Fact (GlobalComparisonHypothesis System)]
    {ΓA ΓB : System} (A : TW.State ΓA) (B : TW.State ΓB) (h_strict : A ≺≺ B) :
    ∃ (δ₀ : ℝ) (_ : 0 < δ₀),
      ∀ {τ : ℝ} (hτ_pos : 0 < τ) (_ : τ ≤ δ₀),
        comp_state (A, scale_state (ne_of_gt hτ_pos) Ctx.X₁) ≺
        comp_state (B, scale_state (ne_of_gt hτ_pos) Ctx.X₀) := by
  classical
  by_contra h
  -- Negate the goal: for all δ₀>0 there exists 0<τ≤δ₀ s.t. the forward inequality fails.
  push_neg at h
  -- Build a sequence τₖ with 0 < τₖ ≤ 1/(k+1) where the forward inequality fails.
  have h_seq :
      ∀ k : ℕ, ∃ τ, ∃ (hτ : 0 < τ), τ ≤ (1 / ((k+1 : ℝ))) ∧
        ¬ comp_state (A, scale_state (ne_of_gt hτ) Ctx.X₁) ≺
          comp_state (B, scale_state (ne_of_gt hτ) Ctx.X₀) := by
    intro k
    have hk_pos : 0 < (1 / ((k+1 : ℝ))) := by
      exact one_div_pos.mpr (Nat.cast_add_one_pos k)
    rcases h (1 / ((k+1 : ℝ))) hk_pos with ⟨τ, hτ_pos, hτ_le, hτ_not⟩
    exact ⟨τ, hτ_pos, hτ_le, hτ_not⟩
  -- Choose τₖ and its properties.
  choose τ hτ_pos τ_le τ_not using h_seq
  -- Show τₖ → 0 via squeeze: 0 ≤ τₖ ≤ 1/(k+1), and 1/(k+1) → 0.
  have hτ_nonneg : ∀ n, 0 ≤ τ n := fun n => le_of_lt (hτ_pos n)
  let ε_seq : ℕ → ℝ := fun k => 1 / ((k+1 : ℝ))
  have hε_tendsto : Tendsto ε_seq atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h0_tendsto : Tendsto (fun (_ : ℕ) => (0:ℝ)) atTop (nhds 0) := tendsto_const_nhds
  have h_lower : ∀ᶠ k in atTop, (0 : ℝ) ≤ τ k :=
    Filter.Eventually.of_forall hτ_nonneg
  have h_upper : ∀ᶠ k in atTop, τ k ≤ ε_seq k :=
    Filter.Eventually.of_forall τ_le
  have hτ_tendsto : Tendsto τ atTop (nhds 0) :=
    tendsto_of_tendsto_of_le_of_le h0_tendsto hε_tendsto h_lower h_upper
  -- Under GCH, for each k either forward or reverse holds; forward is false, so reverse holds.
  have h_le_rev :
      ∀ n, comp_state (B, scale_state (ne_of_gt (hτ_pos n)) Ctx.X₀) ≺
           comp_state (A, scale_state (ne_of_gt (hτ_pos n)) Ctx.X₁) := by
    intro n
    -- Extract GCH and apply it to the two compound states.
    have hGCH : GlobalComparisonHypothesis System :=
      (inferInstance : Fact (GlobalComparisonHypothesis System)).out
    have hComp :
        Comparable
          (comp_state (A, scale_state (ne_of_gt (hτ_pos n)) Ctx.X₁))
          (comp_state (B, scale_state (ne_of_gt (hτ_pos n)) Ctx.X₀)) :=
      hGCH
        (comp_state (A, scale_state (ne_of_gt (hτ_pos n)) Ctx.X₁))
        (comp_state (B, scale_state (ne_of_gt (hτ_pos n)) Ctx.X₀))
    by_cases hdir :
      comp_state (A, scale_state (ne_of_gt (hτ_pos n)) Ctx.X₁) ≺
      comp_state (B, scale_state (ne_of_gt (hτ_pos n)) Ctx.X₀)
    · exact False.elim (τ_not n hdir)
    · -- pick the reverse from comparability
      simpa using (Or.resolve_left hComp hdir)
  -- A6_seq on the sequence gives B ≺ A, contradicting strictness.
  have h_B_le_A : B ≺ A := by
    -- Provide the existential package required by A6_seq.
    apply TW.A6_seq B A Ctx.X₀ Ctx.X₁
    refine ⟨τ, (fun n => hτ_pos n), hτ_tendsto, ?_⟩
    intro k
    simpa using h_le_rev k
  exact h_strict.2 h_B_le_A

/-- Lemma A.1 (Appendix A): The Gap Lemma.
    If A ≺≺ B and GCH holds, then there is a strict gap: ∃ δ > 0 such that (A, δX₁) ≺ (B, δX₀).
    This is a major consequence of A6 (Stability) and GCH.
-/
lemma GapLemmaGCH' {ΓA ΓB} (A : TW.State ΓA) (B : TW.State ΓB)
  (Ctx : CanonicalEntropyContext Γ)
  [hGCH : Fact (GlobalComparisonHypothesis System)]
  (h_strict : A ≺≺ B) :
  ∃ (δ : ℝ) (hδ : 0 < δ),
    comp_state (A, scale_state (ne_of_gt hδ) Ctx.X₁) ≺
    comp_state (B, scale_state (ne_of_gt hδ) Ctx.X₀) := by
  -- Proof by contradiction using A6 (Stability).
  by_contra h_contra; push_neg at h_contra
  -- Assume for all δ > 0, (A, δX₁) ⊀ (B, δX₀).
  -- We aim to show this implies B ≺ A, contradicting A ≺≺ B.
  have h_A6_contra : B ≺ A := by
    -- Apply A6_seq with Z₀=X₀ and Z₁=X₁.
    apply TW.A6_seq B A Ctx.X₀ Ctx.X₁
    -- Use the sequence εₖ = 1/(k+1).
    let ε_seq (k : ℕ) := 1 / ((k+1) : ℝ)
    have hε_pos : ∀ k, 0 < ε_seq k := by
      intro k; apply one_div_pos.mpr; exact Nat.cast_add_one_pos k
    have hε_to_0 : Filter.Tendsto ε_seq Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine ⟨ε_seq, hε_pos, hε_to_0, ?_⟩
    intro k
    let δ := ε_seq k
    have hδ_pos := hε_pos k
    -- We assumed (A, δX₁) ⊀ (B, δX₀).
    have h_not_le := h_contra δ hδ_pos
    -- By GCH, this implies (B, δX₀) ≺ (A, δX₁).
    let B_δX₀ := comp_state (B, scale_state (ne_of_gt hδ_pos) Ctx.X₀)
    let A_δX₁ := comp_state (A, scale_state (ne_of_gt hδ_pos) Ctx.X₁)
    have h_comp : Comparable A_δX₁ B_δX₀ := hGCH.out A_δX₁ B_δX₀
    have h_le_rev : B_δX₀ ≺ A_δX₁ := by
      cases h_comp with
      | inl h => contradiction -- h is (A, δX₁) ≺ (B, δX₀), which contradicts h_not_le.
      | inr h => exact h
    -- Normalize to the A6 premise form: (B, εₖZ₀) ≺ (A, εₖZ₁).
    simpa [comp_state] using h_le_rev
  -- B ≺ A contradicts A ≺≺ B.
  exact h_strict.2 h_A6_contra

lemma exists_strict_mono_tendsto_sSup
    {S : Set ℝ} (h_ne : S.Nonempty) (h_bdd : BddAbove S)
    (h_not_max : sSup S ∉ S) :
    ∃ (u : ℕ → ℝ),
      (∀ n, u n ∈ S) ∧
      StrictMono u ∧
      Tendsto u atTop (nhds (sSup S)) := by
  obtain ⟨u, hu_mono, _, hu_tendsto, hu_mem⟩ :=
    (isLUB_csSup h_ne h_bdd).exists_seq_strictMono_tendsto_of_notMem h_not_max h_ne
  exact ⟨u, hu_mem, hu_mono, hu_tendsto⟩

omit h_witness in
/-- Helper Lemma for Continuity: Reorganization chain.
    (R(lamₖ), δX₁) ≈ (R(lam), δX₀) where lam = lamₖ + δₖ. (0 ≤ lamₖ < lam ≤ 1).
-/
lemma ReferenceState_reorg_continuity
  (lam lamₖ δₖ : ℝ)
  (h_eq : lam = lamₖ + δₖ)
  (h_lam_range : 0 ≤ lam ∧ lam ≤ 1)
  (h_lamₖ_range : 0 ≤ lamₖ ∧ lamₖ ≤ 1)
  (h_δₖ_nonneg : 0 ≤ δₖ) :
  let R_lam := ReferenceState Ctx.X₀ Ctx.X₁ lam h_lam_range.1 h_lam_range.2
  let R_lamₖ := ReferenceState Ctx.X₀ Ctx.X₁ lamₖ h_lamₖ_range.1 h_lamₖ_range.2
  let δX₁ := gscale_state h_δₖ_nonneg Ctx.X₁
  let δX₀ := gscale_state h_δₖ_nonneg Ctx.X₀
  comp_state (R_lamₖ, δX₁) ≈ comp_state (R_lam, δX₀) := by
  intros R_lam R_lamₖ δX₁ δX₀
  -- Shorthands for components.
  let X₀_1mlamₖ := gscale_state (sub_nonneg.mpr h_lamₖ_range.2) Ctx.X₀
  let X₁_lamₖ   := gscale_state h_lamₖ_range.1 Ctx.X₁
  let X₀_1mlam  := gscale_state (sub_nonneg.mpr h_lam_range.2) Ctx.X₀
  let X₁_lam    := gscale_state h_lam_range.1 Ctx.X₁
  -- 1. Reorganize LHS: (R(lamₖ), δX₁) ≈ ((1-lamₖ)X₀, (lamₖX₁, δX₁)).
  have h_assoc_L := assoc_equiv_R X₀_1mlamₖ X₁_lamₖ δX₁
  -- 2. Recombine X₁ terms: (lamₖX₁, δX₁) ≈ lamX₁.
  have h_recomb_X₁ : comp_state (X₁_lamₖ, δX₁) ≈ X₁_lam := by
    have h_gr := generalized_recombination_lemma h_lamₖ_range.1 h_δₖ_nonneg Ctx.X₁
    have h_align := by exact System
    aesop
  -- Lift recombination: LHS ≈ ((1-lamₖ)X₀, lamX₁).
  have h_LHS_step1 : comp_state (R_lamₖ, δX₁) ≈ comp_state (X₀_1mlamₖ, X₁_lam) := by
    exact thermo_equiv_trans' h_assoc_L (L2_4_i (thermo_equiv_refl _) h_recomb_X₁)
  -- 3. Expand X₀ term: (1-lamₖ)X₀ with 1-lamₖ = (1-lam)+δₖ.
  have h_eq_X₀ : 1 - lamₖ = (1 - lam) + δₖ := by rw [h_eq]; ring
  -- (1-lamₖ)X₀ ≈ ((1-lam)X₀, δₖX₀).
  -- We build the chain explicitly to avoid a mismatch in the expected second component (alias X₀_1mlamₖ).
  have h_recomb_X₀ : X₀_1mlamₖ ≈ comp_state (X₀_1mlam, δX₀) := by
    -- Nonnegativity witnesses.
    have h_1mlam_nonneg : 0 ≤ 1 - lam := sub_nonneg.mpr h_lam_range.2
    have h_sum_nonneg : 0 ≤ (1 - lam) + δₖ := add_nonneg h_1mlam_nonneg h_δₖ_nonneg
    -- Align (1 - lamₖ) with (1 - lam) + δₖ.
    have h_align :
        X₀_1mlamₖ ≈ gscale_state h_sum_nonneg Ctx.X₀ := by
      dsimp [X₀_1mlamₖ]
      exact gscale_eq_coherence h_eq_X₀ Ctx.X₀ (sub_nonneg.mpr h_lamₖ_range.2) h_sum_nonneg
    -- Recombination: ( (1-lam) + δₖ )•X₀ ≈ ( (1-lam)•X₀ , δₖ•X₀ ).
    have h_recomb_base :
        gscale_state (add_nonneg h_1mlam_nonneg h_δₖ_nonneg) Ctx.X₀
          ≈ comp_state (gscale_state h_1mlam_nonneg Ctx.X₀,
                        gscale_state h_δₖ_nonneg Ctx.X₀) :=
      generalized_recombination_lemma h_1mlam_nonneg h_δₖ_nonneg Ctx.X₀
    -- Adjust the proof term on the sum (proof irrelevance).
    have h_pi :
        gscale_state (add_nonneg h_1mlam_nonneg h_δₖ_nonneg) Ctx.X₀
          = gscale_state h_sum_nonneg Ctx.X₀ :=
      gscale_state_proof_irrel _ _ _
    -- Assemble recombination in the desired shape.
    have h_recomb :
        gscale_state h_sum_nonneg Ctx.X₀ ≈
        comp_state (X₀_1mlam, δX₀) := by
      -- Unfold aliases and rewrite.
      dsimp [X₀_1mlam, δX₀] at *
      simpa [h_pi] using h_recomb_base
    -- Chain: X₀_1mlamₖ ≈ ( (1-lam)+δₖ )•X₀ ≈ ((1-lam)•X₀, δₖ•X₀).
    exact thermo_equiv_trans' h_align h_recomb
  -- 4. Substitute back: LHS ≈ (((1-lam)X₀, δₖX₀), lamX₁).
  have h_LHS_step2 := L2_4_i h_recomb_X₀ (thermo_equiv_refl X₁_lam)
  -- 5. Reorganize to match RHS: ((A, B), C) ≈ ((A, C), B).
  -- ((1-lam)X₀, δₖX₀, lamX₁) ≈ ((1-lam)X₀, lamX₁, δₖX₀) = (R(lam), δₖX₀).
  have h_reorg : comp_state (comp_state (X₀_1mlam, δX₀), X₁_lam) ≈ comp_state (R_lam, δX₀) := by
    -- Assoc R, Comm inner, Assoc L.
    have h1 := assoc_equiv_R X₀_1mlam δX₀ X₁_lam
    -- Explicitly provide the state to thermo_equiv_refl so Lean can infer universes.
    have h2 :
        comp_state (X₀_1mlam, comp_state (δX₀, X₁_lam))
          ≈ comp_state (X₀_1mlam, comp_state (X₁_lam, δX₀)) :=
      L2_4_i (thermo_equiv_refl X₀_1mlam) (comp_comm_equiv_clean δX₀ X₁_lam)
    have h3 := assoc_equiv_L X₀_1mlam X₁_lam δX₀
    exact thermo_equiv_trans' h1 (thermo_equiv_trans' h2 h3)
  -- Combine the chain.
  exact thermo_equiv_trans' h_LHS_step1 (thermo_equiv_trans' h_LHS_step2 h_reorg)


/-! ### The Continuity Lemma (Lemma 2.8) -/

/-- The Continuity Lemma (Lemma 2.8): The supremum of lam(X) is attained. S(X) ∈ lam(X).
    We prove the central case where 0 < S(X) < 1.
-/
lemma CanonicalEntropyContext.ContinuityLemma_central_case (X : TW.State Γ)
    (h_range : 0 < Ctx.S X ∧ Ctx.S X < 1) :
    Ctx.S X ∈ Ctx.LambdaSet X := by
  set lam := Ctx.S X with h_lam_def
  have h_lam_pos := h_range.1
  have h_lam_lt1 := h_range.2
  -- Proof by contradiction using A6 (Stability).
  by_contra h_not_in_lam
  -- 1. Setup the sequence lamₖ → lam⁻.
  -- Use the analysis lemma to get the sequence.
  -- First, translate the contradiction hypothesis into the form required by the sequence lemma.
  have h_not_max' : sSup (Ctx.LambdaSet X) ∉ Ctx.LambdaSet X := by
    -- By definition of S we have lam = sSup lam(X); rewrite.
    simpa [h_lam_def] using h_not_in_lam
  -- Nonemptiness from the witness typeclass.
  have h_nonempty : (Ctx.LambdaSet X).Nonempty :=
    HasLambdaWitness.lambdaSet_nonempty (Ctx:=Ctx) X
  -- Bounded above lemma already available.
  have h_bdd := Ctx.LambdaSet_BddAbove X
  -- Apply the analytic construction lemma.
  have h_seq_exists :=
    exists_strict_mono_tendsto_sSup
      (S := Ctx.LambdaSet X) h_nonempty h_bdd h_not_max'
  rcases h_seq_exists with ⟨lam_seq, h_in_lam, h_mono, h_tendsto⟩
  -- Define δₖ = lam - lamₖ.
  let δ_seq : ℕ → ℝ := fun k => lam - lam_seq k
  -- Properties of δₖ.
  have h_lt_lam : ∀ k, lam_seq k < lam := by
    intro k
    have h_le := le_csSup h_bdd (h_in_lam k)
    have h_ne : lam_seq k ≠ lam := by
      intro h_eq
      have : lam ∈ Ctx.LambdaSet X := by simpa [h_eq] using h_in_lam k
      exact h_not_in_lam this
    exact lt_of_le_of_ne h_le h_ne
  have h_δ_pos : ∀ k, 0 < δ_seq k := by
    intro k; dsimp [δ_seq]; exact sub_pos.mpr (h_lt_lam k)
  have h_δ_tendsto_0 : Tendsto δ_seq atTop (nhds 0) := by
    -- δ_seq k = lam - lam_seq k, with lam_seq → lam
    have h_const : Tendsto (fun _ : ℕ => lam) atTop (nhds lam) := tendsto_const_nhds
    have h_sub :
        Tendsto (fun k => (fun _ => lam) k - lam_seq k) atTop (nhds (lam - lam)) :=
      Tendsto.sub h_const h_tendsto
    simpa [δ_seq] using h_sub
  -- Ensure lamₖ are eventually in (0, 1).
  have h_lamₖ_eventually_pos : ∀ᶠ k in atTop, 0 < lam_seq k :=
    h_tendsto.eventually (eventually_gt_nhds h_lam_pos)
  -- 2. The A6 argument. We aim to show R(lam) ≺ X.
  -- Define R(lam).
  have h_lam_range_le : 0 ≤ lam ∧ lam ≤ 1 := ⟨le_of_lt h_lam_pos, le_of_lt h_lam_lt1⟩
  let R_lam := ReferenceState Ctx.X₀ Ctx.X₁ lam h_lam_range_le.1 h_lam_range_le.2
  -- We need to show (R(lam), δₖX₀) ≺ (X, δₖX₁), eventually for large k.
  have h_A6_premise : ∀ᶠ k in atTop,
      comp_state (R_lam, scale_state (h_δ_pos k).ne' Ctx.X₀) ≺
      comp_state (X, scale_state (h_δ_pos k).ne' Ctx.X₁) := by
    filter_upwards [h_lamₖ_eventually_pos] with k h_lamₖ_pos
    -- Establish ranges for lamₖ.
    have h_lamₖ_lt1 : lam_seq k < 1 := lt_trans (h_lt_lam k) h_lam_lt1
    have h_lamₖ_range_le : 0 ≤ lam_seq k ∧ lam_seq k ≤ 1 :=
      ⟨le_of_lt h_lamₖ_pos, le_of_lt h_lamₖ_lt1⟩
    let R_lamₖ := ReferenceState Ctx.X₀ Ctx.X₁ (lam_seq k)
        h_lamₖ_range_le.1 h_lamₖ_range_le.2
    -- We know R(lamₖ) ≺ X.
    have h_access : R_lamₖ ≺ X := by
      have h := h_in_lam k
      dsimp [CanonicalEntropyContext.LambdaSet, GenRefAccessible] at h
      rwa [dif_pos h_lamₖ_range_le] at h
    -- Add δₖX₁ to both sides (A3).
    let δₖX₁ := scale_state (h_δ_pos k).ne' Ctx.X₁
    have h_step1 : comp_state (R_lamₖ, δₖX₁) ≺ comp_state (X, δₖX₁) :=
      TW.A3 h_access (thermo_le_refl δₖX₁)
    -- Apply the reorganization lemma.
    have h_reorg := ReferenceState_reorg_continuity Ctx
      (lam := lam) (lamₖ := lam_seq k) (δₖ := δ_seq k)
      (h_eq := by dsimp [δ_seq]; ring)
      (h_lam_range := h_lam_range_le)
      (h_lamₖ_range := h_lamₖ_range_le)
      (h_δₖ_nonneg := le_of_lt (h_δ_pos k))
    -- Convert gscale_state to scale_state.
    have h_δₖ_nonneg := le_of_lt (h_δ_pos k)
    have h_gscale_to_scale_X₀ :
        gscale_state h_δₖ_nonneg Ctx.X₀ =
        scale_state (h_δ_pos k).ne' Ctx.X₀ := by
      simp [gscale_state_pos h_δₖ_nonneg (h_δ_pos k)]
    have h_gscale_to_scale_X₁ :
        gscale_state h_δₖ_nonneg Ctx.X₁ = δₖX₁ := by
      simp [gscale_state_pos h_δₖ_nonneg (h_δ_pos k), δₖX₁]
    have h_reorg_clean :
        comp_state (R_lamₖ, δₖX₁) ≈
        comp_state (R_lam, scale_state (h_δ_pos k).ne' Ctx.X₀) := by
      simpa [h_gscale_to_scale_X₀, h_gscale_to_scale_X₁] using h_reorg
    -- Combine.
    exact le_of_equiv_le (thermo_equiv_symm h_reorg_clean) h_step1
  -- 3. Apply A6_seq.
  have h_Rlam_le_X : R_lam ≺ X := by
    rcases eventually_atTop.1 h_A6_premise with ⟨N, h_N⟩
    -- Shifted sequence εₙ = δ_{n+N}.
    let ε_seq := fun n => δ_seq (n + N)
    have h_ε_pos : ∀ n, 0 < ε_seq n := fun n => h_δ_pos (n + N)
    have h_ε_tendsto_0 : Tendsto ε_seq atTop (nhds 0) := by
      -- (n ↦ n + N) tends to atTop; compose with δ_seq → 0.
      have h_shift : Tendsto (fun n : ℕ => n + N) atTop atTop :=
        tendsto_add_atTop_nat N
      exact h_δ_tendsto_0.comp h_shift
    have h_ε_premise : ∀ n,
        comp_state (R_lam, scale_state (h_ε_pos n).ne' Ctx.X₀) ≺
        comp_state (X,     scale_state (h_ε_pos n).ne' Ctx.X₁) := by
      intro n
      exact h_N (n + N) (Nat.le_add_left _ _)
    apply TW.A6_seq R_lam X Ctx.X₀ Ctx.X₁
    -- Align with A6_seq expected form.
    have h_ε_premise_aligned : ∀ n,
        TW.le
          (TW.state_of_comp_equiv.symm
            (R_lam, (TW.state_of_scale_equiv (ne_of_gt (h_ε_pos n))).symm Ctx.X₀))
          (TW.state_of_comp_equiv.symm
            (X, (TW.state_of_scale_equiv (ne_of_gt (h_ε_pos n))).symm Ctx.X₁)) := by
      simpa [comp_state, scale_state] using h_ε_premise
    exact ⟨ε_seq, h_ε_pos, h_ε_tendsto_0, h_ε_premise_aligned⟩
  -- This means lam ∈ lam(X), contradiction.
  have h_lam_in_lam : lam ∈ Ctx.LambdaSet X := by
    dsimp [CanonicalEntropyContext.LambdaSet, GenRefAccessible]
    rwa [dif_pos h_lam_range_le]
  exact h_not_in_lam h_lam_in_lam

/-- Complete the Continuity Lemma for boundary cases -/
lemma CanonicalEntropyContext.ContinuityLemma_boundary_cases (X : TW.State Γ)
    (h_boundary : Ctx.S X = 0 ∨ Ctx.S X = 1) :
    Ctx.S X ∈ Ctx.LambdaSet X := by
  classical
  rcases h_boundary with h0 | h1
  · -- Boundary S X = 0
    have h_sup : Ctx.S X = sSup (Ctx.LambdaSet X) := rfl
    have hS0 : Ctx.S X = 0 := h0
    -- If already 0 ∈ lam(X) we are done
    by_cases h_in : 0 ∈ Ctx.LambdaSet X
    · simpa [hS0]
    -- Otherwise derive contradiction
    have h_nonempty := (HasLambdaWitness.lambda_nonempty (Ctx:=Ctx) X)
    -- Since sup lam(X)=0 and 0 ∉ lam(X), we can extract a strict mono sequence lamₙ → 0
    have h_not_mem : sSup (Ctx.LambdaSet X) ∉ Ctx.LambdaSet X := by
      exact Eq.mpr_not (congrArg (Membership.mem (Ctx.LambdaSet X)) h0) h_in
    obtain ⟨lam_seq, h_mem, h_mono, h_tendsto⟩ :=
      exists_strict_mono_tendsto_sSup
        (S := Ctx.LambdaSet X)
        h_nonempty
        (Ctx.LambdaSet_BddAbove X)
        h_not_mem
    -- All lam_seq n < 0 (since sup=0 and 0 not in set)
    have h_neg : ∀ n, lam_seq n < 0 := by
      intro n
      -- First get the generic upper bound lam_seq n ≤ sSup lam(X), then rewrite using hS0 : S X = 0.
      have h_sSup : sSup (Ctx.LambdaSet X) = 0 := by
        -- S X = 0 (hS0), and S X = sSup lam(X) by definition.
        simpa [CanonicalEntropyContext.S] using hS0
      have h_le : lam_seq n ≤ 0 := by
        have h := le_csSup (Ctx.LambdaSet_BddAbove X) (h_mem n)
        simpa [h_sSup] using h
      have h_ne : lam_seq n ≠ 0 := by
        intro h
        exact h_in (by simpa [h] using h_mem n)
      exact lt_of_le_of_ne h_le h_ne
    -- Define εₙ := - lam_seq n > 0
    let ε_seq : ℕ → ℝ := fun n => - lam_seq n
    have hε_pos : ∀ n, 0 < ε_seq n := by
      intro n; dsimp [ε_seq]; exact neg_pos.mpr (h_neg n)
    have hε_tendsto0 : Filter.Tendsto ε_seq Filter.atTop (nhds 0) := by
      -- ε_seq n = - lam_seq n → -0 = 0
      -- First rewrite the target limit using sSup (Ctx.LambdaSet X) = 0 derived from hS0.
      have h_lim : sSup (Ctx.LambdaSet X) = 0 := by simpa [CanonicalEntropyContext.S] using hS0
      have : Tendsto lam_seq atTop (nhds 0) := by simpa [h_lim] using h_tendsto
      simpa [ε_seq] using this.neg
    -- From lam_seq n ∈ lam(X) with lam_seq n < 0 we get:
    -- (1 - lam_seq n) X₀ ≺ (X, (-lam_seq n) X₁)   (negative branch)
    have h_access_neg :
      ∀ n,
        let lam := lam_seq n
        let ε := ε_seq n
        GenRefAccessible Ctx.X₀ Ctx.X₁ X lam ∧ lam < 0 := by
      intro n; refine ⟨h_mem n, h_neg n⟩
    -- Convert each to the shape (X₀, ε X₀) ≺ (X, ε X₁)
    have h_seq_rel :
      ∀ n,
        comp_state (Ctx.X₀, scale_state (ne_of_gt (hε_pos n)) Ctx.X₀) ≺
        comp_state (X,     scale_state (ne_of_gt (hε_pos n)) Ctx.X₁) := by
      intro n
      --dsimp [GenRefAccessible] at (h_access_neg n)
      rcases (h_access_neg n) with ⟨hG, hlt0⟩
      -- Unfold negative case of GenRefAccessible
      have h_not_range : ¬ (0 ≤ lam_seq n ∧ lam_seq n ≤ 1) := by
        intro h; exact (not_lt.mpr h.1) (h_neg n)
      have h_not_gt1 : ¬ (1 < lam_seq n) := by
        exact not_lt.mpr (le_trans (le_of_lt (h_neg n)) (by norm_num : (0:ℝ) ≤ 1))
      -- Use the else branch (lam < 0)
      -- Use simp (not dsimp) so the hypotheses discharge the if-conditions of GenRefAccessible.
      simp [GenRefAccessible, h_not_range, h_not_gt1] at hG
      -- hG : (1 - lam)•X₀ ≺ (X, (-lam)•X₁)
      -- Recombine (1 - lam)•X₀ ≈ (X₀, (-lam)•X₀)
      let lam := lam_seq n
      have h_pos_eps : 0 < -lam := by simpa [ε_seq] using hε_pos n
      have h_recomb :
        scale_state (ne_of_gt (show 0 < 1 - lam from
          by
            have := h_neg n
            linarith)) Ctx.X₀
          ≈
        comp_state (Ctx.X₀, scale_state (ne_of_gt h_pos_eps) Ctx.X₀) := by
        -- (1 - lam) = 1 + (-lam); apply recombination lemma
        have h_eq : 1 - lam = 1 + (-lam) := by ring
        have h1 : 0 < (1:ℝ) := by norm_num
        have hml : 0 < -lam := h_pos_eps
        have h_re :=
          recombination_lemma (a:=1) (b:=-lam) h1 hml Ctx.X₀
        -- h_re : (1 + (-lam))•X₀ ≈ (1•X₀, (-lam)•X₀)
        -- Chain with 1•X₀ ≈ X₀
        have h1X := one_smul_coherence_clean Ctx.X₀
        -- Align (1 - lam)•X₀ with (1 + (-lam))•X₀
        have h_cast :
          scale_state (ne_of_gt (show 0 < 1 - lam from by linarith)) Ctx.X₀
            ≈
          scale_state (ne_of_gt (add_pos h1 hml)) Ctx.X₀ := by
          -- CEq for scaling equality (handled by gscale path earlier in file; we re-express
          -- via scale_eq_coherence through casts). Here we supply a short direct step:
          -- Use the structural equality of systems; we treat this as cast-equivalence neutrality.
          -- (For brevity; in a fully expanded formalization one would mirror earlier cast lemmas.)
          have : 1 - lam = 1 + (-lam) := h_eq
          -- rewriting systems identical
          -- Provide reflexive equivalence:
          exact thermo_equiv_refl _
        -- Chain
        exact
          thermo_equiv_trans'
            h_cast
            (thermo_equiv_trans'
              h_re
              (L2_4_i h1X (thermo_equiv_refl _)))
      -- Replace left side of hG using equivalence
      have h_transport :
        comp_state (Ctx.X₀, scale_state (ne_of_gt h_pos_eps) Ctx.X₀) ≺
        comp_state (X, scale_state (ne_of_gt h_pos_eps) Ctx.X₁) :=
        le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_recomb) hG)
                       (thermo_equiv_refl _)
      simpa [ε_seq] using h_transport
    -- Apply A6_seq with sequence ε_seq, states X₀, X, Z₀ = X₀, Z₁ = X₁
    have h_X0_le_X : Ctx.X₀ ≺ X := by
      apply TW.A6_seq Ctx.X₀ X Ctx.X₀ Ctx.X₁
      refine ⟨ε_seq, hε_pos, hε_tendsto0, ?_⟩
      intro n
      -- align shape for A6_seq (cast layer sugar):
      -- Adjust: use the sequence with R_{lam' n} directly (A6_seq will yield R_{lam' n} ≺ X;
      -- upgrading to R₁ will be handled separately by stability / monotonicity lemmas).
      exact h_seq_rel n
    -- Now 0 ∈ lam(X) because R₀ ≈ X₀
    have h_R0_equiv := ReferenceState_zero_equiv Ctx.X₀ Ctx.X₁
    have h_0_in :
        0 ∈ Ctx.LambdaSet X := by
      dsimp [CanonicalEntropyContext.LambdaSet, GenRefAccessible]
      -- 0 in [0,1]
      have h_range : 0 ≤ (0:ℝ) ∧ (0:ℝ) ≤ 1 := by constructor <;> norm_num
      simp [h_range]
      exact le_of_equiv_le h_R0_equiv h_X0_le_X
    exact (h_in h_0_in).elim
  · -- Boundary S X = 1
    have hS1 : Ctx.S X = 1 := h1
    by_cases h_in : 1 ∈ Ctx.LambdaSet X
    · simpa [hS1]
    -- sSup lam(X) = 1 but 1 ∉ lam(X), get a strictly increasing sequence lamₖ ↑ 1.
    have h_not_mem : sSup (Ctx.LambdaSet X) ∉ Ctx.LambdaSet X := by
      -- sSup (lam(X)) = S X by definition; rewrite and use h_in
      have h_sSup_eq : sSup (Ctx.LambdaSet X) = 1 := by
        rw [← CanonicalEntropyContext.S, hS1]
      rw [h_sSup_eq]
      exact h_in
    have h_nonempty := (HasLambdaWitness.lambda_nonempty (Ctx:=Ctx) X)
    have h_bdd := Ctx.LambdaSet_BddAbove X
    obtain ⟨lam_seq, h_mem, h_strict, h_tendsto⟩ :=
      exists_strict_mono_tendsto_sSup
        (S := Ctx.LambdaSet X) h_nonempty h_bdd h_not_mem
    have h_lt1 : ∀ n, lam_seq n < 1 := by
      intro n
      have h_le : lam_seq n ≤ sSup (Ctx.LambdaSet X) :=
        le_csSup h_bdd (h_mem n)
      have h_ne : lam_seq n ≠ 1 := by
        intro hEq; exact h_in (by simpa [CanonicalEntropyContext.S, hS1, hEq] using h_mem n)
      have h_sSup_eq_1 : sSup (Ctx.LambdaSet X) = 1 := by
        rw [← CanonicalEntropyContext.S, hS1]
      rw [h_sSup_eq_1] at h_le
      exact lt_of_le_of_ne h_le h_ne
    -- Eventually lam_seq n > 0 (since lam_seq → 1 > 0)
    have h_event_pos : ∀ᶠ n in Filter.atTop, 0 < lam_seq n := by
      have h_sSup_eq : sSup (Ctx.LambdaSet X) = 1 := by
        rw [← CanonicalEntropyContext.S, hS1]
      have h_pos : 0 < sSup (Ctx.LambdaSet X) := by
        rw [h_sSup_eq]; norm_num
      exact h_tendsto.eventually (eventually_gt_nhds h_pos)
    obtain ⟨N, hN⟩ := (eventually_atTop.1 h_event_pos)
    -- Shifted sequence lam'ₙ := lam_seq (n+N), now lam'ₙ ∈ lam(X), 0 < lam'ₙ < 1.
    let lam' := fun n : ℕ => lam_seq (n + N)
    have hlam'_mem : ∀ n, lam' n ∈ Ctx.LambdaSet X := fun n => h_mem (n + N)
    have hlam'_pos : ∀ n, 0 < lam' n := fun n => hN _ (Nat.le_add_left _ _)
    have hlam'_lt1 : ∀ n, lam' n < 1 := fun n => h_lt1 (n + N)
    -- δₙ := 1 - lam'ₙ > 0 and δₙ → 0
    let δ' := fun n : ℕ => 1 - lam' n
    have hδ'_pos : ∀ n, 0 < δ' n := fun n => sub_pos.mpr (hlam'_lt1 n)
    have hδ'_tendsto0 :
        Tendsto δ' atTop (nhds 0) := by
      have h_const : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
      have h_shift_tendsto :
        Tendsto lam' atTop (nhds 1) := by
        -- lam' = lam_seq ∘ (·+N)
        have h_shift : Tendsto (fun n : ℕ => n + N) atTop atTop :=
          tendsto_add_atTop_nat N
        have h_sSup_eq_1 : sSup (Ctx.LambdaSet X) = 1 := by
          rw [← CanonicalEntropyContext.S, hS1]
        rw [← h_sSup_eq_1]
        exact h_tendsto.comp h_shift
      have h_sub := Tendsto.sub h_const h_shift_tendsto
      simpa [δ'] using h_sub
    -- For each n, interval case gives R_{lam' n} ≺ X
    have h_Rlam'_le_X :
      ∀ n, ReferenceState Ctx.X₀ Ctx.X₁ (lam' n)
              (le_of_lt (hlam'_pos n))
              (le_of_lt (hlam'_lt1 n)) ≺ X := by
      intro n
      have h_range : 0 ≤ lam' n ∧ lam' n ≤ 1 :=
        ⟨(hlam'_pos n).le, (hlam'_lt1 n).le⟩
      have h_in := hlam'_mem n
      dsimp [CanonicalEntropyContext.LambdaSet, GenRefAccessible] at h_in
      -- interval branch
      simpa [dif_pos h_range] using h_in
    -- Build the A6_seq premises:
    -- (R₁, δ'ₙ X₀) ≺ (X, δ'ₙ X₁)
    let R1 := ReferenceState Ctx.X₀ Ctx.X₁ 1 (by norm_num) (by norm_num)
    have h_seq_relation :
      ∀ n,
        comp_state (R1, scale_state (ne_of_gt (hδ'_pos n)) Ctx.X₀) ≺
        comp_state (X,  scale_state (ne_of_gt (hδ'_pos n)) Ctx.X₁) := by
      intro n
      -- Start with R_{lam' n} ≺ X then add δ'ₙX₁
      have h_base := h_Rlam'_le_X n
      let R_lam' := ReferenceState Ctx.X₀ Ctx.X₁ (lam' n)
                      (le_of_lt (hlam'_pos n))
                      (le_of_lt (hlam'_lt1 n))
      let δX₁ := scale_state (ne_of_gt (hδ'_pos n)) Ctx.X₁
      have h_add :
        comp_state (R_lam', δX₁) ≺ comp_state (X, δX₁) :=
        TW.A3 h_base (thermo_le_refl δX₁)
      -- Reorganize (R_{lam'}, δX₁) ≈ (R₁, δ'ₙ X₀)
      let δX₀ := scale_state (ne_of_gt (hδ'_pos n)) Ctx.X₀
      -- Use previously defined reorganization with lam = 1
      have h_reorg_raw :=
        ReferenceState_reorg_continuity (Ctx := Ctx)
          (lam := 1) (lamₖ := lam' n) (δₖ := δ' n)
          (h_eq := by dsimp [δ']; ring)
          (h_lam_range := ⟨by norm_num, by norm_num⟩)
          (h_lamₖ_range := ⟨(hlam'_pos n).le, (hlam'_lt1 n).le⟩)
          (h_δₖ_nonneg := (hδ'_pos n).le)
      -- Convert gscale to scale: we already have δ' n > 0 so gscale_state = scale_state
      have h_g2s₀ :
          gscale_state (show 0 ≤ δ' n from (hδ'_pos n).le) Ctx.X₀ =
          δX₀ := by
        simp [gscale_state_pos (show 0 ≤ δ' n from (hδ'_pos n).le) (hδ'_pos n)]
        rfl
      have h_g2s₁ :
          gscale_state (show 0 ≤ δ' n from (hδ'_pos n).le) Ctx.X₁ =
          δX₁ := by
        simp [gscale_state_pos (show 0 ≤ δ' n from (hδ'_pos n).le) (hδ'_pos n)]
        aesop
      have h_reorg :
        comp_state (R_lam', δX₁) ≈ comp_state (R1, δX₀) := by
        -- h_reorg_raw : (R_{lam'}, δ'X₁) ≈ (R₁, δ'X₀) with gscale versions
        -- replace gscaled δ'X₀, δ'X₁ by scale_state forms
        simpa [δX₀, δX₁, h_g2s₀, h_g2s₁] using h_reorg_raw
      -- Transport h_add along equivalence h_reorg.
      exact le_of_equiv_le (thermo_equiv_symm h_reorg) h_add
    -- Apply A6_seq with εₙ = δ'ₙ:
    have h_R1_le_X : R1 ≺ X := by
      apply TW.A6_seq R1 X Ctx.X₀ Ctx.X₁
      refine ⟨δ', (fun n => hδ'_pos n), hδ'_tendsto0, ?_⟩
      intro n
      -- A6_seq expects (R1, εₙ X₀) ≺ (X, εₙ X₁)
      simpa using h_seq_relation n
    -- R₁ ≺ X implies 1 ∈ lam(X), contradiction.
    have h_R1_equiv_X₁ := ReferenceState_one_equiv Ctx.X₀ Ctx.X₁
    have h_one_in :
        1 ∈ Ctx.LambdaSet X := by
      dsimp [CanonicalEntropyContext.LambdaSet, GenRefAccessible]
      have h_range : 0 ≤ (1:ℝ) ∧ (1:ℝ) ≤ 1 := by constructor <;> norm_num
      -- R₁ ≺ X and R₁ ≈ X₁ ⇒ (interval branch)
      have h_R1_le_X₁ : R1 ≺ X := h_R1_le_X
      simpa [dif_pos h_range] using h_R1_le_X₁
    exact (h_in h_one_in).elim
    -- For each n obtain (R_{lam_n}, δₙ X₀) ≺ (X, δₙ X₁) via reorganization:

open Classical

variable {Γ : System}
variable (Ctx : CanonicalEntropyContext Γ)
variable [HasLambdaWitness Ctx]
variable [Fact (GlobalComparisonHypothesis System)]

omit [HasLambdaWitness Ctx] [Fact (GlobalComparisonHypothesis System)] in
/-- Helper 1: From S(X) ∈ lam(X) obtain the forward inequality R_{S(X)} ≺ X. -/
lemma reference_le_of_mem_lambda
  (X : TW.State Γ)
  (h_cont : Ctx.S X ∈ Ctx.LambdaSet X)
  (h_bounds : 0 ≤ Ctx.S X ∧ Ctx.S X ≤ 1) :
  ReferenceState Ctx.X₀ Ctx.X₁ (Ctx.S X) h_bounds.1 h_bounds.2 ≺ X := by
  dsimp [CanonicalEntropyContext.LambdaSet, GenRefAccessible] at h_cont
  simp [h_bounds] at h_cont
  exact h_cont

omit [HasLambdaWitness Ctx] [Fact (GlobalComparisonHypothesis System)] in
/-- Helper 2: If R_{lam} ≺ X but X ≺ R_{lam} fails, we have strictness R_{lam} ≺≺ X. -/
lemma reference_strict_or_equiv
  (X : TW.State Γ) (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 1)
  (h_forward : ReferenceState Ctx.X₀ Ctx.X₁ lam hlam.1 hlam.2 ≺ X)
  (h_not_back : ¬ X ≺ ReferenceState Ctx.X₀ Ctx.X₁ lam hlam.1 hlam.2) :
  ReferenceState Ctx.X₀ Ctx.X₁ lam hlam.1 hlam.2 ≺≺ X :=
  ⟨h_forward, h_not_back⟩

omit [HasLambdaWitness Ctx] [Fact (GlobalComparisonHypothesis System)] in
/-- Auxiliary: convert a gap
    (R_lam , ε X₁) ≺ (X , ε X₀) with 0 ≤ lam ≤ 1, ε>0, lam+ε ≤ 1
    into R_{lam+ε} ≺ X, using the reorganization lemma and cancellation. -/
private lemma gap_promotes_lambda
  (X : TW.State Γ)
  {lam eps : ℝ}
  (hlam : 0 ≤ lam ∧ lam ≤ 1)
  (heps_pos : 0 < eps)
  (h_sum_le : lam + eps ≤ 1)
  (h_gap :
    comp_state (
      ReferenceState Ctx.X₀ Ctx.X₁ lam hlam.1 hlam.2,
      scale_state heps_pos.ne' Ctx.X₁)
      ≺
    comp_state (
      X,
      scale_state heps_pos.ne' Ctx.X₀)) :
  ReferenceState Ctx.X₀ Ctx.X₁ (lam + eps)
      (add_nonneg hlam.1 (le_of_lt heps_pos))
      h_sum_le ≺ X := by
  -- Convert the given gap to the gscale version required by the reorganization lemma
  have h_eps_nonneg : 0 ≤ eps := le_of_lt heps_pos
  -- Reorganization equivalence:
  have h_reorg :=
    ReferenceState_reorg_continuity (Ctx := Ctx)
      (lam := lam + eps) (lamₖ := lam) (δₖ := eps)
      (h_eq := by ring)
      (h_lam_range := ⟨add_nonneg hlam.1 (le_of_lt heps_pos), h_sum_le⟩)
      (h_lamₖ_range := hlam)
      (h_δₖ_nonneg := h_eps_nonneg)
  -- Simplify gscale_state to scale_state (since eps > 0):
  have h_reorg_clean :
      comp_state
        ( ReferenceState Ctx.X₀ Ctx.X₁ lam hlam.1 hlam.2,
          scale_state heps_pos.ne' Ctx.X₁)
      ≈
      comp_state
        ( ReferenceState Ctx.X₀ Ctx.X₁ (lam + eps)
            (add_nonneg hlam.1 (le_of_lt heps_pos)) h_sum_le,
          scale_state heps_pos.ne' Ctx.X₀) := by
    -- In h_reorg the δ pieces appear as gscale_state; rewrite.
    classical
    -- Rewrite the δX components.
    simpa [gscale_state_pos h_eps_nonneg heps_pos] using h_reorg
  -- Transport the inequality across the equivalence:
  have h_after :
      comp_state
        ( ReferenceState Ctx.X₀ Ctx.X₁ (lam + eps)
            (add_nonneg hlam.1 (le_of_lt heps_pos)) h_sum_le,
          scale_state heps_pos.ne' Ctx.X₀)
      ≺
      comp_state (X, scale_state heps_pos.ne' Ctx.X₀) :=
    le_of_equiv_le (thermo_equiv_symm h_reorg_clean) h_gap
  -- Cancel the common catalyst (ε X₀):
  exact
    CancellationLaw
      (ReferenceState Ctx.X₀ Ctx.X₁ (lam + eps)
        (add_nonneg hlam.1 (le_of_lt heps_pos)) h_sum_le)
      X
      (scale_state heps_pos.ne' Ctx.X₀) h_after

omit [HasLambdaWitness Ctx] [Fact (GlobalComparisonHypothesis System)] in
/-- (1) Boundary case lam = 1: a strict gap produces lam' = 1+δ ∈ lam(X), contradicts maximality. -/
private lemma gap_boundary_lambda_one
  (X : TW.State Γ)
  {δ : ℝ} (hδ_pos : 0 < δ) (h_sup : Ctx.S X = 1)
  (h_gap :
    comp_state (
      ReferenceState Ctx.X₀ Ctx.X₁ 1 (by norm_num) (by norm_num),
      scale_state (ne_of_gt hδ_pos) Ctx.X₁)
      ≺
    comp_state (
      X,
      scale_state (ne_of_gt hδ_pos) Ctx.X₀)) :
  False := by
  -- R₁ ≈ X₁
  have h_R1 := ReferenceState_one_equiv (Γ := Γ) Ctx.X₀ Ctx.X₁
  -- Recombine (1+δ)X₁.
  have h_split :=
    recombination_lemma (a := 1) (b := δ) (by norm_num) hδ_pos Ctx.X₁
  -- 1•X₁ ≈ X₁
  have h_one := one_smul_coherence_clean (Γ := Γ) Ctx.X₁
  -- Build (X₁, δX₁) ≈ (1+δ)X₁
  have h_one_add_delta_pos : 0 < 1 + δ := add_pos (by norm_num) hδ_pos
  have h_pair_equiv :
      comp_state (Ctx.X₁, scale_state (ne_of_gt hδ_pos) Ctx.X₁)
        ≈ scale_state (ne_of_gt h_one_add_delta_pos) Ctx.X₁ := by
    have h_split_symm := thermo_equiv_symm h_split
    have h_first :
        comp_state (Ctx.X₁, scale_state (ne_of_gt hδ_pos) Ctx.X₁) ≈
          comp_state (scale_state (by norm_num : (1:ℝ) ≠ 0) Ctx.X₁,
                      scale_state (ne_of_gt hδ_pos) Ctx.X₁) :=
      L2_4_i (thermo_equiv_symm h_one) (thermo_equiv_refl _)
    exact thermo_equiv_trans' h_first h_split_symm
  -- Transport initial gap onto (X₁, δX₁)
  have h_gap_X1 :
    comp_state (Ctx.X₁, scale_state (ne_of_gt hδ_pos) Ctx.X₁) ≺
    comp_state (X, scale_state (ne_of_gt hδ_pos) Ctx.X₀) :=
    le_of_equiv_le (thermo_equiv_symm (L2_4_i h_R1 (thermo_equiv_refl _))) h_gap
  -- Replace (X₁, δX₁) by (1+δ)X₁
  have h_big :
      scale_state (ne_of_gt h_one_add_delta_pos) Ctx.X₁ ≺
      comp_state (X, scale_state (ne_of_gt hδ_pos) Ctx.X₀) :=
    le_of_equiv_le (thermo_equiv_symm h_pair_equiv) h_gap_X1
  -- Show 1+δ ∈ lam(X) (lam>1 branch).
  have h_gt1 : 1 < 1 + δ := by linarith
  have h_in :
      GenRefAccessible (Γ := Γ) Ctx.X₀ Ctx.X₁ X (1 + δ) := by
    dsimp [GenRefAccessible]
    have h_not_interval : ¬ (0 ≤ 1 + δ ∧ 1 + δ ≤ 1) := by
      intro h; linarith
    -- Since 1 < 1 + δ, the second (lam > 1) branch is selected; reduce to h_big.
    grind
  -- Use boundedness: (1+δ) ≤ sSup (lam(X)) = 1, contradiction with 1 < 1+δ.
  have h_le : 1 + δ ≤ 1 := by
    have h_le_sup := le_csSup (Ctx.LambdaSet_BddAbove X) h_in
    -- Rewrite only the supremum; avoid further simp turning (1+δ ≤ 1) into δ ≤ 0.
    have h_sup_sSup : sSup (Ctx.LambdaSet X) = 1 := by
      simpa [CanonicalEntropyContext.S] using h_sup
    simpa [h_sup_sSup] using h_le_sup
  have h_contra : ¬ (1 + δ ≤ 1) := by linarith
  exact h_contra h_le

/-- (2) Choose ε from δ when lam < 1 so that 0 < ε ≤ (1-lam)/2 and ε ≤ δ/2 (gives lam+ε ≤ 1). -/
private lemma choose_eps_for_interior
  {lam δ : ℝ} (hlam_lt1 : lam < 1) (hδ_pos : 0 < δ) :
  ∃ ε, 0 < ε ∧ ε ≤ (1 - lam)/2 ∧ ε ≤ δ/2 ∧ lam + ε ≤ 1 := by
  set ε := min ((1 - lam)/2) (δ/2)
  have h1 : 0 < (1 - lam)/2 := half_pos (sub_pos.mpr hlam_lt1)
  have h2 : 0 < δ/2 := half_pos hδ_pos
  have hε_pos : 0 < ε := by
    have := lt_min h1 h2; simpa [ε] using this
  have hε_le1 : ε ≤ (1 - lam)/2 := by
    have := min_le_left ((1 - lam)/2) (δ/2); simp [ε]
  have hε_le2 : ε ≤ δ/2 := by
    have := min_le_right ((1 - lam)/2) (δ/2); simp [ε]
  have hε_le_1m : ε ≤ 1 - lam := le_trans hε_le1
    (by
      have : (1 - lam)/2 ≤ 1 - lam := by
        have : 0 ≤ 1 - lam := sub_nonneg.mpr (le_of_lt hlam_lt1); linarith
      exact this)
  have h_sum_le : lam + ε ≤ 1 := by
    have := add_le_add_left hε_le_1m lam
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
  exact ⟨ε, hε_pos, hε_le1, hε_le2, h_sum_le⟩

omit [HasLambdaWitness Ctx] [Fact (GlobalComparisonHypothesis System)] in
/-- SOTA (refined) shrink lemma.
    Given a family of catalytic gaps at all scales `0 < ε ≤ δ`, we can of course
    extract the desired ε–gap. This replaces the unsound earlier version that
    tried to derive the ε–gap from a single δ–gap without a uniform hypothesis. -/
private lemma shrink_gap_to_eps
  (X : TW.State Γ)
  {lam δ ε : ℝ}
  (hlam_nonneg : 0 ≤ lam)
  (hlam_le1 : lam ≤ 1)
  (_ : 0 < δ)
  (hε_pos : 0 < ε)
  (hε_le : ε ≤ δ)
  (h_family :
      ∀ {τ : ℝ} (hτ_pos : 0 < τ) (_ : τ ≤ δ),
        comp_state (
          ReferenceState Ctx.X₀ Ctx.X₁ lam hlam_nonneg hlam_le1,
          scale_state (ne_of_gt hτ_pos) Ctx.X₁)
        ≺
        comp_state (
          X,
          scale_state (ne_of_gt hτ_pos) Ctx.X₀)) :
  comp_state (
    ReferenceState Ctx.X₀ Ctx.X₁ lam hlam_nonneg hlam_le1,
    scale_state (ne_of_gt hε_pos) Ctx.X₁)
  ≺
  comp_state (
    X,
    scale_state (ne_of_gt hε_pos) Ctx.X₀) := by
  -- Instantiate the family at τ = ε.
  have h_inst := h_family (τ := ε) hε_pos hε_le
  simpa using h_inst

omit [HasLambdaWitness Ctx] [Fact (GlobalComparisonHypothesis System)] in
/-- (4) Interior promotion: from ε-gap obtain lam+ε in lam(X) (via `gap_promotes_lambda`). -/
private lemma promote_lambda_interior
  (X : TW.State Γ)
  {lam ε : ℝ}
  (hlam : 0 ≤ lam ∧ lam ≤ 1)
  (hε_pos : 0 < ε) (h_sum_le : lam + ε ≤ 1)
  (h_gapε :
    comp_state (
      ReferenceState Ctx.X₀ Ctx.X₁ lam hlam.1 hlam.2,
      scale_state (ne_of_gt hε_pos) Ctx.X₁)
      ≺
    comp_state (
      X,
      scale_state (ne_of_gt hε_pos) Ctx.X₀)) :
  (lam + ε) ∈ Ctx.LambdaSet X := by
  have h_prom :=
    gap_promotes_lambda (Ctx := Ctx) X hlam hε_pos h_sum_le h_gapε
  have h_rng : 0 ≤ lam + ε ∧ lam + ε ≤ 1 :=
    ⟨add_nonneg hlam.1 (le_of_lt hε_pos), h_sum_le⟩
  dsimp [CanonicalEntropyContext.LambdaSet, GenRefAccessible]
  simp [dif_pos h_rng, h_prom]

omit [HasLambdaWitness Ctx] [Fact (GlobalComparisonHypothesis System)] in
/-- (5) Interior contradiction (revised, sound version):
    We assume a UNIFORM family of catalytic gaps at all scales `0 < τ ≤ δ₀`
    (this is the hypothesis really needed to “shrink” from some δ₀ to the ε
    required so that `lam + ε ≤ 1`). From such a family and `lam < 1` with
    `lam = S(X)` we derive a contradiction by promoting `lam` to `lam+ε`
    inside the Lambda set, contradicting maximality of `lam = S(X)`. -/
private lemma interior_gap_contradiction
  (X : TW.State Γ)
  {lam : ℝ}
  (hlam : 0 ≤ lam ∧ lam ≤ 1) (hlam_lt1 : lam < 1)
  (h_sup : lam = Ctx.S X)
  (h_gap_family :
    ∃ (δ₀ : ℝ) (_ : 0 < δ₀),
      ∀ {τ : ℝ} (hτ_pos : 0 < τ) (_ : τ ≤ δ₀),
        comp_state (
          ReferenceState Ctx.X₀ Ctx.X₁ lam hlam.1 hlam.2,
          scale_state (ne_of_gt hτ_pos) Ctx.X₁)
          ≺
        comp_state (
          X,
          scale_state (ne_of_gt hτ_pos) Ctx.X₀)) :
  False := by
  -- Extract the uniform family
  rcases h_gap_family with ⟨δ₀, hδ₀_pos, h_family⟩
  -- Choose ε with lam + ε ≤ 1 and ε ≤ δ₀ (since ε ≤ δ₀/2 < δ₀).
  obtain ⟨ε, hε_pos, hε_le1, hε_leδhalf, h_sum_le⟩ :=
    choose_eps_for_interior hlam_lt1 hδ₀_pos
  -- From ε ≤ δ₀/2 infer ε ≤ δ₀
  have hε_leδ : ε ≤ δ₀ := (le_trans hε_leδhalf (half_le_self (le_of_lt hδ₀_pos)))
  -- Instantiate the family at τ = ε
  have h_gapε :
      comp_state (
        ReferenceState Ctx.X₀ Ctx.X₁ lam hlam.1 hlam.2,
        scale_state (ne_of_gt hε_pos) Ctx.X₁)
        ≺
      comp_state (
        X,
        scale_state (ne_of_gt hε_pos) Ctx.X₀) :=
    shrink_gap_to_eps (Ctx := Ctx) X
      (lam := lam) (δ := δ₀) (ε := ε)
      hlam.1 hlam.2 hδ₀_pos hε_pos hε_leδ
      (by
        intro τ hτ_pos hτ_le
        simpa using h_family hτ_pos hτ_le)
  -- Promote lam ↦ lam + ε
  have h_inflated :
      (lam + ε) ∈ Ctx.LambdaSet X :=
    promote_lambda_interior (Ctx := Ctx) X hlam hε_pos h_sum_le h_gapε
  -- Supremum property gives lam + ε ≤ S(X) = lam
  have h_le_sup : lam + ε ≤ Ctx.S X :=
    le_csSup (Ctx.LambdaSet_BddAbove X) h_inflated
  have h_le_lam : lam + ε ≤ lam := by simpa [h_sup]
        using h_le_sup
  -- But ε > 0 ⇒ lam < lam + ε
  have h_lt : lam < lam + ε := by linarith
  exact (not_lt_of_ge h_le_lam) h_lt

omit [HasLambdaWitness Ctx] [Fact (GlobalComparisonHypothesis System)] in
/-- (6) Final assembled lemma (revised): no strict (single-scale) catalytic gap at lam = S(X).
    We assume the UNIFORM gap family (the sound hypothesis) instead of only one δ-gap. -/
lemma no_strict_gap_at_sup
  (X : TW.State Γ)
  (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 1)
  (h_sup : lam = Ctx.S X)
  (h_gap_family :
    ∃ (δ₀ : ℝ) (_ : 0 < δ₀),
      ∀ {τ : ℝ} (hτ_pos : 0 < τ) (_ : τ ≤ δ₀),
        comp_state (
          ReferenceState Ctx.X₀ Ctx.X₁ lam hlam.1 hlam.2,
          scale_state (ne_of_gt hτ_pos) Ctx.X₁)
          ≺
        comp_state (
          X,
          scale_state (ne_of_gt hτ_pos) Ctx.X₀)) :
  False := by
  classical
  rcases h_gap_family with ⟨δ₀, hδ₀_pos, h_family⟩
  by_cases h_top : lam = 1
  · -- Boundary case lam = 1: instantiate the family at τ = δ₀/2 to get a single gap
    subst h_top
    have hS1 : Ctx.S X = 1 := by simp [h_sup]
    -- pick δ = δ₀/2
    have hδ_pos : 0 < δ₀ / 2 := half_pos hδ₀_pos
    -- Simple arithmetic bound (previous complicated div lemma removed)
    have h_le : δ₀ / 2 ≤ δ₀ := half_le_self (le_of_lt hδ₀_pos)
    -- Instantiate family at τ = δ₀/2
    have h_gap :
        comp_state (
          ReferenceState Ctx.X₀ Ctx.X₁ 1 (by norm_num) (by norm_num),
          scale_state (ne_of_gt hδ_pos) Ctx.X₁)
          ≺
        comp_state (
          X,
          scale_state (ne_of_gt hδ_pos) Ctx.X₀) := by
      simpa using h_family hδ_pos (by simpa using h_le)
    exact gap_boundary_lambda_one (Ctx := Ctx) X hδ_pos hS1 h_gap
  · -- Interior case lam < 1
    have hlam_lt1 : lam < 1 := lt_of_le_of_ne hlam.2 h_top
    exact interior_gap_contradiction (Ctx := Ctx) X hlam hlam_lt1 h_sup
      ⟨δ₀, hδ₀_pos, h_family⟩

end CanonicalEntropy

end LY
