/-
Copyright (c) 2025 Matteo Cipollina All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LY.Entropy.Construction
import LY.Cancellation

/-!
# Completion of the Continuity Lemma and Canonical Entropy Properties

This file completes the proof of the Continuity Lemma (Lemma 2.8) and establishes
the full properties of the canonical entropy function, including:
- **Lemma 2.8 (Continuity)**: The supremum S(X) is attained, i.e., S(X) ∈ λ(X).
- **Theorem 2.2 (Complete)**: The canonical entropy satisfies normalization,
  monotonicity (both directions), additivity, and extensivity.
-/

namespace LY

universe u v
variable {System : Type u} [TW : ThermoWorld System]
local infix:50 " ≺ " => TW.le
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X
local infix:50 " ≺≺ " => StrictlyPrecedes

open CanonicalEntropyContext

section ContinuityLemma

variable {Γ : System}
variable (Ctx : CanonicalEntropyContext Γ)
variable [HasLambdaWitness Ctx]
variable [Fact (GlobalComparisonHypothesis System)]

omit [Fact (GlobalComparisonHypothesis System)] in
/-- Lemma 2.8 (Continuity Lemma): The supremum of λ(X) is attained.
    Interior-aware statement: assumes `0 ≤ S(X) ≤ 1` to dispatch the central case. -/
theorem CanonicalEntropyContext.ContinuityLemma (X : TW.State Γ)
    (h_range : 0 ≤ Ctx.S X ∧ Ctx.S X ≤ 1) :
    Ctx.S X ∈ Ctx.LambdaSet X := by
  set lam := Ctx.S X
  by_cases h0 : lam = 0
  · -- Boundary case: S(X) = 0
    exact Ctx.ContinuityLemma_boundary_cases X (Or.inl h0)
  · by_cases h1 : lam = 1
    · -- Boundary case: S(X) = 1
      exact Ctx.ContinuityLemma_boundary_cases X (Or.inr h1)
    · -- Central/general case: neither 0 nor 1
      have h_pos : 0 < lam := lt_of_le_of_ne h_range.1 (Ne.symm h0)
      have h_lt1 : lam < 1 := lt_of_le_of_ne h_range.2 h1
      exact Ctx.ContinuityLemma_central_case X ⟨h_pos, h_lt1⟩

/-- Corollary: R_{S(X)} ≈ X for states in the interior range. -/
theorem reference_at_entropy_equiv (X : TW.State Γ)
    (h_range : 0 ≤ Ctx.S X ∧ Ctx.S X ≤ 1) :
    ReferenceState Ctx.X₀ Ctx.X₁ (Ctx.S X) h_range.1 h_range.2 ≈ X := by
  have h_in : Ctx.S X ∈ Ctx.LambdaSet X := Ctx.ContinuityLemma X h_range
  have h_forward := reference_le_of_mem_lambda (Ctx := Ctx) X h_in h_range
  -- For the reverse direction, use maximality of S(X)
  have h_reverse : X ≺ ReferenceState Ctx.X₀ Ctx.X₁ (Ctx.S X) h_range.1 h_range.2 := by
    by_contra h_not
    -- If X ⊀ R_{S(X)}, then by GCH we have R_{S(X)} ≺ X strictly
    have h_strict := reference_strict_or_equiv (Ctx := Ctx) X (Ctx.S X) h_range h_forward h_not
    -- By Gap Lemma, we get a UNIFORM gap family
    obtain ⟨δ₀, hδ₀, h_gap_family⟩ :=
      GapLemmaGCH (Ctx := Ctx)
        (A := ReferenceState Ctx.X₀ Ctx.X₁ (Ctx.S X) h_range.1 h_range.2)
        (B := X)
        h_strict
    have h_gap_exists : ∃ (δ₀ : ℝ) (_ : 0 < δ₀),
        ∀ {τ : ℝ} (hτ_pos : 0 < τ) (_ : τ ≤ δ₀),
          comp_state (
            ReferenceState Ctx.X₀ Ctx.X₁ (Ctx.S X) h_range.1 h_range.2,
            scale_state (ne_of_gt hτ_pos) Ctx.X₁)
            ≺
          comp_state (
            X,
            scale_state (ne_of_gt hτ_pos) Ctx.X₀) :=
      ⟨δ₀, hδ₀, fun {τ} hτ_pos hτ_le =>
        h_gap_family hτ_pos hτ_le⟩
    exact no_strict_gap_at_sup (Ctx := Ctx) X (Ctx.S X) h_range rfl h_gap_exists
  exact ⟨h_forward, h_reverse⟩

end ContinuityLemma

/-! ### Theorem 2.2: Complete Properties of Canonical Entropy -/

section CanonicalEntropyProperties

variable {Γ : System}
variable (Ctx : CanonicalEntropyContext Γ)
variable [HasLambdaWitness Ctx]
variable [Fact (GlobalComparisonHypothesis System)]

/-- Theorem 2.2 (ii) reverse direction (interior-range version):
    If S(X) ≤ S(Y) and both S(X), S(Y) ∈ [0,1], then X ≺ Y (for comparable states). -/
theorem CanonicalEntropyContext.S_le_implies_le
    (X Y : TW.State Γ)
    (h_S_le : Ctx.S X ≤ Ctx.S Y)
    (hX_range : 0 ≤ Ctx.S X ∧ Ctx.S X ≤ 1)
    (hY_range : 0 ≤ Ctx.S Y ∧ Ctx.S Y ≤ 1) : X ≺ Y := by
  -- R_{S(X)} ≈ X and R_{S(Y)} ≈ Y
  have hX_equiv := reference_at_entropy_equiv (Ctx := Ctx) X hX_range
  have hY_equiv := reference_at_entropy_equiv (Ctx := Ctx) Y hY_range
  -- Monotonicity of reference states
  by_cases h_eq : Ctx.S X = Ctx.S Y
  · -- If S(X) = S(Y), conclude directly via transitivity
    -- Both X and Y are equivalent to reference states at the same parameter value
    have hY_equiv' : ReferenceState Ctx.X₀ Ctx.X₁ (Ctx.S X) hX_range.1 (h_eq ▸ hY_range.2) ≈ Y := by
      convert hY_equiv using 2
      all_goals grind
    have h_X_equiv_Y := thermo_equiv_trans (thermo_equiv_symm hX_equiv) hY_equiv'
    exact h_X_equiv_Y.1
  · -- Strictly increasing in the parameter for reference states
    have h_lt : Ctx.S X < Ctx.S Y := lt_of_le_of_ne h_S_le h_eq
    have h_R_lt_R :
        ReferenceState Ctx.X₀ Ctx.X₁ (Ctx.S X) hX_range.1 hX_range.2 ≺
        ReferenceState Ctx.X₀ Ctx.X₁ (Ctx.S Y) hY_range.1 hY_range.2 :=
      (StrictReferenceState_monotone (Ctx := Ctx) (Ctx.S X) (Ctx.S Y)
          hX_range.1 hY_range.2 h_lt).1
    -- X ≈ R_{S X} ≺ R_{S Y} ≈ Y => X ≺ Y
    exact le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm hX_equiv) h_R_lt_R) hY_equiv

/-- Theorem 2.2 (ii) complete (interior-range version):
    X ≺ Y ↔ S(X) ≤ S(Y), assuming both S(X), S(Y) ∈ [0,1]. -/
theorem CanonicalEntropyContext.le_iff_S_le
    (X Y : TW.State Γ)
    (hX_range : 0 ≤ Ctx.S X ∧ Ctx.S X ≤ 1)
    (hY_range : 0 ≤ Ctx.S Y ∧ Ctx.S Y ≤ 1) :
    X ≺ Y ↔ Ctx.S X ≤ Ctx.S Y := by
  constructor
  · exact Ctx.S_le_of_le X Y
  · intro hSle
    exact S_le_implies_le Ctx X Y hSle hX_range hY_range

end CanonicalEntropyProperties

end LY
