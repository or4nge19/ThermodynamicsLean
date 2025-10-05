/-
Copyright (c) 2025 Matteo Cipollina All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LY.Cancellation

/-!
# Immediate Consequences of the Axioms

This file contains several direct consequences of the core axioms and the
newly proven Cancellation Law. These lemmas correspond to Sections II.B and
II.C of the Lieb-Yngvason paper.

## Main Definitions
- `Comparable`: Two states `X` and `Y` are comparable if `X ≺ Y` or `Y ≺ X`.
- `ComparisonHypothesis`: The assertion that any two states in a given
  system's state space are comparable.
- `StrictlyPrecedes` (`≺≺`): `X ≺ Y` but not `Y ≺ X`.

## Main Results
- **Lemma 2.3**: Properties of the zero system `Z` (or state `0`), showing
  it acts as a neutral element for composition up to `≈`.
- **Lemma 2.4**: Additivity of `≺` and `≈` over composition.
- **Lemma 2.5**: Scaling invariance of `≺` and `≈` for `t > 0`.
- **Lemma 2.6**: Properties of strict accessibility `≺≺`, including a
  generalized cancellation law.
-/

namespace LY

universe u v
variable {System : Type u} [TW : ThermoWorld System]
local infix:50 " ≺ " => TW.le
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X
local infixr:70 " ⊗ " => TW.comp
local infixr:80 " • " => TW.scale

/-!
### Section II.B: Definitions and Immediate Consequences
-/

/-! ### Definitions: Comparability, CH, Strict Accessibility -/

/-- Definition of Comparability -/
def Comparable {Γ₁ Γ₂ : System} (X : TW.State Γ₁) (Y : TW.State Γ₂) : Prop := X ≺ Y ∨ Y ≺ X

/-- The Comparison Hypothesis (CH) for a specific System (State Space). -/
def ComparisonHypothesis (Γ : System) : Prop :=
  ∀ X Y : TW.State Γ, Comparable X Y

/-- Strict Adiabatic Accessibility (≺≺) -/
def StrictlyPrecedes {Γ₁ Γ₂ : System} (X : TW.State Γ₁) (Y : TW.State Γ₂) : Prop :=
  X ≺ Y ∧ ¬(Y ≺ X)

local infix:50 " ≺≺ " => StrictlyPrecedes

/-! ### Section II.C: Immediate Consequences of the Axioms (Lemmas 2.3 - 2.6) -/

/-! #### Lemma 2.3: Properties of the Zero System (Z) -/

/-- Lemma 2.3 (i): (X, 0) ≈ X. This is Axiom CZ. -/
lemma L2_3_i {Γ} (X : TW.State Γ) : comp_state (X, (default : TW.State TW.ZSystem)) ≈ X :=
  TW.comp_ZSystem_is_identity Γ X

/-- Lemma 2.3 (ii): If X ≺ Y then (X, 0) ≺ (Y, 0). -/
lemma L2_3_ii {Γ₁ Γ₂} (X : TW.State Γ₁) (Y : TW.State Γ₂) (h : X ≺ Y) :
    comp_state (X, (default : TW.State TW.ZSystem)) ≺ comp_state (Y, (default : TW.State TW.ZSystem)) := by
  exact TW.A3 h (thermo_le_refl (default : TW.State TW.ZSystem))

/-- Lemma 2.3 (iii): If (X, 0) ≺ (Y, 0) then X ≺ Y. -/
lemma L2_3_iii {Γ₁ Γ₂} (X : TW.State Γ₁) (Y : TW.State Γ₂)
    (h : comp_state (X, (default : TW.State TW.ZSystem)) ≺ comp_state (Y, (default : TW.State TW.ZSystem))) :
    X ≺ Y := by
  exact le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm (L2_3_i X)) h) (L2_3_i Y)

/-! #### Lemma 2.4: Additivity of Equivalence and Accessibility -/

/-- Lemma 2.4 (i): If X₁ ≈ Y₁ and X₂ ≈ Y₂, then (X₁, X₂) ≈ (Y₁, Y₂). -/
lemma L2_4_i {ΓX₁ ΓX₂ ΓY₁ ΓY₂} {X₁ : TW.State ΓX₁} {X₂ : TW.State ΓX₂} {Y₁ : TW.State ΓY₁} {Y₂ : TW.State ΓY₂}
    (h₁ : X₁ ≈ Y₁) (h₂ : X₂ ≈ Y₂) :
    comp_state (X₁, X₂) ≈ comp_state (Y₁, Y₂) := by
  -- Follows directly from A3 (Consistency).
  constructor
  · exact TW.A3 h₁.1 h₂.1
  · exact TW.A3 h₁.2 h₂.2

/-- Lemma 2.4 (ii): If X₁ ≺ Y₁ and X₂ ≺ Y₂, then (X₁, X₂) ≺ (Y₁, Y₂). This is Axiom A3. -/
lemma L2_4_ii {ΓX₁ ΓX₂ ΓY₁ ΓY₂} {X₁ : TW.State ΓX₁} {X₂ : TW.State ΓX₂} {Y₁ : TW.State ΓY₁} {Y₂ : TW.State ΓY₂}
    (h₁ : X₁ ≺ Y₁) (h₂ : X₂ ≺ Y₂) :
    comp_state (X₁, X₂) ≺ comp_state (Y₁, Y₂) :=
  TW.A3 h₁ h₂

/-! #### Lemma 2.5: Scaling of Equivalence and Accessibility -/

/-- Helper Lemma: (1/t)(tX) ≈ X for t > 0. Relies on CS, CEq, C1, CCast.
    This proves that scaling is reversible up to adiabatic equivalence.
    We use the rigorous cast manipulation approach.
-/
lemma inv_scale_equiv {t : ℝ} (ht : 0 < t) {Γ} (X : TW.State Γ) :
    scale_state (one_div_pos.mpr ht).ne' (scale_state ht.ne' X) ≈ X := by
  have h_inv_t_pos : 0 < 1 / t := one_div_pos.mpr ht
  let tX := scale_state ht.ne' X
  let inv_tX := scale_state h_inv_t_pos.ne' tX
  -- Define the relevant states and system equalities.
  let h_mul_ne : (1 / t * t) ≠ 0 := mul_ne_zero h_inv_t_pos.ne' ht.ne'
  let X_mul := scale_state h_mul_ne X            -- ((1/t)*t)•X : State ((1/t)*t • Γ)
  let X_1   := scale_state (by norm_num : (1:ℝ) ≠ 0) X  -- 1•X     : State (1 • Γ)
  have h_eq_one : (1 / t) * t = 1 := by field_simp [ht.ne']
  -- System equalities used for casts.
  let E_smul := TW.smul_smul (1 / t) t Γ                 -- ((1/t)*t)•Γ = (1/t)•(t•Γ)
  let E_eq   := congrArg (fun r => TW.scale r Γ) h_eq_one -- ((1/t)*t)•Γ = 1•Γ
  let E_one  := TW.one_smul Γ                             -- 1•Γ = Γ
  -- Apply Coherence Axioms.
  -- CS: Cast(E_smul) X_mul ≈ inv_tX.
  have h_CS := TW.scale_coherence h_inv_t_pos.ne' ht.ne' (Γ := Γ) (X := X)
  -- CEq: Cast(E_eq) X_mul ≈ X_1.
  have h_CEq := TW.scale_eq_coherence (Γ := Γ) (X := X) h_eq_one h_mul_ne
  -- C1: Cast(E_one) X_1 ≈ X.
  have h_C1 := TW.one_smul_coherence (Γ := Γ) (X := X)
  -- 1) inv_tX ≈ Cast(E_smul) X_mul (by symmetry of h_CS).
  have h1 : inv_tX ≈ (Equiv.cast (congrArg TW.State E_smul) X_mul) := by
    simpa using (thermo_equiv_symm h_CS)
  -- 2) From h_CEq: Cast(E_eq) X_mul ≈ X_1.
  --    Cast both sides by E_eq.symm to obtain: X_mul ≈ Cast(E_eq.symm) X_1.
  have h_CEq_inv : X_mul ≈ Equiv.cast (congrArg TW.State E_eq.symm) X_1 := by
    have h_symm : X_1 ≈ (Equiv.cast (congrArg TW.State E_eq) X_mul) :=
      thermo_equiv_symm h_CEq
    have h_casted :=
      cast_preserves_equiv_simple (Γ₁ := TW.scale 1 Γ) (Γ₂ := TW.scale ((1 / t) * t) Γ)
        E_eq.symm h_symm
    -- RHS simplifies: Cast(E_eq.symm) (Cast(E_eq) X_mul) = X_mul
    simpa using (thermo_equiv_symm h_casted)
  -- 3) Transport h_CEq_inv along E_smul:
  --    Cast(E_smul) X_mul ≈ Cast(E_smul) (Cast(E_eq.symm) X_1)
  --    which definitionally is Cast(E_eq.symm.trans E_smul) X_1.
  have h12 :
      (Equiv.cast (congrArg TW.State E_smul) X_mul)
        ≈ (Equiv.cast (congrArg TW.State (E_eq.symm.trans E_smul)) X_1) := by
    have h := cast_preserves_equiv_simple
                (Γ₁ := TW.scale ((1 / t) * t) Γ)
                (Γ₂ := TW.scale (1 / t) (TW.scale t Γ))
                E_smul h_CEq_inv
    simpa using h
  -- 4) From h_C1: Cast(E_one) X_1 ≈ X.
  --    Cast by (E_eq.symm.trans E_smul) to get:
  --    Cast(E_eq.symm.trans E_smul) X_1 ≈ Cast(E_one.symm.trans (E_eq.symm.trans E_smul)) X.
  have h_C1_inv : X_1 ≈ Equiv.cast (congrArg TW.State E_one.symm) X := by
    -- Cast both sides of h_C1 by E_one.symm and simplify.
    have h_symm : X ≈ (Equiv.cast (congrArg TW.State E_one) X_1) := thermo_equiv_symm h_C1
    have h_casted :=
      cast_preserves_equiv_simple (Γ₁ := Γ) (Γ₂ := TW.scale 1 Γ) E_one.symm h_symm
    simpa using (thermo_equiv_symm h_casted)
  have h34 :=
    cast_preserves_equiv_simple
      (Γ₁ := TW.scale 1 Γ)
      (Γ₂ := TW.scale (1 / t) (TW.scale t Γ))
      (E_eq.symm.trans E_smul) h_C1_inv
  have h_final :
      (Equiv.cast (congrArg TW.State (E_eq.symm.trans E_smul)) X_1)
        ≈ (Equiv.cast (congrArg TW.State (E_one.symm.trans (E_eq.symm.trans E_smul))) X) := by
    simpa using h34
  -- Chain: inv_tX ≈ Cast(E_smul) X_mul ≈ Cast(E_eq.symm.trans E_smul) X_1
  --        ≈ Cast(E_one.symm.trans (E_eq.symm.trans E_smul)) X ≈ X.
  have h_chain := thermo_equiv_trans' h1 (thermo_equiv_trans' h12 h_final)
  have h_cast_id := TW.state_equiv_coherence (E_one.symm.trans (E_eq.symm.trans E_smul)) X
  exact thermo_equiv_trans' h_chain (id (And.symm h_cast_id))

/-- Lemma 2.5 (i): For t > 0, X ≈ Y if and only if tX ≈ tY. -/
lemma L2_5_i {ΓX ΓY} {X : TW.State ΓX} {Y : TW.State ΓY} {t : ℝ} (ht : 0 < t) :
    (X ≈ Y) ↔ (scale_state ht.ne' X ≈ scale_state ht.ne' Y) := by
  constructor
  · -- (⇒) If X ≈ Y, then tX ≈ tY. Follows from A4.
    intro h
    constructor
    · exact TW.A4 ht h.1
    · exact TW.A4 ht h.2
  · -- (⇐) If tX ≈ tY, then X ≈ Y.
    intro h_scaled
    -- Use A4 with inverse scaling 1/t.
    have h_inv_t_pos : 0 < 1/t := one_div_pos.mpr ht
    have h_inv_fwd := TW.A4 h_inv_t_pos h_scaled.1
    have h_inv_bwd := TW.A4 h_inv_t_pos h_scaled.2
    -- Use the helper lemma: (1/t)(tX) ≈ X.
    have h_X_equiv := inv_scale_equiv ht X
    have h_Y_equiv := inv_scale_equiv ht Y
    -- Combine: X ≈ (1/t)(tX) ≺ (1/t)(tY) ≈ Y.
    constructor
    · exact le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_X_equiv) h_inv_fwd) h_Y_equiv
    · exact le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_Y_equiv) h_inv_bwd) h_X_equiv

/-- Lemma 2.5 (ii): For t > 0, X ≺ Y if and only if tX ≺ tY. -/
lemma L2_5_ii {ΓX ΓY} {X : TW.State ΓX} {Y : TW.State ΓY} {t : ℝ} (ht : 0 < t) :
    (X ≺ Y) ↔ (scale_state ht.ne' X ≺ scale_state ht.ne' Y) := by
  constructor
  · exact TW.A4 ht
  · -- (⇐) If tX ≺ tY, then X ≺ Y. (Proof structure identical to L2_5_i (⇐)).
    intro h_scaled
    have h_inv_t_pos : 0 < 1/t := one_div_pos.mpr ht
    have h_inv_fwd := TW.A4 h_inv_t_pos h_scaled
    have h_X_equiv := inv_scale_equiv ht X
    have h_Y_equiv := inv_scale_equiv ht Y
    exact le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_X_equiv) h_inv_fwd) h_Y_equiv

/-! #### Lemma 2.6: Strict Accessibility Properties and Generalized Cancellation -/

/-- Transitivity of ≺≺ with ≺. (X ≺≺ Y and Y ≺ Z ⇒ X ≺≺ Z) -/
lemma strict_le_trans_le {Γ₁ Γ₂ Γ₃ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂} {Z : TW.State Γ₃}
    (h₁ : X ≺≺ Y) (h₂ : Y ≺ Z) : X ≺≺ Z := by
  refine ⟨thermo_le_trans h₁.1 h₂, fun h_ZX => ?_⟩
  -- If Z ≺ X, then Y ≺ Z ≺ X, so Y ≺ X. Contradiction.
  exact h₁.2 (thermo_le_trans h₂ h_ZX)

/-- Transitivity of ≺ with ≺≺. (X ≺ Y and Y ≺≺ Z ⇒ X ≺≺ Z) -/
lemma le_trans_strict_le {Γ₁ Γ₂ Γ₃ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂} {Z : TW.State Γ₃}
    (h₁ : X ≺ Y) (h₂ : Y ≺≺ Z) : X ≺≺ Z := by
  refine ⟨thermo_le_trans h₁ h₂.1, fun h_ZX => ?_⟩
  -- If Z ≺ X, then Z ≺ X ≺ Y. So Z ≺ Y. Contradiction.
  exact h₂.2 (thermo_le_trans h_ZX h₁)

/-- Lemma 2.6 (i): If X ≺≺ Y then (X, Z) ≺≺ (Y, Z).
    This relies on the Cancellation Law (Theorem 2.1).
-/
lemma L2_6_i {ΓX ΓY ΓZ} {X : TW.State ΓX} {Y : TW.State ΓY} (Z : TW.State ΓZ)
    (h : X ≺≺ Y) : comp_state (X, Z) ≺≺ comp_state (Y, Z) := by
  rcases h with ⟨h_le, h_strict⟩
  -- 1. Prove (X, Z) ≺ (Y, Z). (A3).
  have h_comp_le := TW.A3 h_le (thermo_le_refl Z)
  -- 2. Prove ¬((Y, Z) ≺ (X, Z)).
  have h_comp_strict : ¬(comp_state (Y, Z) ≺ comp_state (X, Z)) := by
    -- Assume (Y, Z) ≺ (X, Z) for contradiction.
    intro h_contra
    -- Apply the Cancellation Law.
    have h_cancel := CancellationLaw Y X Z h_contra
    -- This implies Y ≺ X, which contradicts X ≺≺ Y.
    contradiction
  exact ⟨h_comp_le, h_comp_strict⟩

/-- Helper: Cancellation on the Left. If (X, Z) ≺ (X, W) then Z ≺ W. -/
lemma cancellation_left {ΓX ΓZ ΓW} (X : TW.State ΓX) (Z : TW.State ΓZ) (W : TW.State ΓW)
    (h_main : comp_state (X, Z) ≺ comp_state (X, W)) : Z ≺ W := by
  -- 1. Use Commutativity Coherence (CC). (X, Z) ≈ (Z, X) and (X, W) ≈ (W, X).
  have h_comm_L := comp_comm_equiv_clean X Z
  have h_comm_R := comp_comm_equiv_clean X W
  -- 2. (Z, X) ≈ (X, Z) ≺ (X, W) ≈ (W, X).
  have h_trans := le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_comm_L) h_main) h_comm_R
  -- 3. Apply Cancellation Law (on the right).
  exact CancellationLaw Z W X h_trans

/-- Lemma 2.6 (ii): If X₁ ≺ Y₁ and X₂ ≺≺ Y₂, then (X₁, X₂) ≺≺ (Y₁, Y₂).
-/
lemma L2_6_ii {ΓX₁ ΓY₁ ΓX₂ ΓY₂}
    {X₁ : TW.State ΓX₁} {Y₁ : TW.State ΓY₁} {X₂ : TW.State ΓX₂} {Y₂ : TW.State ΓY₂}
    (h₁ : X₁ ≺ Y₁) (h₂ : X₂ ≺≺ Y₂) :
    comp_state (X₁, X₂) ≺≺ comp_state (Y₁, Y₂) := by
  -- 1. (X₁, X₂) ≺ (Y₁, Y₂). (A3).
  have h_le := TW.A3 h₁ h₂.1
  -- 2. ¬((Y₁, Y₂) ≺ (X₁, X₂)).
  have h_strict : ¬(comp_state (Y₁, Y₂) ≺ comp_state (X₁, X₂)) := by
    intro h_contra
    -- Assume (Y₁, Y₂) ≺ (X₁, X₂). We derive a contradiction.
    -- Consider the intermediate state (Y₁, X₂).
    -- We use the fact that X₂ ≺≺ Y₂ implies (Y₁, X₂) ≺≺ (Y₁, Y₂).
    -- This requires L2.6 (i) applied on the left, which needs commutativity.
    -- (X₂, Y₁) ≺≺ (Y₂, Y₁) by L2.6 (i).
    have step1_comm := L2_6_i Y₁ h₂
    -- We derive the strict relation (Y₁, X₂) ≺≺ (Y₁, Y₂).
    have step1 : comp_state (Y₁, X₂) ≺≺ comp_state (Y₁, Y₂) := by
      -- (Y₁, X₂) ≈ (X₂, Y₁) ≺≺ (Y₂, Y₁) ≈ (Y₁, Y₂).
      have h_comm_YX := comp_comm_equiv_clean Y₁ X₂
      have h_comm_YY := comp_comm_equiv_clean Y₁ Y₂
      have h_le' :=
        le_of_le_equiv (le_of_equiv_le h_comm_YX step1_comm.1) (thermo_equiv_symm h_comm_YY)
      have h_strict' : ¬(comp_state (Y₁, Y₂) ≺ comp_state (Y₁, X₂)) := by
        intro hc
        have hc' := le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_comm_YY) hc) h_comm_YX
        exact step1_comm.2 hc'
      exact ⟨h_le', h_strict'⟩
    -- Combine with h_contra: (Y₁, X₂) ≺≺ (Y₁, Y₂) ≺ (X₁, X₂).
    -- (Y₁, X₂) ≺ (X₁, X₂).
    have chain := thermo_le_trans step1.1 h_contra
    -- Apply Cancellation Law (Right): Y₁ ≺ X₁.
    have cancel1 := CancellationLaw Y₁ X₁ X₂ chain
    -- Now we know Y₁ ≺ X₁. Combined with h₁ (X₁ ≺ Y₁), we have X₁ ≈ Y₁.
    have equiv1 : X₁ ≈ Y₁ := ⟨h₁, cancel1⟩
    -- If X₁ ≈ Y₁, then (X₁, X₂) ≈ (Y₁, X₂).
    have comp_equiv1 : comp_state (X₁, X₂) ≈ comp_state (Y₁, X₂) := L2_4_i equiv1 (thermo_equiv_refl X₂)
    -- Chain: (Y₁, Y₂) ≺ (X₁, X₂) ≈ (Y₁, X₂).
    have chain2 := le_of_le_equiv h_contra comp_equiv1
    -- (Y₁, Y₂) ≺ (Y₁, X₂).
    -- Apply Cancellation Law (Left): Y₂ ≺ X₂.
    have cancel2 := cancellation_left Y₁ Y₂ X₂ chain2
    -- This contradicts X₂ ≺≺ Y₂.
    exact h₂.2 cancel2
  exact ⟨h_le, h_strict⟩

/-- Lemma 2.6 (iii): Scaling preserves strict accessibility.
    If X ≺≺ Y and t > 0, then tX ≺≺ tY.
-/
lemma L2_6_iii {ΓX ΓY} {X : TW.State ΓX} {Y : TW.State ΓY} (t : ℝ) (ht : 0 < t)
    (h : X ≺≺ Y) :
    scale_state ht.ne' X ≺≺ scale_state ht.ne' Y := by
  -- Follows directly from L2.5 (ii).
  rw [StrictlyPrecedes]
  constructor
  · -- show tX ≺ tY from X ≺ Y
    exact (L2_5_ii ht).1 h.1
  · intro h_YX_scaled
    -- If tY ≺ tX, then Y ≺ X, contradicting strictness.
    exact h.2 ((L2_5_ii ht).2 h_YX_scaled)

/-- Generalized Cancellation Law (Often included in discussions around Lemma 2.6).
    If (X₁, Z₁) ≺ (X₂, Z₂) and X₂ ≺ X₁, then Z₁ ≺ Z₂. -/
lemma generalized_cancellation {ΓX₁ ΓX₂ ΓZ₁ ΓZ₂}
    (X₁ : TW.State ΓX₁) (X₂ : TW.State ΓX₂) (Z₁ : TW.State ΓZ₁) (Z₂ : TW.State ΓZ₂)
    (h_main : comp_state (X₁, Z₁) ≺ comp_state (X₂, Z₂))
    (h_X : X₂ ≺ X₁) : Z₁ ≺ Z₂ := by
  -- 1. Use A3 (Consistency) with X₂ ≺ X₁ and Z₁ ≺ Z₁ (A1).
  -- (X₂, Z₁) ≺ (X₁, Z₁)
  have h_step1 := TW.A3 h_X (thermo_le_refl Z₁)
  -- 2. Use Transitivity (A2): (X₂, Z₁) ≺ (X₁, Z₁) ≺ (X₂, Z₂).
  have h_step2 := thermo_le_trans h_step1 h_main
  -- 3. Apply Cancellation Left.
  exact cancellation_left X₂ Z₁ Z₂ h_step2

end LY
