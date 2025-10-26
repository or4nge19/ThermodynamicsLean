/-
Copyright (c) 2025 Matteo Cipollina All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LY.Axioms
import LY.Algebra

/-!
# The Recombination Lemma

This file builds the proof of the Recombination Lemma, a main result derived
from the core axioms. It states that for scalars `a, b > 0`, the state `(a+b)•X`
is adiabatically equivalent to the compound state `(a•X, b•X)`.

The proof is constructed in three main steps:
1.  Apply Axiom A5 (Splitting/Recombination) to the scaled state `(a+b)•X`.
2.  Use coherence axioms to transport the resulting components along system
    equalities, such as `t•(s•Γ) = (t*s)•Γ`.
3.  Bridge the casted components to their canonical forms `a•X` and `b•X`.

The file also introduces `gscale_state`, a generalized scaling operation that
handles scaling by zero, and proves the `generalized_recombination_lemma`
which extends the result to non-negative scalars `a, b ≥ 0`.
-/

namespace LY

universe u v
variable {System : Type u} [TW : ThermoWorld System]
local infix:50 " ≺ " => TW.le
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X
local infixr:70 " ⊗ " => TW.comp
local infixr:80 " • " => TW.scale

/-! ### The Recombination Lemma (Generalization of A5)
We prove that for a > 0, b > 0, (a+b)•X ≈ (a•X, b•X).
-/

/-- Step 1: Apply A5 to the scaled state (a+b)•X. -/
lemma split_scaled_sum_A5_equiv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {Γ} (X : TW.State Γ) :
    let t := a / (a + b)
    let h_U_ne := (add_pos ha hb).ne'
    let U_state := scale_state h_U_ne X
    let hden_pos : 0 < a + b := add_pos ha hb
    let ht : 0 < t ∧ t < 1 := by
      refine ⟨div_pos ha hden_pos, (div_lt_one hden_pos).mpr (by linarith)⟩
    U_state ≈ comp_state (
      (TW.state_of_scale_equiv (by exact (ne_of_gt ht.1))).symm U_state,
      (TW.state_of_scale_equiv (by linarith : 1 - t ≠ 0)).symm U_state
    ) := by
  intros t h_U_ne U_state hden_pos ht
  simpa [comp_state] using (TW.A5 U_state ht)

/-- Step 2: Transport the split components along the system equalities derived from smul_smul.
-/
lemma transport_split_to_scalars_equiv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {Γ} (X : TW.State Γ) :
    let t := a / (a + b)
    let hden_pos : 0 < a + b := add_pos ha hb
    let hden_ne := hden_pos.ne'
    let ht : 0 < t ∧ t < 1 := by
      refine ⟨div_pos ha hden_pos, (div_lt_one hden_pos).mpr (by linarith)⟩
    let U_state := scale_state hden_ne X
    -- A = t•U_state, B = (1-t)•U_state
    let A := scale_state ht.1.ne' U_state
    let B := scale_state (one_minus_ne_of_ht ht) U_state
    -- System equality for A: t•((a+b)•Γ) = a•Γ
    let h_a_smul : TW.scale t (TW.scale (a + b) Γ) = TW.scale a Γ := by
      rw [←TW.smul_smul]; congr 1; dsimp [t]; field_simp [hden_ne]
    let h_b_smul : TW.scale (1 - t) (TW.scale (a + b) Γ) = TW.scale b Γ := by
      rw [←TW.smul_smul]; congr 1; dsimp [t]; field_simp [hden_ne]; ring
    comp_state (A, B)
      ≈ comp_state (
          (Equiv.cast (congrArg TW.State h_a_smul) A),
          (Equiv.cast (congrArg TW.State h_b_smul) B)
        ) := by
  intros t hden_pos hden_ne ht U_state A B h_a_smul h_b_smul
  -- Apply CCast (state_equiv_coherence) to A and B.
  have h_cast_A : A ≈ (Equiv.cast (congrArg TW.State h_a_smul) A) :=
    TW.state_equiv_coherence h_a_smul A
  have h_cast_B : B ≈ (Equiv.cast (congrArg TW.State h_b_smul) B) :=
    TW.state_equiv_coherence h_b_smul B
  -- Apply A3 (Consistency).
  exact ⟨TW.A3 h_cast_A.1 h_cast_B.1, TW.A3 h_cast_A.2 h_cast_B.2⟩

/-- Step 3: Bridge from the casted split components to the canonical `a•X` and `b•X`.
    This relies on the coherence axioms CS (Scale Coherence) and CEq (Equal Scaling Coherence).
-/
lemma casted_split_to_canonical_equiv
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {Γ} (X : TW.State Γ) :
    let t := a / (a + b)
    let s := a + b
    let hden_pos := add_pos ha hb
    let hs_ne := hden_pos.ne'
    let ht_bounds : 0 < t ∧ t < 1 := by
      refine ⟨div_pos ha hden_pos, (div_lt_one hden_pos).mpr (by linarith)⟩
    let ht_ne := ht_bounds.1.ne'
    let h1mt_ne := one_minus_ne_of_ht ht_bounds
    let U_state := scale_state hs_ne X
    let A := scale_state ht_ne U_state
    let B := scale_state h1mt_ne U_state
    let h_a_smul : TW.scale t (TW.scale s Γ) = TW.scale a Γ := by
      rw [←TW.smul_smul]; congr 1; dsimp [t, s]; field_simp [hs_ne]
    let h_b_smul : TW.scale (1-t) (TW.scale s Γ) = TW.scale b Γ := by
      rw [←TW.smul_smul]; congr 1; dsimp [t, s]; field_simp [hs_ne]; ring
    comp_state (
      (Equiv.cast (congrArg TW.State h_a_smul) A),
      (Equiv.cast (congrArg TW.State h_b_smul) B)
    )
      ≈ comp_state (scale_state ha.ne' X, scale_state hb.ne' X) := by
  intros t s hden_pos hs_ne ht_bounds ht_ne h1mt_ne U_state A B h_a_smul h_b_smul
  -- Helper proving: cast(h_c_smul) C_state ≈ c•X, where C_state = t'•(s•X) and t'*s = c.
  let component_proof :=
    fun (t' c : ℝ) (ht'_ne : t' ≠ 0) (h_mul_c : t' * s = c) (hc_ne : c ≠ 0)
        (h_c_smul : TW.scale t' (TW.scale s Γ) = TW.scale c Γ)
        (C_state : TW.State (TW.scale t' (TW.scale s Γ)))
        (hC_def : C_state = scale_state ht'_ne (scale_state hs_ne X)) =>
    let X_mul : TW.State (TW.scale (t' * s) Γ) := scale_state (mul_ne_zero ht'_ne hs_ne) X
    let X_c   : TW.State (TW.scale c Γ)         := scale_state hc_ne X
    let E_smul := TW.smul_smul t' s Γ                 -- (t'*s)•Γ = t'•(s•Γ)
    let E_eq   := congrArg (fun r : ℝ => TW.scale r Γ) h_mul_c -- (t'*s)•Γ = c•Γ
    -- 1) CS coherence: C_state ≈ cast(E_smul) X_mul
    have h_CS : C_state ≈ Equiv.cast (congrArg TW.State E_smul) X_mul := by
      -- scale_coherence gives X_ts ≈ cast(E_smul) X_mul; rewrite X_ts and X_mul
      simpa [hC_def, X_mul, E_smul]
        using (thermo_equiv_symm (TW.scale_coherence ht'_ne hs_ne (Γ := Γ) (X := X)))
    -- 2) Move CS to the (E_smul.symm)-casted form
    have h_CS_inv0 := cast_preserves_equiv_simple (Γ₁ := TW.scale t' (TW.scale s Γ))
                          (Γ₂ := TW.scale (t' * s) Γ) E_smul.symm h_CS
    have h_CS_inv : Equiv.cast (congrArg TW.State E_smul.symm) C_state ≈ X_mul := by
      -- RHS simplifies as cast(E_smul.symm) ∘ cast(E_smul) = id
      have h_RHS_def : Equiv.cast (congrArg TW.State E_smul.symm)
                            (Equiv.cast (congrArg TW.State E_smul) X_mul) = X_mul := by simp
      simpa [h_RHS_def] using h_CS_inv0
    -- 3) CEq coherence: cast(E_eq) X_mul ≈ X_c
    have h_CEq : Equiv.cast (congrArg TW.State E_eq) X_mul ≈ X_c := by
      simpa [X_mul, X_c, E_eq] using
        (TW.scale_eq_coherence (Γ := Γ) h_mul_c (mul_ne_zero ht'_ne hs_ne) (X := X))
    -- 4) Cast with E_eq and compose with CEq
    have h_casted := cast_preserves_equiv_simple (Γ₁ := TW.scale (t' * s) Γ)
                        (Γ₂ := TW.scale c Γ) E_eq h_CS_inv
    have h_chain : Equiv.cast (congrArg TW.State E_eq)
                      (Equiv.cast (congrArg TW.State E_smul.symm) C_state) ≈ X_c :=
      thermo_equiv_trans' h_casted h_CEq
    -- 5) Identify the composed cast on the left with cast(h_c_smul)
    have h_eq_comp : h_c_smul = E_smul.symm.trans E_eq := by rfl
    have h_LHS_def :
        Equiv.cast (congrArg TW.State h_c_smul) C_state =
        Equiv.cast (congrArg TW.State E_eq)
          (Equiv.cast (congrArg TW.State E_smul.symm) C_state) := by
      simp
    -- Conclude for this component
    show Equiv.cast (congrArg TW.State h_c_smul) C_state ≈ X_c from
      by
        -- rewrite LHS; RHS already X_c
        simpa [h_LHS_def] using h_chain
  -- Apply to Component A: t' = t, c = a, C_state = A
  have h_comp_A : Equiv.cast (congrArg TW.State h_a_smul) A ≈ scale_state ha.ne' X := by
    refine component_proof t a ht_ne (by dsimp [t, s]; field_simp [hs_ne]) ha.ne' h_a_smul A ?hAdef
    -- A = t•((a+b)•X)
    dsimp [A, U_state]
  -- Apply to Component B: t' = 1 - t, c = b, C_state = B
  have h_comp_B : Equiv.cast (congrArg TW.State h_b_smul) B ≈ scale_state hb.ne' X := by
    let t' := 1 - t
    refine component_proof t' b h1mt_ne (by dsimp [t', t, s]; field_simp [hs_ne]; ring) hb.ne' h_b_smul B ?hBdef
    -- B = (1-t)•((a+b)•X)
    dsimp [B, U_state, t']
  -- Combine the two components via A3 (Consistency)
  exact ⟨TW.A3 h_comp_A.1 h_comp_B.1, TW.A3 h_comp_A.2 h_comp_B.2⟩

/-- The Recombination Lemma: (a+b)•X ≈ (a•X, b•X) for a>0, b>0. -/
lemma recombination_lemma {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {Γ} (X : TW.State Γ) :
    scale_state (add_pos ha hb).ne' X ≈ comp_state (scale_state ha.ne' X, scale_state hb.ne' X) := by
  have h_split := split_scaled_sum_A5_equiv ha hb (Γ := Γ) X
  have h_transport := transport_split_to_scalars_equiv ha hb (Γ := Γ) X
  have h_canon := casted_split_to_canonical_equiv ha hb (Γ := Γ) X
  exact thermo_equiv_trans' h_split (thermo_equiv_trans' h_transport h_canon)

/-! ### Generalized Scaling and Recombination
We extend the framework to allow scaling by zero.
-/

/-- Generalized scaling that handles t=0 by mapping to the Zero System state. -/
noncomputable def gscale_state {t : ℝ} (ht_nonneg : 0 ≤ t) {Γ} (X : TW.State Γ) :
    TW.State (t • Γ) :=
  if ht_pos : 0 < t then
    scale_state ht_pos.ne' X
  else
    have h_t_zero : t = 0 := le_antisymm (le_of_not_gt ht_pos) ht_nonneg
    have h_sys_eq : t • Γ = TW.ZSystem := by simp [h_t_zero, TW.scale_zero_is_ZSystem]
    (Equiv.cast (congrArg TW.State h_sys_eq)).symm TW.State_ZSystem_is_Unit.default

/-! ### Generalized Scaling Lemmas -/

@[simp] lemma gscale_state_pos {t : ℝ} (ht_nonneg : 0 ≤ t) (ht_pos : 0 < t) {Γ}
    (X : TW.State Γ) :
    gscale_state ht_nonneg X = scale_state ht_pos.ne' X := by
  simp [gscale_state, ht_pos]

@[simp] lemma gscale_state_zero {Γ} (X : TW.State Γ) :
    gscale_state (show 0 ≤ (0:ℝ) by simp) X
      = (Equiv.cast (congrArg TW.State (by simp [TW.scale_zero_is_ZSystem]))).symm
          (TW.State_ZSystem_is_Unit.default) := by
  simp [gscale_state]

/-- Proof-irrelevance for the nonneg proof in gscale_state. -/
@[simp] lemma gscale_state_proof_irrel {t : ℝ} {Γ} (h1 h2 : 0 ≤ t) (X : TW.State Γ) :
    gscale_state (System := System) h1 X = gscale_state (System := System) h2 X := by
  classical
  by_cases ht_pos : 0 < t
  · simp [gscale_state, ht_pos]
  · simp [gscale_state, ht_pos]

/-- Generalized CEq for gscale_state: if t₁ = t₂, the generalized scaled states are adiabatically equivalent. -/
lemma gscale_eq_coherence {t₁ t₂ : ℝ} (h_eq : t₁ = t₂) {Γ} (X : TW.State Γ)
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    gscale_state ht₁ X ≈ gscale_state ht₂ X := by
  subst h_eq
  have h_rewrite :
      gscale_state (System := System) (t := t₁) (Γ := Γ) ht₂ X
        = gscale_state (System := System) (t := t₁) (Γ := Γ) ht₁ X := by
    simp
  simpa [h_rewrite] using (thermo_equiv_refl (gscale_state ht₁ X))

/-! ### Generalized Recombination
-/
lemma generalized_recombination_lemma {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {Γ} (X : TW.State Γ) :
    gscale_state (add_nonneg ha hb) X ≈ comp_state (gscale_state ha X, gscale_state hb X) := by
  classical
  rcases lt_or_eq_of_le ha with ha_pos | ha_zero
  · -- a > 0
    rcases lt_or_eq_of_le hb with hb_pos | hb_zero
    · -- b > 0: strict recombination, normalize via gscale_state_pos
      have hsum_pos : 0 < a + b := add_pos ha_pos hb_pos
      simpa [ gscale_state_pos (add_nonneg ha hb) hsum_pos
            , gscale_state_pos ha ha_pos
            , gscale_state_pos hb hb_pos ] using
        (recombination_lemma ha_pos hb_pos (Γ := Γ) X)
    · -- b = 0
      subst hb_zero
      -- LHS: (a+0)•X ≈ a•X by CEq and CCast
      have hsum_pos : 0 < a + 0 := by simpa [add_zero] using ha_pos
      have hL_eq : gscale_state (add_nonneg ha (by simp)) X
                 = scale_state hsum_pos.ne' X := by
        simp [gscale_state_pos (add_nonneg ha (by simp)) hsum_pos]
      let L0 : TW.State ((a + 0) • Γ) := scale_state hsum_pos.ne' X
      let aX : TW.State (a • Γ) := scale_state ha_pos.ne' X
      have h_sys_sum : TW.scale (a + 0) Γ = TW.scale a Γ := by simp [add_zero]
      -- Cast coherence for L0 along system equality, then CEq to reach aX
      have h_castL : L0 ≈ (Equiv.cast (congrArg TW.State h_sys_sum) L0) :=
        TW.state_equiv_coherence h_sys_sum L0
      have h_ceq :
          (Equiv.cast (congrArg TW.State h_sys_sum) L0) ≈ aX :=
        TW.scale_eq_coherence (Γ := Γ) (t₁ := a + 0) (t₂ := a)
          (h_eq := by simp [add_zero]) (ht₁ := hsum_pos.ne') (X := X)
      have h_left : gscale_state (add_nonneg ha (by rfl)) X ≈ aX := by
        rw [hL_eq]
        exact (thermo_equiv_trans' h_castL h_ceq)
      -- RHS: (a•X, 0•X) ≈ (a•X, default) ≈ a•X
      let zeroR : TW.State (TW.scale 0 Γ) := gscale_state (by simp) X
      -- zeroR ≈ default via CCast
      have h0_sys : (0 : ℝ) • Γ = TW.ZSystem := by simp [TW.scale_zero_is_ZSystem]
      have h_zeroR_equiv_default :
          zeroR ≈ (default : TW.State TW.ZSystem) := by
        -- default ≈ cast(default) = zeroR
        have h_def_to_zeroR :
            (default : TW.State TW.ZSystem) ≈
              (Equiv.cast (congrArg TW.State h0_sys)).symm (default) := by
          simpa using
            (TW.state_equiv_coherence h0_sys.symm (default : TW.State TW.ZSystem))
        -- unfold zeroR to the same casted form
        have hz : zeroR =
            (Equiv.cast (congrArg TW.State h0_sys)).symm (default) := by
          simp [zeroR]
        simpa [hz] using (thermo_equiv_symm h_def_to_zeroR)
      -- aX ≈ (aX, default)
      have h_to_pair_default :
          aX ≈ comp_state (aX, (default : TW.State TW.ZSystem)) :=
        thermo_equiv_symm (TW.comp_ZSystem_is_identity (Γ := (a • Γ)) (X := aX))
      -- replace default by zeroR using A3
      have h_replace :
          comp_state (aX, (default : TW.State TW.ZSystem))
            ≈ comp_state (aX, zeroR) :=
        ⟨ TW.A3 (thermo_le_refl aX) (h_zeroR_equiv_default).2
        , TW.A3 (thermo_le_refl aX) (h_zeroR_equiv_default).1 ⟩
      have h_right_to_pair : aX ≈ comp_state (aX, zeroR) :=
        thermo_equiv_trans' h_to_pair_default h_replace
      -- adjust RHS shape by normalizing gscale_state on a>0 and b=0
      have hA_norm : gscale_state ha X = aX := by
        simp [gscale_state_pos ha ha_pos, aX]
      have hB_norm : gscale_state (by simp : 0 ≤ (0:ℝ)) X = zeroR := rfl
      have h_right :
          aX ≈ comp_state (gscale_state ha X, zeroR) := by
        simpa [hA_norm] using h_right_to_pair
      -- chain LHS to RHS through aX
      exact thermo_equiv_trans' h_left h_right
  · -- a = 0
    subst ha_zero
    rcases lt_or_eq_of_le hb with hb_pos | hb_zero
    · -- b > 0 (symmetric)
      -- LHS: (0+b)•X ≈ b•X
      have hsum_pos : 0 < 0 + b := by simpa [zero_add] using hb_pos
      have hL_eq : gscale_state (add_nonneg (by simp) hb) X
                 = scale_state hsum_pos.ne' X := by
        simp [gscale_state_pos (add_nonneg (by simp) hb) hsum_pos]
      let L0 : TW.State ((0 + b) • Γ) := scale_state hsum_pos.ne' X
      let bX : TW.State (b • Γ) := scale_state hb_pos.ne' X
      have h_sys_sum : TW.scale (0 + b) Γ = TW.scale b Γ := by simp [zero_add]
      have h_castL : L0 ≈ (Equiv.cast (congrArg TW.State h_sys_sum) L0) :=
        TW.state_equiv_coherence h_sys_sum L0
      have h_ceq :
          (Equiv.cast (congrArg TW.State h_sys_sum) L0) ≈ bX := by
        simpa [L0, bX, h_sys_sum] using
          (TW.scale_eq_coherence (Γ := Γ) (X := X)
            (h_eq := by simp [zero_add]) (ht₁ := hsum_pos.ne'))
      have h_left : gscale_state (add_nonneg (by rfl) hb) X ≈ bX := by
        simpa [hL_eq] using (thermo_equiv_trans' h_castL h_ceq)
      -- RHS: (0•X, b•X) ≈ (default, b•X) ≈ b•X
      -- RHS: (0•X, b•X) ≈ (default, b•X) ≈ b•X
      let zeroL : TW.State (TW.scale 0 Γ) := gscale_state (by simp) X
      have h0_sys : (0 : ℝ) • Γ = TW.ZSystem := by simp [TW.scale_zero_is_ZSystem]
      have h_zeroL_equiv_default :
          zeroL ≈ (default : TW.State TW.ZSystem) := by
        have h_def_to_zeroL :
            (default : TW.State TW.ZSystem) ≈
              (Equiv.cast (congrArg TW.State h0_sys)).symm (default) := by
          simpa using
            (TW.state_equiv_coherence h0_sys.symm (default : TW.State TW.ZSystem))
        have hz : zeroL =
            (Equiv.cast (congrArg TW.State h0_sys)).symm (default) := by
          simp [zeroL]
        simpa [hz] using (thermo_equiv_symm h_def_to_zeroL)
      -- (default, bX) ≈ bX via CC then CZ
      have h_comm :
          comp_state ((default : TW.State TW.ZSystem), bX)
            ≈ comp_state (bX, (default : TW.State TW.ZSystem)) :=
        comp_comm_equiv_clean (default : TW.State TW.ZSystem) bX
      have h_cz :
          comp_state (bX, (default : TW.State TW.ZSystem)) ≈ bX :=
        TW.comp_ZSystem_is_identity (Γ := (b • Γ)) (X := bX)
      have h_ZbX :
          comp_state ((default : TW.State TW.ZSystem), bX) ≈ bX :=
        thermo_equiv_trans' h_comm h_cz
      -- replace default by zeroL on the left using A3
      have h_replace :
          comp_state (zeroL, bX) ≈
          comp_state ((default : TW.State TW.ZSystem), bX) :=
        ⟨ TW.A3 (h_zeroL_equiv_default.1) (thermo_le_refl bX)
        , TW.A3 (h_zeroL_equiv_default.2) (thermo_le_refl bX) ⟩
      have h_right_to_pair :
          bX ≈ comp_state (zeroL, bX) :=
        thermo_equiv_symm (thermo_equiv_trans' h_replace h_ZbX)
      -- adjust RHS shape by normalizing gscale_state on a=0 and b>0
      have hA_norm : gscale_state (by simp : 0 ≤ (0:ℝ)) X = zeroL := rfl
      have hB_norm : gscale_state hb X = bX := by
        simp [gscale_state_pos hb hb_pos]; rfl
      have h_right :
          bX ≈ comp_state (gscale_state (by rfl) X, gscale_state hb X) := by
        aesop
      -- chain LHS to RHS through bX
      exact thermo_equiv_trans' h_left (h_right)
    · -- a = 0, b = 0
      subst hb_zero
      have hsum_sys : ((0:ℝ) + 0) • Γ = TW.ZSystem := by simp [TW.scale_zero_is_ZSystem]
      have hL_def :
          gscale_state (add_nonneg (by simp) (by simp)) X
            = (Equiv.cast (congrArg TW.State hsum_sys)).symm
                (TW.State_ZSystem_is_Unit.default) := by
        simp [gscale_state]
      have hL_equiv_default :
          gscale_state (add_nonneg (by rfl) (by rfl)) X
            ≈ (default : TW.State TW.ZSystem) := by
        have h_def_to_L :
            (default : TW.State TW.ZSystem) ≈
              (Equiv.cast (congrArg TW.State hsum_sys)).symm
                (TW.State_ZSystem_is_Unit.default) := by
          simpa using
            (TW.state_equiv_coherence hsum_sys.symm
              (default : TW.State TW.ZSystem))
        simpa [hL_def] using (thermo_equiv_symm h_def_to_L)
      let zeroL : TW.State (TW.scale 0 Γ) := gscale_state (by simp) X
      let zeroR : TW.State (TW.scale 0 Γ) := gscale_state (by simp) X
      have h0_sys : (0 : ℝ) • Γ = TW.ZSystem := by simp [TW.scale_zero_is_ZSystem]
      have h_zeroL_def :
          zeroL ≈ (default : TW.State TW.ZSystem) := by
        have h_def_to_zeroL :
            (default : TW.State TW.ZSystem) ≈
              (Equiv.cast (congrArg TW.State h0_sys)).symm (default) := by
          simpa using
            (TW.state_equiv_coherence h0_sys.symm (default : TW.State TW.ZSystem))
        have hz : zeroL =
            (Equiv.cast (congrArg TW.State h0_sys)).symm (default) := by
          simp [zeroL]
        simpa [hz] using (thermo_equiv_symm h_def_to_zeroL)
      have h_zeroR_def :
          zeroR ≈ (default : TW.State TW.ZSystem) := by
        have h_def_to_zeroR :
            (default : TW.State TW.ZSystem) ≈
              (Equiv.cast (congrArg TW.State h0_sys)).symm (default) := by
          simpa using
            (TW.state_equiv_coherence h0_sys.symm (default : TW.State TW.ZSystem))
        have hz : zeroR =
            (Equiv.cast (congrArg TW.State h0_sys)).symm (default) := by
          aesop
        simpa [hz] using (thermo_equiv_symm h_def_to_zeroR)
      -- replace both by defaults via A3
      have h_pair_to_defaults :
          comp_state (zeroL, zeroR)
            ≈ comp_state ((default : TW.State TW.ZSystem),
                          (default : TW.State TW.ZSystem)) :=
        ⟨ TW.A3 (h_zeroL_def.1) (h_zeroR_def.1)
        , TW.A3 (h_zeroL_def.2) (h_zeroR_def.2) ⟩
      -- collapse (Z, Z) ≈ Z
      have h_ZZ_to_Z :
          comp_state ((default : TW.State TW.ZSystem),
                      (default : TW.State TW.ZSystem))
            ≈ (default : TW.State TW.ZSystem) :=
        TW.comp_ZSystem_is_identity (Γ := TW.ZSystem)
          (X := (default : TW.State TW.ZSystem))
      have h_R_equiv_default :
          comp_state (zeroL, zeroR) ≈ (default : TW.State TW.ZSystem) :=
        thermo_equiv_trans' h_pair_to_defaults h_ZZ_to_Z
      have hA_norm2 : gscale_state (System := System) ha X = zeroL := by
        simp [zeroL]
      have hB_norm2 : gscale_state (System := System) hb X = zeroR := by
        simp [zeroR]
      simpa [hA_norm2, hB_norm2, zeroL, zeroR, gscale_state, gscale_state_zero] using
        (thermo_equiv_trans' hL_equiv_default (thermo_equiv_symm h_R_equiv_default))

end LY
