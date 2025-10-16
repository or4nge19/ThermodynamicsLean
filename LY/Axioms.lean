/-
Copyright (c) 2025 Matteo Cipollina All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The Axiomatic Framework of Lieb-Yngvason Thermodynamics

This file defines the foundational `ThermoWorld` class, which encapsulates the
axiomatic framework for the second law of thermodynamics as proposed by
Lieb and Yngvason. It includes:
- The basic types: `System` and `State`.
- System operations: composition (`comp`) and scaling (`scale`).
- The adiabatic accessibility relation (`le`, denoted `≺`).
- Structural properties of systems (associativity, commutativity, etc.).
- The six core axioms of adiabatic accessibility (A1-A6).
- Coherence axioms that relate system equalities to state equivalences.
-/

namespace LY

universe u v

/--
The ThermoWorld class encapsulates the axiomatic framework of Lieb and Yngvason.
-/
class ThermoWorld (System : Type u) where
  State : System → Type v
  comp : System → System → System
  scale : ℝ → System → System

  /-- Adiabatic accessibility relation (≺) -/
  le {Γ₁ Γ₂ : System} : State Γ₁ → State Γ₂ → Prop

  /- ### Structural Definitions -/

  /-- The Zero System (Z). -/
  ZSystem : System
  State_ZSystem_is_Unit : Unique (State ZSystem)

  state_of_comp_equiv {Γ₁ Γ₂} : State (comp Γ₁ Γ₂) ≃ (State Γ₁ × State Γ₂)
  state_of_scale_equiv {t : ℝ} (ht : t ≠ 0) {Γ} : State (scale t Γ) ≃ State Γ

  scale_zero_is_ZSystem (Γ : System) : scale 0 Γ = ZSystem

  /- ### Algebraic Properties of Systems -/

  comp_assoc (Γ₁ Γ₂ Γ₃ : System) : comp (comp Γ₁ Γ₂) Γ₃ = comp Γ₁ (comp Γ₂ Γ₃)
  comp_comm (Γ₁ Γ₂ : System) : comp Γ₁ Γ₂ = comp Γ₂ Γ₁
  scale_distrib_comp (t : ℝ) (Γ₁ Γ₂ : System) : scale t (comp Γ₁ Γ₂) = comp (scale t Γ₁) (scale t Γ₂)
  smul_smul (t s : ℝ) (Γ : System) : scale (t * s) Γ = scale t (scale s Γ)
  one_smul (Γ : System) : scale 1 Γ = Γ

  /- ### Axioms of Adiabatic Accessibility (A1-A6) -/

  /-- A1 (Reflexivity) -/
  A1 {Γ} (X : State Γ) : le X X
  /-- A2 (Transitivity) -/
  A2 {Γ₁ Γ₂ Γ₃} {X : State Γ₁} {Y : State Γ₂} {Z : State Γ₃} : le X Y → le Y Z → le X Z
  /-- A3 (Consistency) -/
  A3 {Γ₁ Γ₂ Γ₃ Γ₄} {X₁ : State Γ₁} {X₂ : State Γ₂} {Y₁ : State Γ₃} {Y₂ : State Γ₄} :
    le X₁ Y₁ → le X₂ Y₂ → le (state_of_comp_equiv.symm (X₁, X₂)) (state_of_comp_equiv.symm (Y₁, Y₂))
  /-- A4 (Scaling Invariance) -/
  A4 {Γ₁ Γ₂} {X : State Γ₁} {Y : State Γ₂} {t : ℝ} (ht : 0 < t) :
    le X Y → le ((state_of_scale_equiv ht.ne.symm).symm X) ((state_of_scale_equiv ht.ne.symm).symm Y)
  /-- A5 (Splitting and Recombination) -/
  A5 {Γ} (X : State Γ) {t : ℝ} (ht : 0 < t ∧ t < 1) :
    le X
      (state_of_comp_equiv.symm
        ( ((state_of_scale_equiv ht.1.ne').symm X)
        , ((state_of_scale_equiv (t := 1 - t) (by
              have hpos : 0 < 1 - t := sub_pos.mpr ht.2
              exact hpos.ne')).symm X) )) ∧
    le (state_of_comp_equiv.symm
        ( ((state_of_scale_equiv ht.1.ne').symm X)
        , ((state_of_scale_equiv (t := 1 - t) (by
              have hpos : 0 < 1 - t := sub_pos.mpr ht.2
              exact hpos.ne')).symm X) )) X
  /-- A6 (Stability) - Sequential Formulation (L–Y Eq 2.5).
      If (X, εₖZ₀) ≺ (Y, εₖZ₁) holds for a sequence εₖ → 0 with εₖ > 0, then X ≺ Y. -/
  A6_seq {ΓX ΓY ΓZ₀ ΓZ₁} (X : State ΓX) (Y : State ΓY) (Z₀ : State ΓZ₀) (Z₁ : State ΓZ₁) :
    (∃ (ε_seq : ℕ → ℝ) (hpos : ∀ n, 0 < ε_seq n),
      Filter.Tendsto ε_seq Filter.atTop (nhds 0) ∧
      (∀ n,
        le
          (state_of_comp_equiv.symm
            (X, (state_of_scale_equiv (ne_of_gt (hpos n))).symm Z₀))
          (state_of_comp_equiv.symm
            (Y, (state_of_scale_equiv (ne_of_gt (hpos n))).symm Z₁)))) → le X Y

  /- ### Coherence Axioms -/

  /-- Coherence of Casting (CCast) -/
  state_equiv_coherence {Γ₁ Γ₂ : System} (h_sys : Γ₁ = Γ₂) (X : State Γ₁) :
    le X (Equiv.cast (congrArg State h_sys) X) ∧ le (Equiv.cast (congrArg State h_sys) X) X

  /-- Coherence of Zero Composition (CZ) -/
  comp_ZSystem_is_identity (Γ : System) (X : State Γ) :
    le (state_of_comp_equiv.symm (X, (default : State ZSystem))) X ∧
    le X (state_of_comp_equiv.symm (X, (default : State ZSystem)))

  /-- Coherence of Scaling (CS): t•(s•X) ≈ (t*s)•X -/
  scale_coherence {t s : ℝ} (ht : t ≠ 0) (hs : s ≠ 0) {Γ} (X : State Γ) :
    let X_s := (state_of_scale_equiv hs).symm X
    let X_ts := (state_of_scale_equiv ht).symm X_s -- t•(s•X)
    let X_mul := (state_of_scale_equiv (mul_ne_zero ht hs)).symm X -- (t*s)•X
    let h_eq := smul_smul t s Γ -- (t*s)•Γ = t•(s•Γ)
    le (Equiv.cast (congrArg State h_eq) X_mul) X_ts ∧
    le X_ts (Equiv.cast (congrArg State h_eq) X_mul)

  /-- Coherence of Equal Scaling (CEq): If t₁ = t₂, then t₁•X ≈ t₂•X. -/
  scale_eq_coherence {t₁ t₂ : ℝ} (h_eq : t₁ = t₂) (ht₁ : t₁ ≠ 0) {Γ} (X : State Γ) :
    let ht₂ : t₂ ≠ 0 := by rwa [←h_eq]
    let X₁ := (state_of_scale_equiv ht₁).symm X
    let X₂ := (state_of_scale_equiv ht₂).symm X
    let h_sys_eq := congrArg (fun r => scale r Γ) h_eq -- t₁•Γ = t₂•Γ
    le (Equiv.cast (congrArg State h_sys_eq) X₁) X₂ ∧
    le X₂ (Equiv.cast (congrArg State h_sys_eq) X₁)

  /-- Coherence of Identity Scaling (C1): 1•X ≈ X -/
  one_smul_coherence {Γ} (X : State Γ) :
    let X_1 := (state_of_scale_equiv (by norm_num : (1:ℝ) ≠ 0)).symm X
    let h_eq := one_smul Γ
    le (Equiv.cast (congrArg State h_eq) X_1) X ∧
    le X (Equiv.cast (congrArg State h_eq) X_1)

  /-- Coherence of Scaling Composition (CSC): t•(X, Y) ≈ (t•X, t•Y) -/
  scale_comp_coherence {t : ℝ} (ht : t ≠ 0) {Γ₁ Γ₂} (X : State Γ₁) (Y : State Γ₂) :
    let XY := state_of_comp_equiv.symm (X, Y)
    let tXY := (state_of_scale_equiv ht).symm XY
    let tX := (state_of_scale_equiv ht).symm X
    let tY := (state_of_scale_equiv ht).symm Y
    let tXtY := state_of_comp_equiv.symm (tX, tY)
    let h_eq := scale_distrib_comp t Γ₁ Γ₂
    le (Equiv.cast (congrArg State h_eq) tXY) tXtY ∧
    le tXtY (Equiv.cast (congrArg State h_eq) tXY)

  /-- Coherence of Commutativity (CC): (X, Y) ≈ (Y, X) -/
  comp_comm_coherence {Γ₁ Γ₂} (X : State Γ₁) (Y : State Γ₂) :
    let XY := state_of_comp_equiv.symm (X, Y)
    let YX := state_of_comp_equiv.symm (Y, X)
    let h_eq := comp_comm Γ₁ Γ₂
    -- Note: We use h_eq.symm because Cast(h_eq.symm) maps State(Γ₂⊗Γ₁) to State(Γ₁⊗Γ₂).
    le (Equiv.cast (congrArg State h_eq.symm) YX) XY ∧
    le XY (Equiv.cast (congrArg State h_eq.symm) YX)

  /-- Coherence of Associativity (CA): ((X, Y), Z) ≈ (X, (Y, Z)) -/
  comp_assoc_coherence {Γ₁ Γ₂ Γ₃} (X : State Γ₁) (Y : State Γ₂) (Z : State Γ₃) :
    let XY := state_of_comp_equiv.symm (X, Y)
    let XYZ_L := state_of_comp_equiv.symm (XY, Z)
    let YZ := state_of_comp_equiv.symm (Y, Z)
    let XYZ_R := state_of_comp_equiv.symm (X, YZ)
    let h_eq := comp_assoc Γ₁ Γ₂ Γ₃
    -- Cast(h_eq) maps State((Γ₁⊗Γ₂)⊗Γ₃) to State(Γ₁⊗(Γ₂⊗Γ₃)).
    le (Equiv.cast (congrArg State h_eq) XYZ_L) XYZ_R ∧
    le XYZ_R (Equiv.cast (congrArg State h_eq) XYZ_L)

-- Setup and Notation
variable {System : Type u} [TW : ThermoWorld System]
local infix:50 " ≺ " => TW.le
/-- Adiabatic Equivalence (≈) -/
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X
local infixr:70 " ⊗ " => TW.comp
local infixr:80 " • " => TW.scale

-- Inhabited instance for the zero system state.
instance instInhabitedZState (System : Type u) [TW : ThermoWorld System] :
    Inhabited (TW.State TW.ZSystem) :=
  ⟨TW.State_ZSystem_is_Unit.default⟩

/-- Helper definition for the state of a compound system. -/
def comp_state {Γ₁ Γ₂} (p : TW.State Γ₁ × TW.State Γ₂) : TW.State (Γ₁ ⊗ Γ₂) := TW.state_of_comp_equiv.symm p
/-- Helper definition for the state of a scaled system (tX). -/
def scale_state {t : ℝ} (ht : t ≠ 0) {Γ} (X : TW.State Γ) : TW.State (t • Γ) := (TW.state_of_scale_equiv ht).symm X

/-! ### Basic Lemmas -/

lemma thermo_le_refl {Γ : System} (X : TW.State Γ) : X ≺ X := TW.A1 X
lemma thermo_le_trans {Γ₁ Γ₂ Γ₃ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂} {Z : TW.State Γ₃}
    (h₁ : X ≺ Y) (h₂ : Y ≺ Z) : X ≺ Z := TW.A2 h₁ h₂
lemma thermo_equiv_refl {Γ : System} (X : TW.State Γ) : X ≈ X := ⟨thermo_le_refl X, thermo_le_refl X⟩
lemma thermo_equiv_symm {Γ₁ Γ₂ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂} (h : X ≈ Y) : Y ≈ X := And.symm h
lemma thermo_equiv_trans {Γ₁ Γ₂ Γ₃ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂} {Z : TW.State Γ₃}
    (h₁ : X ≈ Y) (h₂ : Y ≈ Z) : X ≈ Z :=
  ⟨thermo_le_trans h₁.1 h₂.1, thermo_le_trans h₂.2 h₁.2⟩

-- Alias for explicit typing when needed.
lemma thermo_equiv_trans' {Γ₁ Γ₂ Γ₃ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂} {Z : TW.State Γ₃}
    (h₁ : X ≈ Y) (h₂ : Y ≈ Z) : X ≈ Z := thermo_equiv_trans h₁ h₂

lemma le_of_equiv_le {Γ₁ Γ₂ Γ₃ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂} {Z : TW.State Γ₃}
    (h : X ≈ Y) (h' : Y ≺ Z) : X ≺ Z := thermo_le_trans h.1 h'
lemma le_of_le_equiv {Γ₁ Γ₂ Γ₃ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂} {Z : TW.State Γ₃}
    (h : X ≺ Y) (h' : Y ≈ Z) : X ≺ Z := thermo_le_trans h h'.1

lemma one_minus_ne_of_ht {t : ℝ} (ht : 0 < t ∧ t < 1) : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'

/-- Coordinate model for simple systems. -/
abbrev SimpleSystemSpace (n : ℕ) := ℝ × (Fin n → ℝ)

/-! Instances for the coordinate space. -/
instance instAddCommGroupSimpleSystemSpace (n : ℕ) :
    AddCommGroup (SimpleSystemSpace n) := by
  dsimp [SimpleSystemSpace]; infer_instance

noncomputable instance instModuleSimpleSystemSpace (n : ℕ) :
    Module ℝ (SimpleSystemSpace n) := by
  dsimp [SimpleSystemSpace]; infer_instance

instance instTopologicalSpaceSimpleSystemSpace (n : ℕ) :
    TopologicalSpace (SimpleSystemSpace n) := by
  dsimp [SimpleSystemSpace]; infer_instance

instance (n : ℕ) : Inhabited (SimpleSystemSpace n) := ⟨(0, 0)⟩

/-- The class `IsSimpleSystem` asserts that a system `Γ` has the structure of a
    simple system with `n` work coordinates. It contains the axioms specific to
    simple systems, including A7, S1, S2, and S3.
-/
class IsSimpleSystem {System : Type u} [TW : ThermoWorld System] (n : ℕ) (Γ : System) where
  space : Set (SimpleSystemSpace n)
  isOpen : IsOpen space
  isConvex : Convex ℝ space
  state_equiv : TW.State Γ ≃ { p : SimpleSystemSpace n // p ∈ space }
  /-- Coherence of convex splitting: the composition of scaled simple systems equals the original system. -/
  comp_scale_split {t : ℝ} (ht : 0 < t ∧ t < 1) :
    TW.comp (TW.scale t Γ) (TW.scale (1 - t) Γ) = Γ

  /-- Coherence Axiom: abstract scaling corresponds to coordinate smul (axiomatic).
  TODO derive it as theorem from a concrete simple system -/
  scale_is_smul_equiv (X : TW.State Γ) {t : ℝ} (ht : 0 < t) :
    let tX_abstract := scale_state ht.ne' X
    let X_coord := state_equiv X
    let tX_coord_val : SimpleSystemSpace n := t • (X_coord : SimpleSystemSpace n)
    -- We postulate existence of the scaled coordinate inside the simple system space.
    ∃ (h_in_space : tX_coord_val ∈ space),
      let tX_concrete := state_equiv.symm ⟨tX_coord_val, h_in_space⟩
      -- Transport the concrete (in-Γ) representative to t•Γ via the scale equivalence.
      let tX_concrete_scaled := (TW.state_of_scale_equiv ht.ne').symm tX_concrete
      (TW.le (Γ₁ := TW.scale t Γ) (Γ₂ := TW.scale t Γ) tX_abstract tX_concrete_scaled) ∧
      (TW.le (Γ₁ := TW.scale t Γ) (Γ₂ := TW.scale t Γ) tX_concrete_scaled tX_abstract)

  /-- A7 (Concavity): convex combination yields adiabatic accessibility. -/
  A7 (X Y : TW.State Γ) {t : ℝ} (ht : 0 < t ∧ t < 1)
     (ha : 0 ≤ t) (hb : 0 ≤ 1 - t) (hab : t + (1 - t) = 1) :
    let X_coord := state_equiv X
    let Y_coord := state_equiv Y
    let tX := scale_state ht.1.ne' X
    let one_minus_t_Y := scale_state (sub_pos.mpr ht.2).ne' Y
    let combo_state := comp_state (tX, one_minus_t_Y)
    let target_coord := t • (X_coord : SimpleSystemSpace n) + (1 - t) • (Y_coord : SimpleSystemSpace n)
    let h_target_in_space := isConvex X_coord.property Y_coord.property ha hb hab
    let target_state_orig := state_equiv.symm ⟨target_coord, h_target_in_space⟩
    let h_eq := comp_scale_split ht
    let target_state := (Equiv.cast (congrArg TW.State h_eq).symm) target_state_orig
    (@TW.le
      (TW.comp (TW.scale t Γ) (TW.scale (1 - t) Γ))
      (TW.comp (TW.scale t Γ) (TW.scale (1 - t) Γ))
      combo_state target_state)

  -- Explicit systems in `le` to avoid inference ambiguity.
  S1 (X : TW.State Γ) :
    ∃ Y : TW.State Γ,
      (TW.le (Γ₁ := Γ) (Γ₂ := Γ) X Y) ∧
      ¬ (TW.le (Γ₁ := Γ) (Γ₂ := Γ) Y X)
local notation:50 X " ≺≺ " Y => X ≺ Y ∧ ¬ (Y ≺ X)

def ForwardSector {Γ Γ' : System} (X : TW.State Γ) : Set (TW.State Γ') :=
  { Y : TW.State Γ' | X ≺ Y }

/-- **Theorem 2.6 (Forward sectors are convex)** - Revised
    If `Γ` is a simple system, the forward sector of any state `X ∈ Γ` within `Γ`
    is a convex set (in the coordinate representation). -/
theorem forward_sectors_are_convex {n : ℕ} {Γ : System} [ss : IsSimpleSystem n Γ] (X : TW.State Γ) :
    Convex ℝ ((fun Y : TW.State Γ =>
      ((ss.state_equiv Y : { p : SimpleSystemSpace n // p ∈ ss.space }) : SimpleSystemSpace n))
        '' (ForwardSector X : Set (TW.State Γ))) := by
  -- `Convex` in Mathlib uses coefficients `a b` with `a,b ≥ 0` and `a+b=1`.
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  rcases hy₁ with ⟨Y₁, hY₁_in_sector, rfl⟩
  rcases hy₂ with ⟨Y₂, hY₂_in_sector, rfl⟩
  -- Shorthands for subtype points and their coordinate representatives.
  set Y₁_sub := ss.state_equiv Y₁ with hY₁sub
  set Y₂_sub := ss.state_equiv Y₂ with hY₂sub
  have hY₁_in_space : (Y₁_sub : SimpleSystemSpace n) ∈ ss.space := Y₁_sub.property
  have hY₂_in_space : (Y₂_sub : SimpleSystemSpace n) ∈ ss.space := Y₂_sub.property
  -- The convex combination in coordinates.
  let Z_coord_val : SimpleSystemSpace n :=
    a • (Y₁_sub : SimpleSystemSpace n) + b • (Y₂_sub : SimpleSystemSpace n)
  have hZ_in_space : Z_coord_val ∈ ss.space :=
    ss.isConvex hY₁_in_space hY₂_in_space ha hb hab
  -- Build the target state Z in Γ whose coordinates are Z_coord_val.
  let Z : TW.State Γ := ss.state_equiv.symm ⟨Z_coord_val, hZ_in_space⟩
  -- Show X ≺ Z by chaining A5, A3, A7 (handling edge cases a=0 or b=0).
  -- First, derive useful equalities from a+b=1.
  have hb_eq : b = 1 - a := by
    have hba : b + a = 1 := by simpa [add_comm] using hab
    exact eq_sub_of_add_eq' hab
  have ha_le_1 : a ≤ 1 := by
    have : 0 ≤ 1 - a := by simpa [hb_eq] using hb
    simpa [sub_nonneg] using this
  -- Prove X ≺ Z.
  have h_chain : X ≺ Z := by
    by_cases ha0 : a = 0
    · -- Then b = 1, so Z reduces to Y₂.
      have hb1 : b = 1 := by simpa [ha0] using hab
      have hZ_eqY₂ : ss.state_equiv Z = Y₂_sub := by
        apply Subtype.eq
        simp [Z, Z_coord_val, ha0, hb1, zero_smul, one_smul, zero_add]
      have Z_eq_Y₂ : Z = Y₂ := ss.state_equiv.injective hZ_eqY₂
      simpa [Z_eq_Y₂] using hY₂_in_sector
    · -- a ≠ 0
      have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      by_cases hb0 : b = 0
      · -- Then a = 1 by a+b=1, so Z reduces to Y₁.
        have ha1 : a = 1 := by
          have := congrArg (fun t => t - b) hab
          -- a + b = 1 ⇒ a = 1 - b = 1 - 0 = 1
          simpa [add_comm, hb0] using this
        have hZ_eqY₁ : ss.state_equiv Z = Y₁_sub := by
          apply Subtype.eq
          simp [Z, Z_coord_val, ha1, hb0, zero_smul, one_smul, add_zero]
        have Z_eq_Y₁ : Z = Y₁ := ss.state_equiv.injective hZ_eqY₁
        simpa [Z_eq_Y₁] using hY₁_in_sector
      · -- Main case: 0 < a < 1 and 0 < b (since b = 1 - a).
        have hb_pos : 0 < b := by
          -- b = 1 - a and a < 1
          have ha_ne1 : a ≠ 1 := by
            intro h
            have : b = 0 := by simp [hb_eq, h]
            exact hb0 this
          have : 0 < 1 - a := by
            simpa [hb_eq] using lt_of_le_of_ne' hb hb0
          exact lt_of_lt_of_eq this (id (Eq.symm hb_eq))
        clear hb_pos
        have hb_pos : 0 < b := by
          exact lt_of_le_of_ne' hb hb0
        have ha_ne1 : a ≠ 1 := by
          intro h
          have : b = 0 := by simp [hb_eq, h]
          exact (ne_of_gt hb_pos) this
        have ha_lt_1 : a < 1 := lt_of_le_of_ne ha_le_1 ha_ne1
        have ht_bounds : 0 < a ∧ a < 1 := ⟨ha_pos, ha_lt_1⟩
        -- 1. A5: X ≺ (a•X, (1-a)•X).
        have h_split := (TW.A5 X ht_bounds).1
        -- 2. A3 via A4 on each component: (a•X, (1-a)•X) ≺ (a•Y₁, (1-a)•Y₂).
        have h_aX_aY₁   := TW.A4 ht_bounds.1 hY₁_in_sector
        have h_1maX_1maY₂ := TW.A4 (by exact sub_pos.mpr ht_bounds.2) hY₂_in_sector
        have h_consistency := TW.A3 h_aX_aY₁ h_1maX_1maY₂
        -- 3. A7: (a•Y₁, (1-a)•Y₂) ≺ Z_casted in the composite system.
        let h_eq := ss.comp_scale_split ht_bounds
        let Z_casted : TW.State (TW.comp (TW.scale a Γ) (TW.scale (1 - a) Γ)) :=
          Equiv.cast (congrArg TW.State h_eq).symm Z
        have h_A7_applied :
            comp_state (scale_state ht_bounds.1.ne' Y₁,
                        scale_state (one_minus_ne_of_ht ht_bounds) Y₂) ≺ Z_casted := by
          -- Match the let-terms in A7 to our Z_casted and parameters.
          simpa [Z_casted, Z, Z_coord_val, hb_eq, h_eq] using
            (ss.A7 (X := Y₁) (Y := Y₂) (t := a) ht_bounds
              ha
              (by simpa [hb_eq] using hb)
              (by simp))
        -- 4. Chain with Transitivity (A2) and remove the cast using coherence.
        have h_chain1 := TW.A2 h_split (TW.A2 h_consistency h_A7_applied)
        have h_coh : Z_casted ≺ Z := (TW.state_equiv_coherence (h_sys := h_eq.symm) Z).2
        exact TW.A2 h_chain1 h_coh
  -- Return the coordinates of Z, showing they're in the image under the coordinate map.
  refine ⟨Z, h_chain, ?_⟩
  simp [Z, Z_coord_val, hY₁sub, hY₂sub]

end LY
