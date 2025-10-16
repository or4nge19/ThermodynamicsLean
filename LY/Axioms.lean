/-
Copyright (c) 2025 Matteo Cipollina All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic

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

end LY
