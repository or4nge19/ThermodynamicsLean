/-
Copyright (c) 2025 Matteo Cipollina All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.InnerProductSpace.PiL2
import LY.ForMathlib.TangentCone

open scoped RealInnerProductSpace

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
- The `IsSimpleSystem` and `SimpleSystemFamily` abstractions:
  identification of simple systems with open, convex subsets of a
  Euclidean coordinate space, closure under positive scaling, and the
  additional axioms (A7, S1) used in the coordinate theory.
- Definitions and basic lemmas for composition and scaling of
  states, forward sectors, convexity results.
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

-- Provide a transitivity instance for the adiabatic accessibility relation
instance calcTransThermoLe {Γ₁ Γ₂ Γ₃ : System} :
  Trans (TW.le : TW.State Γ₁ → TW.State Γ₂ → Prop)
        (TW.le : TW.State Γ₂ → TW.State Γ₃ → Prop)
        (TW.le : TW.State Γ₁ → TW.State Γ₃ → Prop) where
  trans := TW.A2

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

lemma thermo_equiv_trans' {Γ₁ Γ₂ Γ₃ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂} {Z : TW.State Γ₃}
    (h₁ : X ≈ Y) (h₂ : Y ≈ Z) : X ≈ Z := thermo_equiv_trans h₁ h₂

lemma le_of_equiv_le {Γ₁ Γ₂ Γ₃ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂} {Z : TW.State Γ₃}
    (h : X ≈ Y) (h' : Y ≺ Z) : X ≺ Z := thermo_le_trans h.1 h'
lemma le_of_le_equiv {Γ₁ Γ₂ Γ₃ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂} {Z : TW.State Γ₃}
    (h : X ≺ Y) (h' : Y ≈ Z) : X ≺ Z := thermo_le_trans h h'.1

lemma one_minus_ne_of_ht {t : ℝ} (ht : 0 < t ∧ t < 1) : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'

end LY

namespace LY

universe u v

variable {System : Type u} [TW : ThermoWorld System]

local infix:50 " ≺ " => TW.le
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X
local infixr:70 " ⊗ " => TW.comp
local infixr:80 " • " => TW.scale

open InnerProductSpace RealInnerProductSpace

abbrev SimpleSystemSpace (n : ℕ) := EuclideanSpace ℝ (Fin (n+1))
instance (n:ℕ) : AddCommGroup (SimpleSystemSpace n) := by infer_instance
noncomputable instance (n:ℕ) : Module ℝ (SimpleSystemSpace n) := by infer_instance
instance (n:ℕ) : TopologicalSpace (SimpleSystemSpace n) := by infer_instance

instance (n:ℕ) : Inhabited (SimpleSystemSpace n) := ⟨0⟩
variable {n : ℕ}


/-- The 1-dimensional subspace corresponding to the energy coordinate. -/
def energy_subspace : Subspace ℝ (SimpleSystemSpace n) :=
  ℝ ∙ (WithLp.toLp 2 (Fin.cons (1 : ℝ) (WithLp.ofLp (0 : EuclideanSpace ℝ (Fin n)))))

/-- The n-dimensional subspace corresponding to the work coordinates. -/
noncomputable def work_subspace : Subspace ℝ (SimpleSystemSpace n) := (energy_subspace).orthogonal

/-- Forward sector A_X := { Y | X ≺ Y } -/
def ForwardSector {Γ} (X : TW.State Γ) : Set (TW.State Γ) := { Y | X ≺ Y }

-- The full S2 Axiom suite, to be placed inside the SimpleSystemFamily class.

/-- The `IsSimpleSystem` structure holds the data for a single simple system: its identification
with a convex, open subset of an `(n+1)`-dimensional coordinate space (`SimpleSystemSpace n`).
It contains no axioms itself. -/
structure IsSimpleSystem (n : ℕ) (Γ : System) where
  space : Set (SimpleSystemSpace n)
  isOpen : IsOpen space
  isConvex : Convex ℝ space
  state_equiv : TW.State Γ ≃ Subtype space

/-- A `SimpleSystemFamily` is a collection of systems whose states are identified with points
in an `(n+1)`-dimensional coordinate space (`SimpleSystemSpace n`). The parameter `n`
corresponds to the number of so-called "work coordinates".

This class contains the axioms (A7, S1-S3) and the coherence axioms that govern
how simple systems behave under scaling and composition within this coordinate-based
framework. -/
class SimpleSystemFamily (n : ℕ) (is_in_family : System → Prop) where
  /-- Provides the `IsSimpleSystem` data structure for any system in the family. -/
  get_ss_inst (Γ : System) (h_in : is_in_family Γ) : IsSimpleSystem n Γ
  /-- The family is closed under positive scaling. -/
  scale_family_closed {Γ} (h_in : is_in_family Γ) {t : ℝ} (ht : 0 < t) :
    is_in_family (t • Γ)

  /-- **Coherence of Scaling and Coordinates (CSS)**: The coordinate map of the scaled
  system `t•Γ` applied to the abstractly scaled state `t•X` yields exactly the
  scalar product of `t` and the coordinates of `X`. This allows to connect abstract system
  algebra and concrete coordinate vector algebra. -/
  coord_of_scaled_state_eq_smul_coord {Γ} (h_in : is_in_family Γ) (X : TW.State Γ) {t : ℝ} (ht : 0 < t) :
    let ss_Γ := get_ss_inst Γ h_in
    let ss_tΓ := get_ss_inst (t • Γ) (scale_family_closed h_in ht)
    ss_tΓ.state_equiv (scale_state ht.ne' X) = t • (ss_Γ.state_equiv X).val

  /-- **A7 (Convex Combination)**: The state formed by composing two scaled-down simple
      systems is adiabatically accessible to the state corresponding to the convex
      combination of their coordinates. -/
  A7 {Γ} (h_in : is_in_family Γ) (X Y : TW.State Γ) {t : ℝ} (ht : 0 < t ∧ t < 1) :
    let ss := get_ss_inst Γ h_in
    let combo_state := comp_state (scale_state ht.1.ne' X, scale_state (sub_pos.mpr ht.2).ne' Y)
    let target_coord_val := t • (ss.state_equiv X).val + (1-t) • (ss.state_equiv Y).val
    have h_target_in_space : target_coord_val ∈ ss.space :=
      ss.isConvex (ss.state_equiv X).property (ss.state_equiv Y).property (le_of_lt ht.1) (le_of_lt (sub_pos.mpr ht.2)) (by ring)
    let target_state : TW.State Γ := ss.state_equiv.symm ⟨target_coord_val, h_target_in_space⟩
    TW.le combo_state target_state

  /-- **S1 (Irreversibility)**: For any state in a simple system, there exists another
      state that is strictly adiabatically accessible from it. -/
  S1 {Γ} (h_in : is_in_family Γ) (X : TW.State Γ) :
    ∃ Y : TW.State Γ, X ≺ Y ∧ ¬ (Y ≺ X)
  pressure_map {Γ} (h_in : is_in_family Γ) : TW.State Γ → EuclideanSpace ℝ (Fin n)

  /-- **S2.1 (Unique Tangent Plane):** For each state `X`, the forward sector `Aₓ` has a
  unique supporting hyperplane `Πₓ` at `X`. This plane has a finite slope with respect
  to the work coordinates (i.e., its normal vector is not purely a work vector). -/
  S2_Unique_Tangent_Plane {Γ} (h_in : is_in_family Γ) (X : TW.State Γ) :
    let ss := get_ss_inst Γ h_in
    let C_X : Set (SimpleSystemSpace n) :=
      Set.image (fun Y : TW.State Γ => (ss.state_equiv Y).val) (ForwardSector X)
    let x_coord : SimpleSystemSpace n := (ss.state_equiv X).val
    ∃! (f : (SimpleSystemSpace n) →L[ℝ] ℝ),
      ‖f‖ = 1 ∧
      (∀ y_coord ∈ C_X, f y_coord ≤ f x_coord) ∧
      -- finite slope: the normal is not orthogonal to the energy direction
      (let u : SimpleSystemSpace n :=
          (InnerProductSpace.toDual ℝ (SimpleSystemSpace n)).symm f
       let eE : SimpleSystemSpace n :=
          WithLp.toLp 2 (Fin.cons (1 : ℝ) (WithLp.ofLp (0 : EuclideanSpace ℝ (Fin n))))
       ⟪u, eE⟫_ℝ ≠ 0)

  /-- **S2.2 (Lipschitz Pressure):** The pressure `P(X)` is locally Lipschitz in coordinates. -/
  S2_Lipschitz_Pressure {Γ} (h_in : is_in_family Γ) :
    let ss := get_ss_inst Γ h_in
    -- Define P on the ambient space; only its restriction to ss.space matters.
    let P : SimpleSystemSpace n → SimpleSystemSpace n :=
      by
        classical
        -- total function on the ambient space; use by_cases for membership
        intro x
        by_cases hx : x ∈ ss.space
        · -- state corresponding to coordinates x
          let X : TW.State Γ := ss.state_equiv.symm ⟨x, hx⟩
          -- extract a supporting functional at X from S2 via classical choice
          let ex := S2_Unique_Tangent_Plane (Γ := Γ) h_in X
          let f : (SimpleSystemSpace n) →L[ℝ] ℝ := Classical.choose ex.exists
          -- normal vector and energy/work decomposition
          let u : SimpleSystemSpace n :=
            (InnerProductSpace.toDual ℝ (SimpleSystemSpace n)).symm f
          let eE : SimpleSystemSpace n :=
            WithLp.toLp 2 (Fin.cons (1 : ℝ) (WithLp.ofLp (0 : EuclideanSpace ℝ (Fin n))))
          let u_E : ℝ := ⟪u, eE⟫_ℝ
          let u_W : SimpleSystemSpace n := (work_subspace (n := n)).starProjection u
          -- define P(x)
          exact (-1 / u_E) • u_W
        · exact 0
    LocallyLipschitzOn ss.space P
  /-- **S2 Coherence**: Adiabatically equivalent states have the same pressure map.
      This ensures that the supporting hyperplanes for their forward sectors are parallel. -/
  S2_Coherence {Γ} (h_in : is_in_family Γ) {X Y : TW.State Γ} (h_equiv : X ≈ Y) :
    pressure_map h_in X = pressure_map h_in Y
  /-- **S3 (Connectedness of the Boundary)**: the boundary of the forward sector is path connected. -/
  S3_path_connected {Γ : System} (h_in : is_in_family Γ) (X : TW.State Γ) :
    let ss : IsSimpleSystem n Γ := get_ss_inst Γ h_in
    let coord_sector : Set (SimpleSystemSpace n) :=
      Set.image (fun (Y : TW.State Γ) => (ss.state_equiv Y).val) { Y | X ≺ Y }
    let boundary : Set (SimpleSystemSpace n) := frontier coord_sector
    let adia_points : Set (SimpleSystemSpace n) :=
      { p | p ∈ boundary ∧ ∃ Y : TW.State Γ, (ss.state_equiv Y).val = p ∧ X ≈ Y }
    IsPathConnected adia_points

/-- **Theorem 2.6 (Forward sectors are convex)** -
    If `Γ` is in a simple system family, the forward sector of any state `X ∈ Γ`
    is a convex set in the coordinate representation. -/
theorem forward_sectors_are_convex {n : ℕ} {is_in_family} [ssf : SimpleSystemFamily n is_in_family]
    {Γ : System} (h_in : is_in_family Γ) (X : TW.State Γ) :
    Convex ℝ (Set.image (fun Y => ((ssf.get_ss_inst Γ h_in).state_equiv Y).val) (ForwardSector X)) := by
  -- Let `ss` be the simple system instance for `Γ`.
  let ss := ssf.get_ss_inst Γ h_in
  -- Use the definition of Convex: `∀ y₁ y₂, y₁ ∈ S → y₂ ∈ S → ∀ a b, a≥0,b≥0,a+b=1 → a•y₁+b•y₂ ∈ S`
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  rcases hy₁ with ⟨Y₁, hY₁_in_sector, rfl⟩
  rcases hy₂ with ⟨Y₂, hY₂_in_sector, rfl⟩
  -- Define the target state Z by its coordinates, which are the convex combination.
  let Z_coord_val := a • (ss.state_equiv Y₁).val + b • (ss.state_equiv Y₂).val
  have hZ_in_space : Z_coord_val ∈ ss.space :=
    ss.isConvex (ss.state_equiv Y₁).property (ss.state_equiv Y₂).property ha hb hab
  let Z : TW.State Γ := ss.state_equiv.symm ⟨Z_coord_val, hZ_in_space⟩
  have h_chain : X ≺ Z := by
    by_cases ha0 : a = 0
    · have b1 : b = 1 := by simpa [ha0] using hab
      have Z_eq_Y₂ : Z = Y₂ := by
        apply ss.state_equiv.injective
        apply Subtype.ext
        simp [Z, Z_coord_val, ha0, b1]
      exact Z_eq_Y₂ ▸ hY₂_in_sector
    · by_cases hb0 : b = 0
      · have a1 : a = 1 := by simpa [hb0] using hab
        have Z_eq_Y₁ : Z = Y₁ := by
          apply ss.state_equiv.injective
          apply Subtype.ext
          simp [Z, Z_coord_val, a1, hb0]
        exact Z_eq_Y₁ ▸ hY₁_in_sector
      · -- Main case: 0 < a < 1 (which implies 0 < b < 1).
        have ha_pos : 0 < a := lt_of_le_of_ne' ha ha0
        have hb_pos : 0 < b := lt_of_le_of_ne' hb hb0
        have ha_lt_1 : a < 1 := by
          have := add_lt_add_left hb_pos a
          simpa [hab] using this
        have ha_bounds : 0 < a ∧ a < 1 := ⟨ha_pos, ha_lt_1⟩
        have hb_eq : b = 1 - a := by linarith
        calc
          X ≺ comp_state (scale_state ha_bounds.1.ne' X, scale_state (sub_pos.mpr ha_bounds.2).ne' X) :=
            (TW.A5 X ha_bounds).1
          _ ≺ comp_state (scale_state ha_bounds.1.ne' Y₁, scale_state (sub_pos.mpr ha_bounds.2).ne' Y₂) := by
            exact TW.A3 (TW.A4 ha_bounds.1 hY₁_in_sector) (TW.A4 (sub_pos.mpr ha_bounds.2) hY₂_in_sector)
          _ ≺ Z := by
            -- A7 is defined with `t`, here we use `a`.
            subst hb_eq
            exact SimpleSystemFamily.A7 h_in Y₁ Y₂ ha_bounds
  exact ⟨Z, h_chain, by simp [Z, Z_coord_val]; simp_all only [Equiv.apply_symm_apply, Z, ss, Z_coord_val]⟩

variable {n : ℕ} {is_in_family : System → Prop} [ssf : SimpleSystemFamily n is_in_family]

/-! ### Topological and Convex Geometry Lemmas -/

section TopologicalLemmas
open Convex
variable {E : Type*} [NormedAddCommGroup E]

/-- A cluster point of a set contained in a closed set must be in that closed set. -/
lemma clusterPt_subset_of_subset_isClosed {s t : Set E} {x : E}
    (hs : s ⊆ t) (ht : IsClosed t) (hx : ClusterPt x (Filter.principal s)) : x ∈ t := by
  have hx_cl : x ∈ closure s := mem_closure_iff_clusterPt.mpr hx
  exact (closure_minimal hs ht) hx_cl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Points on an open line segment are in the interior of a convex set containing the endpoints. -/
lemma openSegment_subset_interior_of_convex {s : Set E} (hs : Convex ℝ s)
    {x y : E} (hx : x ∈ interior s) (hy : y ∈ s) (_ : x ≠ y) :
    openSegment ℝ x y ⊆ interior s := by
  exact Convex.openSegment_interior_self_subset_interior hs hx hy

/-- Convex combination of interior point and boundary point stays in interior (except endpoint). -/
lemma convex_combo_interior_mem {s : Set E} (hs : Convex ℝ s)
    {x y : E} (hx : x ∈ interior s) (hy : y ∈ s) {t : ℝ} (ht : 0 < t ∧ t < 1) :
    (1 - t) • x + t • y ∈ interior s := by
  have hz_seg : (1 - t) • x + t • y ∈ openSegment ℝ x y := by
    rw [openSegment_eq_image]
    refine ⟨t, ht, rfl⟩
  by_cases hxy : x = y
  · subst hxy
    simp_all only [openSegment_same, Set.mem_singleton_iff]
  exact (openSegment_subset_interior_of_convex hs hx hy hxy) hz_seg

end TopologicalLemmas

/-! ### Convex Set Properties in Euclidean Space -/

section ConvexSetProperties

variable {n : ℕ}

/-- A convex set in finite-dimensional Euclidean space with nonempty interior has
    interior equal to the set minus its boundary. -/
lemma interior_eq_self_diff_frontier_of_convex {s : Set (SimpleSystemSpace n)}
    (_ : Convex ℝ s) (_ : (interior s).Nonempty) :
    interior s = s \ frontier s := by
  simp [self_diff_frontier]

/-- In a normed space, if a set contains a ball and is contained in a larger ball,
    then its interior is nonempty. -/
lemma interior_nonempty_of_ball_subset {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} {x : E} {r : ℝ}
    (hr : 0 < r) (h : Metric.ball x r ⊆ s) : (interior s).Nonempty := by
  use x
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (Metric.ball_mem_nhds x hr) h

/-- A convex set in a finite-dimensional space that contains a ball has nonempty interior. -/
lemma convex_has_interior_of_ball {s : Set (SimpleSystemSpace n)}
    (_ : Convex ℝ s) {x : SimpleSystemSpace n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x r ⊆ s) : (interior s).Nonempty :=
  interior_nonempty_of_ball_subset (E := SimpleSystemSpace n) hr hball

end ConvexSetProperties

/-- Build a state from a coordinate point in the simple-system space. -/
def state_of_coord {n : ℕ} {is_in_family : System → Prop} [ssf : SimpleSystemFamily n is_in_family]
    {Γ : System} (h_in : is_in_family Γ)
    (y : SimpleSystemSpace n)
    (hy : y ∈ (ssf.get_ss_inst Γ h_in).space) : TW.State Γ :=
  (ssf.get_ss_inst Γ h_in).state_equiv.symm ⟨y, hy⟩

@[simp] lemma state_of_coord_val {n : ℕ} {is_in_family : System → Prop} [ssf : SimpleSystemFamily n is_in_family]
    {Γ : System} (h_in : is_in_family Γ)
    (y : SimpleSystemSpace n)
    (hy : y ∈ (ssf.get_ss_inst Γ h_in).space) :
    ((ssf.get_ss_inst Γ h_in).state_equiv (state_of_coord (System := System) h_in y hy)).val = y := by
  dsimp [state_of_coord]
  simp

end LY
