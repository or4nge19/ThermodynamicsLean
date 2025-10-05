/-
Copyright (c) 2025 Matteo Cipollina All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LY.Axioms

/-!
# Algebraic Reorganization Lemmas

This file provides a set of lemmas for reorganizing compound states up to
adiabatic equivalence (`≈`). These "cast-free" lemmas are derived from the
coherence axioms (CA, CC, CSC, C1) and the coherence of casting (CCast),
allowing for more direct algebraic manipulation in proofs without handling
explicit `Equiv.cast` terms.
-/

namespace LY
universe u v
variable {System : Type u} [TW : ThermoWorld System]
local infix:50 " ≺ " => TW.le
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X

/-- A cast-free commutativity equivalence on compound states. (CC) -/
lemma comp_comm_equiv_clean {Γ₁ Γ₂} (X : TW.State Γ₁) (Y : TW.State Γ₂) :
    comp_state (X, Y) ≈ comp_state (Y, X) := by
  let h_eq := TW.comp_comm Γ₁ Γ₂
  let XY := comp_state (X, Y)
  let YX := comp_state (Y, X)
  -- CC: XY ≈ Cast(h_eq.symm) YX.
  have h_cc := TW.comp_comm_coherence X Y
  -- CCast: Cast(h_eq.symm) YX ≈ YX.
  have h_cast : (Equiv.cast (congrArg TW.State h_eq.symm) YX) ≈ YX :=
    thermo_equiv_symm (TW.state_equiv_coherence h_eq.symm YX)
  -- Combine: XY ≺ Cast ≺ YX and YX ≺ Cast⁻¹ ≺ XY.
  exact And.symm (thermo_equiv_trans' (id (And.symm h_cast)) h_cc)

/-- Helper for using CA: ((X, Y), Z) ≈ (X, (Y, Z)). (CA) -/
lemma assoc_equiv_R {Γ₁ Γ₂ Γ₃} (X : TW.State Γ₁) (Y : TW.State Γ₂) (Z : TW.State Γ₃) :
  comp_state (comp_state (X, Y), Z) ≈ comp_state (X, comp_state (Y, Z)) := by
  let L := comp_state (comp_state (X, Y), Z)
  let h_eq := TW.comp_assoc Γ₁ Γ₂ Γ₃
  -- CA: Cast(h_eq) L ≈ R.
  have h_coh := TW.comp_assoc_coherence X Y Z
  -- CCast: L ≈ Cast(h_eq) L.
  have h_cast := TW.state_equiv_coherence h_eq L
  -- Combine: L ≈ Cast ≈ R.
  exact thermo_equiv_trans' h_cast h_coh

/-- Helper for using CA: (X, (Y, Z)) ≈ ((X, Y), Z). (CA) -/
lemma assoc_equiv_L {Γ₁ Γ₂ Γ₃} (X : TW.State Γ₁) (Y : TW.State Γ₂) (Z : TW.State Γ₃) :
    comp_state (X, comp_state (Y, Z)) ≈ comp_state (comp_state (X, Y), Z) :=
  thermo_equiv_symm (assoc_equiv_R X Y Z)

/-- Lemma: ((A, X), (B, Z)) ≈ ((A, B), (X, Z)). Generalized Commutativity/Associativity.
    This proves that the algebraic structure holds up to adiabatic equivalence. -/
lemma quadruple_reorg_center {ΓA ΓB ΓX ΓZ}
    (A : TW.State ΓA) (B : TW.State ΓB) (X : TW.State ΓX) (Z : TW.State ΓZ) :
    comp_state (comp_state (A, X), comp_state (B, Z)) ≈
    comp_state (comp_state (A, B), comp_state (X, Z)) := by
  -- 1) ((A, X), (B, Z)) ≈ (A, (X, (B, Z))) [Assoc R (outer)]
  have h1 :
      comp_state (comp_state (A, X), comp_state (B, Z))
      ≈ comp_state (A, comp_state (X, comp_state (B, Z))) :=
    assoc_equiv_R A X (comp_state (B, Z))
  -- 2) (A, (X, (B, Z))) ≈ (A, ((X, B), Z)) [Assoc R (inner), lifted by A3]
  have h2_inner :
      comp_state (comp_state (X, B), Z) ≈ comp_state (X, comp_state (B, Z)) :=
    assoc_equiv_R X B Z
  have h2 :
      comp_state (A, comp_state (X, comp_state (B, Z)))
      ≈ comp_state (A, comp_state (comp_state (X, B), Z)) :=
    ⟨ TW.A3 (thermo_le_refl A) (thermo_equiv_symm h2_inner).1
    , TW.A3 (thermo_le_refl A) (thermo_equiv_symm h2_inner).2 ⟩
  -- 3) Swap center (X,B) → (B,X), lifted by Z then by A
  have h3_inner : comp_state (X, B) ≈ comp_state (B, X) :=
    comp_comm_equiv_clean X B
  have h3_lift1 :
      comp_state (comp_state (X, B), Z) ≈ comp_state (comp_state (B, X), Z) :=
    ⟨ TW.A3 h3_inner.1 (thermo_le_refl Z)
    , TW.A3 h3_inner.2 (thermo_le_refl Z) ⟩
  have h3 :
      comp_state (A, comp_state (comp_state (X, B), Z))
      ≈ comp_state (A, comp_state (comp_state (B, X), Z)) :=
    ⟨ TW.A3 (thermo_le_refl A) h3_lift1.1
    , TW.A3 (thermo_le_refl A) h3_lift1.2 ⟩
  -- 4) ((B, X), Z) ≈ (B, (X, Z)), lifted by A3 on A
  have h4_inner :
      comp_state (comp_state (B, X), Z) ≈ comp_state (B, comp_state (X, Z)) :=
    assoc_equiv_R B X Z
  have h4 :
      comp_state (A, comp_state (comp_state (B, X), Z))
      ≈ comp_state (A, comp_state (B, comp_state (X, Z))) :=
    ⟨ TW.A3 (thermo_le_refl A) h4_inner.1
    , TW.A3 (thermo_le_refl A) h4_inner.2 ⟩
  -- 5) (A, (B, (X, Z))) ≈ ((A, B), (X, Z)) [Assoc L (outer)]
  have h5 :
      comp_state (A, comp_state (B, comp_state (X, Z)))
      ≈ comp_state (comp_state (A, B), comp_state (X, Z)) :=
    assoc_equiv_L A B (comp_state (X, Z))
  -- Chain all steps
  exact
    thermo_equiv_trans' h1
      (thermo_equiv_trans' h2 (thermo_equiv_trans' h3 (thermo_equiv_trans' h4 h5)))

/-- Lemma: ((A, B), (Y, Z)) ≈ (A, ((B, Y), Z)). Pure Associativity reorganization. -/
lemma quadruple_reorg_assoc {ΓA ΓB ΓY ΓZ}
    (A : TW.State ΓA) (B : TW.State ΓB) (Y : TW.State ΓY) (Z : TW.State ΓZ) :
    comp_state (comp_state (A, B), comp_state (Y, Z)) ≈
    comp_state (A, comp_state (comp_state (B, Y), Z)) := by
  -- 1. ((A, B), (Y, Z)) ≈ (A, (B, (Y, Z))) [Assoc R outer]
  have h1 :
      comp_state (comp_state (A, B), comp_state (Y, Z)) ≈
      comp_state (A, comp_state (B, comp_state (Y, Z))) :=
    assoc_equiv_R A B (comp_state (Y, Z))
  -- 2. (B, (Y, Z)) ≈ ((B, Y), Z) [Assoc R inner], oriented correctly
  have h2_inner :
      comp_state (B, comp_state (Y, Z)) ≈ comp_state (comp_state (B, Y), Z) :=
    thermo_equiv_symm (assoc_equiv_R B Y Z)
  -- 3. Lift to (A, ...) using A3
  have h2 :
      comp_state (A, comp_state (B, comp_state (Y, Z))) ≈
      comp_state (A, comp_state (comp_state (B, Y), Z)) :=
    ⟨ TW.A3 (thermo_le_refl A) h2_inner.1
    , TW.A3 (thermo_le_refl A) h2_inner.2 ⟩
  -- Chain: h1 then h2
  exact thermo_equiv_trans' h1 h2

/-- A cast-free scaling composition equivalence. (CSC) -/
lemma scale_comp_coherence_clean {t : ℝ} (ht : t ≠ 0) {Γ₁ Γ₂} (X : TW.State Γ₁) (Y : TW.State Γ₂) :
  scale_state ht (comp_state (X, Y)) ≈ comp_state (scale_state ht X, scale_state ht Y) := by
  let tXY := scale_state ht (comp_state (X, Y))
  let h_eq := TW.scale_distrib_comp t Γ₁ Γ₂
  -- CSC: Cast(h_eq) tXY ≈ (tX, tY).
  have h_CSC := TW.scale_comp_coherence ht X Y
  -- CCast: tXY ≈ Cast(h_eq) tXY.
  have h_cast := TW.state_equiv_coherence h_eq tXY
  exact thermo_equiv_trans' h_cast h_CSC

/-- Helper: 1•X ≈ X (C1 Coherence, cast-free). -/
lemma one_smul_coherence_clean {Γ} (X : TW.State Γ) :
    scale_state (by norm_num : (1:ℝ) ≠ 0) X ≈ X := by
  let X_1 := scale_state (by norm_num : (1:ℝ) ≠ 0) X
  let h_eq := TW.one_smul Γ
  -- C1: Cast(h_eq) X_1 ≈ X.
  have h_C1 := TW.one_smul_coherence X
  -- CCast: X_1 ≈ Cast(h_eq) X_1.
  have h_cast := TW.state_equiv_coherence h_eq X_1
  exact thermo_equiv_trans' h_cast h_C1

/-- Casting along a system equality preserves adiabatic equivalence. (CCast) -/
lemma cast_preserves_equiv_simple {Γ₁ Γ₂} (h_eq : Γ₁ = Γ₂)
    {X : TW.State Γ₁} {Y : TW.State Γ₁} (h : X ≈ Y) :
    Equiv.cast (congrArg TW.State h_eq) X ≈ Equiv.cast (congrArg TW.State h_eq) Y := by
  have hCX : X ≈ Equiv.cast (congrArg TW.State h_eq) X := TW.state_equiv_coherence h_eq X
  have hCY : Y ≈ Equiv.cast (congrArg TW.State h_eq) Y := TW.state_equiv_coherence h_eq Y
  exact thermo_equiv_trans' (thermo_equiv_trans' (thermo_equiv_symm hCX) h) hCY

end LY
