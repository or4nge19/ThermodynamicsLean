/-
Copyright (c) 2025 Matteo Cipollina All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LY.Consequences

/-!
# The Entropy Principle

This file defines the abstract concept of an entropy function `S` for a given
`ThermoWorld`, as described in Section II.D of the Lieb-Yngvason paper.

## Main Definitions
- `AllStates`: A Sigma type representing the collection of all possible
  states in the `ThermoWorld`. This serves as the domain for the entropy function.
- `EntropyFunction`: A structure containing a function `S : AllStates → ℝ`
  and the three properties it must satisfy:
    a) **Monotonicity**: `X ≺ Y ↔ S(X) ≤ S(Y)` for comparable states.
    b) **Additivity**: `S(X, Y) = S(X) + S(Y)`.
    c) **Extensivity**: `S(t•X) = t * S(X)`.
-/

namespace LY

universe u v
variable {System : Type u} [TW : ThermoWorld System]
local infix:50 " ≺ " => TW.le
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X
local infix:50 " ≺≺ " => StrictlyPrecedes

/-- The domain of an entropy function S (Sigma type). -/
def AllStates (System : Type u) [TW : ThermoWorld System] :=
  Σ (Γ : System), TW.State Γ

/-- The Entropy Principle (Definition). -/
structure EntropyFunction (System : Type u) [TW : ThermoWorld System] where
  S : AllStates System → ℝ

  /-- a) Monotonicity (If X and Y are comparable) -/
  Monotonicity {Γ₁ Γ₂} (X : TW.State Γ₁) (Y : TW.State Γ₂) :
    Comparable X Y → (TW.le (Γ₁ := Γ₁) (Γ₂ := Γ₂) X Y ↔ (S ⟨Γ₁, X⟩ ≤ S ⟨Γ₂, Y⟩))

  /-- b) Additivity -/
  Additivity {Γ₁ Γ₂} (X : TW.State Γ₁) (Y : TW.State Γ₂) :
    S ⟨TW.comp Γ₁ Γ₂, (TW.state_of_comp_equiv).symm (X, Y)⟩ = S ⟨Γ₁, X⟩ + S ⟨Γ₂, Y⟩

  /-- c) Extensivity (Scaling) -/
  Extensivity {Γ} (X : TW.State Γ) {t : ℝ} (ht : 0 < t) :
    S ⟨TW.scale t Γ, (TW.state_of_scale_equiv (ne_of_gt ht)).symm X⟩ = t * S ⟨Γ, X⟩

lemma entropy_equiv_iff_eq {E : EntropyFunction System} {Γ₁ Γ₂} (X : TW.State Γ₁) (Y : TW.State Γ₂) (h_comp : Comparable X Y) :
  (X ≈ Y) ↔ E.S ⟨Γ₁, X⟩ = E.S ⟨Γ₂, Y⟩ := by
  rw [E.Monotonicity X Y h_comp]
  have h_comp_symm : Comparable Y X := Or.symm h_comp
  rw [E.Monotonicity Y X h_comp_symm]
  exact le_antisymm_iff.symm

lemma entropy_strict_iff_lt {E : EntropyFunction System} {Γ₁ Γ₂} (X : TW.State Γ₁) (Y : TW.State Γ₂) (h_comp : Comparable X Y) :
  X ≺≺ Y ↔ E.S ⟨Γ₁, X⟩ < E.S ⟨Γ₂, Y⟩ := by
  rw [StrictlyPrecedes]
  rw [E.Monotonicity X Y h_comp]
  have h_comp_symm : Comparable Y X := Or.symm h_comp
  rw [E.Monotonicity Y X h_comp_symm]
  -- S(X) ≤ S(Y) ∧ ¬(S(Y) ≤ S(X)) ↔ S(X) < S(Y)
  exact Iff.symm lt_iff_le_not_ge

end LY
