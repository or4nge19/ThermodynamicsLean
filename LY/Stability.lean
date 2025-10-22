/-
Copyright (c) 2025 Matteo Cipollina All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LY.Axioms

/-!
# Formulations of the Stability Axiom (A6)

This file explores the stability axiom (A6) from the Lieb-Yngvason framework.
It provides:
- A specialized version of the sequential axiom A6 (`A6_spec`) where the
  two catalyst states are the same.
- A proof that the δ-ε formulation of stability can be derived from the
  sequential formulation (`stability_from_seq`).
-/

namespace LY

open Filter Tendsto
universe u v
variable {System : Type u} [TW : ThermoWorld System]
local infix:50 " ≺ " => TW.le

/-- Specialized A6 for Cancellation Law proof (Z₀ = Z₁). -/
lemma A6_spec {ΓX ΓY ΓZ} (X : TW.State ΓX) (Y : TW.State ΓY) (Z : TW.State ΓZ)
  (h_premise :
    ∃ (ε_seq : ℕ → ℝ) (hpos : ∀ n, 0 < ε_seq n),
      Filter.Tendsto ε_seq Filter.atTop (nhds 0) ∧
      (∀ n,
        TW.le
          (TW.state_of_comp_equiv.symm
            (X, (TW.state_of_scale_equiv (ne_of_gt (hpos n))).symm Z))
          (TW.state_of_comp_equiv.symm
            (Y, (TW.state_of_scale_equiv (ne_of_gt (hpos n))).symm Z)))) :
  TW.le X Y := by
  simpa using (TW.A6_seq X Y Z Z h_premise)

/-- (Derived) Stability A6 (δ–ε form) from the sequential axiom A6_seq (Z₀ = Z₁).
    We choose εₙ = δ / (n+2) so that εₙ < δ holds for all n (including n = 0). -/
lemma stability_from_seq
  {Γ₁ Γ₂ ΓZ} (X : TW.State Γ₁) (Y : TW.State Γ₂) (Z : TW.State ΓZ) :
  (∃ δ > 0, ∀ ε (hε : 0 < ε ∧ ε < δ),
      TW.le (TW.state_of_comp_equiv.symm (X, (TW.state_of_scale_equiv (ne_of_gt hε.1)).symm Z))
        (TW.state_of_comp_equiv.symm (Y, (TW.state_of_scale_equiv (ne_of_gt hε.1)).symm Z))) →
  TW.le X Y := by
  intro hδ
  rcases hδ with ⟨δ, hδpos, h_prop⟩
  -- Choose a sequence εₙ = δ / (n+2) (so denominator ≥ 2 and εₙ < δ).
  let ε_seq : ℕ → ℝ := fun n => δ / (n + 2 : ℝ)
  have hpos : ∀ n, 0 < ε_seq n := by
    intro n
    have hden_nat : 0 < n + 2 := Nat.succ_pos (n + 1)
    have hden : 0 < (n + 2 : ℝ) := by exact_mod_cast hden_nat
    exact div_pos hδpos hden
  have h_small : ∀ n, ε_seq n < δ := by
    intro n
    have hgt_nat : 1 < n + 2 := Nat.succ_lt_succ (Nat.succ_pos _)
    have hgt : (1 : ℝ) < (n + 2 : ℝ) := by exact_mod_cast hgt_nat
    have h_inv : (1 : ℝ) / (n + 2 : ℝ) < 1 := by
      have h := one_div_lt_one_div_of_lt (show 0 < (1 : ℝ) by norm_num) hgt
      simpa using h
    have h_mul := mul_lt_mul_of_pos_left h_inv hδpos
    simpa [ε_seq, one_div, div_eq_mul_inv] using h_mul
  have h_tend : Filter.Tendsto ε_seq Filter.atTop (nhds 0) := by
    have h_nat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have h_add : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 h_nat
    -- Inverse tends to 0
    have h_inv := (tendsto_inv_atTop_zero).comp h_add
    have h_inv' : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (nhds 0) := by
      simpa [one_div] using h_inv
    have h_mul := h_inv'.const_mul δ
    simpa [ε_seq, one_div, div_eq_mul_inv, Nat.cast_add, add_comm, add_left_comm, add_assoc] using h_mul
  refine (TW.A6_seq X Y Z Z) ?_
  refine ⟨ε_seq, hpos, h_tend, ?_⟩
  intro n
  exact h_prop _ ⟨hpos n, h_small n⟩

end LY
