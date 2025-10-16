/-
Copyright (c) 2025 Matteo Cipollina All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LY.Axioms
import LY.Stability
import LY.Algebra
import LY.Recombination

/-!
# The Cancellation Law (Theorem 2.1)

This file provides the proof of the Cancellation Law, which states that
if `(X, Z) ≺ (Y, Z)`, then `X ≺ Y`.

The proof relies on:
- **Axiom A6 (Stability)**: To eliminate an infinitesimal catalyst.
- **The Recombination Lemma**: To additively manipulate scaled states.
- **Algebraic Reorganization**: To reorder compound states.
- **Axiom A4 (Scaling Invariance)**: To scale relations.

The core of the proof involves constructing a sequence of states `S(k)` that
interpolates between `(X, ε'•Z)` and `(Y, ε'•Z)` and showing `S(k) ≺ S(k+1)`.
The transitivity of `≺` establishes the relation between the endpoints, and
A6 is used to remove the catalyst `ε'•Z`. The `catalyst_amplification` lemma
is also proven and used in the final step.
-/

namespace LY

universe u v
variable {System : Type u} [TW : ThermoWorld System]
local infix:50 " ≺ " => TW.le
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X
local infixr:70 " ⊗ " => TW.comp
local infixr:80 " • " => TW.scale

/-! ### The Cancellation Law (Theorem 2.1)
Proof structure: Chain argument using A6, generalized recombination, and algebraic reorganization.
-/

/-- Helper lemma: (ε'•X, ε'•Z) ≺ (ε'•Y, ε'•Z). Follows from A4 and CSC coherence. -/
lemma cancellation_scaled_step {ΓX ΓY ΓZ} (X : TW.State ΓX) (Y : TW.State ΓY) (Z : TW.State ΓZ)
    (h_main : comp_state (X, Z) ≺ comp_state (Y, Z))
    {ε' : ℝ} (hε'_pos : 0 < ε') :
    comp_state (scale_state hε'_pos.ne' X, scale_state hε'_pos.ne' Z) ≺
    comp_state (scale_state hε'_pos.ne' Y, scale_state hε'_pos.ne' Z) := by
  -- 1. Scale the main hypothesis (A4): ε'•(X, Z) ≺ ε'•(Y, Z)
  have h_scaled := TW.A4 hε'_pos h_main

  -- 2. Apply CSC Coherence: ε'•(X, Z) ≈ (ε'•X, ε'•Z) (after casting).
  let ε'XZ := scale_state hε'_pos.ne' (comp_state (X, Z))
  let ε'X_ε'Z := comp_state (scale_state hε'_pos.ne' X, scale_state hε'_pos.ne' Z)
  have h_CSC_L : ε'XZ ≈ ε'X_ε'Z := by
    let h_eq := TW.scale_distrib_comp ε' ΓX ΓZ
    -- CSC: Cast(h_eq) (ε'•(X,Z)) ≈ (ε'•X, ε'•Z).
    have h_CSC_raw := TW.scale_comp_coherence hε'_pos.ne' X Z
    -- CCast: ε'•(X,Z) ≈ Cast(h_eq) (ε'•(X,Z)).
    have h_cast := TW.state_equiv_coherence h_eq ε'XZ
    exact thermo_equiv_trans' h_cast h_CSC_raw
  -- 3. Apply CSC Coherence to the Right side similarly.
  let ε'YZ := scale_state hε'_pos.ne' (comp_state (Y, Z))
  let ε'Y_ε'Z := comp_state (scale_state hε'_pos.ne' Y, scale_state hε'_pos.ne' Z)
  have h_CSC_R : ε'YZ ≈ ε'Y_ε'Z := by
    let h_eq := TW.scale_distrib_comp ε' ΓY ΓZ
    have h_CSC_raw := TW.scale_comp_coherence hε'_pos.ne' Y Z
    have h_cast := TW.state_equiv_coherence h_eq ε'YZ
    exact thermo_equiv_trans' h_cast h_CSC_raw
  -- 4. Combine using transitivity: (ε'•X, ε'•Z) ≺ ε'•(X, Z) ≺ ε'•(Y, Z) ≺ (ε'•Y, ε'•Z).
  exact le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_CSC_L) h_scaled) h_CSC_R

/-- Archimedean property: For 0 < ε < 1 there exists n ≥ 1 with ε' = 1/n satisfying 0 < ε' ≤ ε. -/
lemma exists_inv_nat_le_eps {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
  ∃ n : Nat, 1 ≤ n ∧ 0 < (1 / (n : ℝ)) ∧ (1 / (n : ℝ)) ≤ ε := by
  -- ∃ n, 1/ε < n
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  -- Since ε < 1, 1 ≤ 1/ε.
  have hε_le1 : ε ≤ 1 := le_of_lt hε1
  have h_one_le_inv : (1 : ℝ) ≤ 1 / ε := one_le_one_div hε hε_le1
  -- Hence n ≥ 1.
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) < n := lt_of_le_of_lt h_one_le_inv hn
    exact_mod_cast this.le
  -- n > 0 in ℝ.
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn1
  -- 1/n > 0 and 1/n ≤ ε.
  refine ⟨n, hn1, one_div_pos.mpr hn_pos, (one_div_le hε hn_pos).mp (le_of_lt hn)⟩

/-! ### The Step Lemma S(k) ≺ S(k+1) -/

/-- Abbreviation for the right-associated triple. This structure is used for S(k). -/
def tripleR {ΓA ΓB ΓC}
  (A : TW.State ΓA) (B : TW.State ΓB) (C : TW.State ΓC) :=
  comp_state (A, comp_state (B, C))

set_option linter.unusedVariables false in
/-- Definition of the state S(k) = ( (1 - k ε')•X, k ε'•Y, ε'•Z ), right-associated. -/
noncomputable def S_of (ε' : ℝ) {ΓX ΓY ΓZ}
  (X : TW.State ΓX) (Y : TW.State ΓY) (Z : TW.State ΓZ) (a b c : ℝ)
  (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :=
  tripleR (gscale_state ha X) (gscale_state hb Y) (gscale_state hc Z)

/-- The main step of the chain argument: S(k) ≺ S(k+1).
    This proof relies heavily on algebraic reorganization (CA, CC) and generalized recombination. -/
lemma S_step
  {ΓX ΓY ΓZ} (X : TW.State ΓX) (Y : TW.State ΓY) (Z : TW.State ΓZ)
  (h_main : comp_state (X, Z) ≺ comp_state (Y, Z))
  {n k : Nat} {ε' : ℝ} (hε'_pos : 0 < ε') (heq : ε' = 1 / (n : ℝ)) (hk : k < n) :
  -- Define coefficients for S(k) and S(k+1).
  let a_k  := 1 - (k       : ℝ) * ε'
  let a_k1 := 1 - (k.succ  : ℝ) * ε'
  let b_k  := (k : ℝ) * ε'
  let b_k1 := (k.succ : ℝ) * ε'
  -- Define non-negativity proofs required for S_of.
  let hn_ne0 : (n : ℝ) ≠ 0 := by
    have hne : ε' ≠ 0 := ne_of_gt hε'_pos
    intro h; apply hne; simp [heq, h]
  let ha_k_nonneg : 0 ≤ a_k := by
    have hk_le_n_nat : k ≤ n := Nat.le_of_lt hk
    have hk_le_n : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk_le_n_nat
    have hk_mul_le_one : (k : ℝ) * ε' ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hk_le_n (le_of_lt hε'_pos)
      simpa [heq, hn_ne0] using this
    exact sub_nonneg.mpr hk_mul_le_one
  let ha_k1_nonneg : 0 ≤ a_k1 := by
    have hk1_le_n_nat : k.succ ≤ n := Nat.succ_le_of_lt hk
    have hk1_le_n : (k.succ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk1_le_n_nat
    have hks_mul_le_one : (k.succ : ℝ) * ε' ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hk1_le_n (le_of_lt hε'_pos)
      simpa [heq, hn_ne0] using this
    exact sub_nonneg.mpr hks_mul_le_one
  let hb_k_nonneg : 0 ≤ b_k  := mul_nonneg (by exact_mod_cast (Nat.cast_nonneg k))        (le_of_lt hε'_pos)
  let hb_k1_nonneg : 0 ≤ b_k1 := mul_nonneg (by exact_mod_cast (Nat.cast_nonneg k.succ)) (le_of_lt hε'_pos)
  -- The step S(k) ≺ S(k+1).
  S_of ε' X Y Z a_k b_k ε' ha_k_nonneg hb_k_nonneg (le_of_lt hε'_pos)
  ≺
  S_of ε' X Y Z a_k1 b_k1 ε' ha_k1_nonneg hb_k1_nonneg (le_of_lt hε'_pos) := by
  -- Introduce locals.
  intros a_k a_k1 b_k b_k1 hn_ne0 ha_k_nonneg ha_k1_nonneg hb_k_nonneg hb_k1_nonneg
  have hε'_nonneg := le_of_lt hε'_pos
  -- Algebra: a_k = a_k1 + ε', b_k1 = b_k + ε'
  have hadd  : a_k = a_k1 + ε' := by simp [a_k, a_k1, Nat.cast_succ]; ring
  have hbadd : b_k1 = b_k + ε' := by simp [b_k1, b_k, Nat.cast_succ]; ring
  -- Local scaled states.
  let Ak  := gscale_state ha_k_nonneg X
  let Ak1 := gscale_state ha_k1_nonneg X
  let Bk  := gscale_state hb_k_nonneg Y
  let Bk1 := gscale_state hb_k1_nonneg Y
  let EZ  := gscale_state hε'_nonneg Z
  let εX  := gscale_state hε'_nonneg X
  let εY  := gscale_state hε'_nonneg Y
  -- 1. Recombine on X: Ak ≈ (Ak1, εX).
  have h_recomb_X : Ak ≈ comp_state (Ak1, εX) := by
    -- Align Ak to (a_k1+ε') via generalized CEq for gscale_state.
    have h_eq_add : a_k = a_k1 + ε' := hadd
    have h_align : Ak ≈ gscale_state (add_nonneg ha_k1_nonneg hε'_nonneg) X := by
      exact gscale_eq_coherence hadd X ha_k_nonneg (add_nonneg ha_k1_nonneg hε'_nonneg)
    -- Generalized recombination on X.
    have h_gr :
      gscale_state (add_nonneg ha_k1_nonneg hε'_nonneg) X
        ≈ comp_state (gscale_state ha_k1_nonneg X, gscale_state hε'_nonneg X) :=
      generalized_recombination_lemma ha_k1_nonneg hε'_nonneg (Γ := ΓX) X
    -- Chain.
    have h2 : gscale_state (add_nonneg ha_k1_nonneg hε'_nonneg) X ≈ comp_state (Ak1, εX) := by
      simpa [Ak1, εX] using h_gr
    exact thermo_equiv_trans' h_align h2
  -- 1'. Lift into the triple using A3.
  have hL1 : tripleR Ak Bk EZ ≈ comp_state (comp_state (Ak1, εX), comp_state (Bk, EZ)) := by
    exact ⟨TW.A3 h_recomb_X.1 (thermo_le_refl _), TW.A3 h_recomb_X.2 (thermo_le_refl _)⟩
  -- 2. Reorganize center blocks.
  have h_reorg_center := quadruple_reorg_center Ak1 Bk εX EZ
  have hL2 := thermo_equiv_trans' hL1 h_reorg_center
  -- 3. Scaled Cancellation on (εX, EZ) ≺ (εY, EZ).
  have h_pair : comp_state (εX, EZ) ≺ comp_state (εY, EZ) := by
    -- Normalize gscale_state to scale_state and use cancellation_scaled_step.
    have h_scaled :=
      cancellation_scaled_step X Y Z h_main hε'_pos
    simpa [εX, εY, EZ, gscale_state_pos hε'_nonneg hε'_pos]
      using h_scaled
  -- 5. Recombine on Y: (Bk, εY) ≈ Bk1.
  have h_recomb_Y : comp_state (Bk, εY) ≈ Bk1 := by
    -- Generalized recombination for Y, oriented towards (Bk, εY).
    have hgr :
      gscale_state (add_nonneg hb_k_nonneg hε'_nonneg) Y
        ≈ comp_state (Bk, εY) :=
      by
        have := generalized_recombination_lemma hb_k_nonneg hε'_nonneg (Γ := ΓY) Y
        -- This gives (b_k+ε')•Y ≈ (b_k•Y, ε'•Y) = (Bk, εY).
        simpa [Bk, εY] using this
    -- Align (b_k+ε') to b_k1 via CEq for gscale_state using hbadd.
    have h_eqb : b_k + ε' = b_k1 := by simp [hbadd]
    have h_align_b :
      gscale_state (add_nonneg hb_k_nonneg hε'_nonneg) Y ≈ Bk1 := by
      -- gscale_state (b_k + ε') Y ≈ gscale_state b_k1 Y = Bk1
      have h :=
        gscale_eq_coherence (Γ := ΓY) (X := Y)
          (h_eq := h_eqb) (ht₁ := add_nonneg hb_k_nonneg hε'_nonneg) (ht₂ := hb_k1_nonneg)
      simpa [Bk1] using h
    -- Chain: (Bk, εY) ≈ (b_k+ε')•Y ≈ b_k1•Y = Bk1.
    exact thermo_equiv_trans' (thermo_equiv_symm hgr) h_align_b
  -- 5'. Lift recombination on the right tail and then reassociate.
  have h_inner_lift :
    comp_state (comp_state (Bk, εY), EZ) ≈ comp_state (Bk1, EZ) :=
    ⟨TW.A3 h_recomb_Y.1 (thermo_le_refl EZ), TW.A3 h_recomb_Y.2 (thermo_le_refl EZ)⟩
  have hR1 :
    comp_state (Ak1, comp_state (comp_state (Bk, εY), EZ)) ≈
    comp_state (Ak1, comp_state (Bk1, EZ)) :=
    ⟨TW.A3 (thermo_le_refl Ak1) h_inner_lift.1, TW.A3 (thermo_le_refl Ak1) h_inner_lift.2⟩
  -- 4. Reassociate: ((Ak1, Bk), (εY, EZ)) ≈ (Ak1, ((Bk, εY), EZ)).
  have h_assoc := quadruple_reorg_assoc Ak1 Bk εY EZ
  -- Middle monotone step lifted by A3: replace (εX, EZ) with (εY, EZ).
  have h_middle :
    comp_state (comp_state (Ak1, Bk), comp_state (εX, EZ)) ≺
    comp_state (comp_state (Ak1, Bk), comp_state (εY, EZ)) :=
    TW.A3 (thermo_le_refl (comp_state (Ak1, Bk))) h_pair
  -- Chain to conclusion.
  have hL3 :
    tripleR Ak Bk EZ ≺
    comp_state (comp_state (Ak1, Bk), comp_state (εY, EZ)) :=
    le_of_equiv_le hL2 h_middle
  have hL4 :
    tripleR Ak Bk EZ ≺
    comp_state (Ak1, comp_state (comp_state (Bk, εY), EZ)) :=
    le_of_le_equiv hL3 h_assoc
  exact le_of_le_equiv hL4 hR1

/-! ### Catalyst Amplification (Lemma 2.2) -/

/-- Catalyst Amplification: If (X, tZ) ≺ (Y, tZ) and 0 < t ≤ s, then (X, sZ) ≺ (Y, sZ). -/
lemma catalyst_amplification {ΓX ΓY ΓZ} (X : TW.State ΓX) (Y : TW.State ΓY) (Z : TW.State ΓZ)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (h_le : t ≤ s)
    (h_hyp : comp_state (X, scale_state ht.ne' Z) ≺ comp_state (Y, scale_state ht.ne' Z)) :
    comp_state (X, scale_state hs.ne' Z) ≺ comp_state (Y, scale_state hs.ne' Z) := by
  -- If t = s, transport the hypothesis along scaling-equality coherence.
  rcases eq_or_lt_of_le h_le with (h_eq | h_lt)
  · -- Build equivalence tZ ≈ sZ from t = s using CCast and CEq, then lift into pairs via A3.
    let tZ := scale_state ht.ne' Z
    let sZ := scale_state hs.ne' Z
    let h_sys_eq := congrArg (fun r => TW.scale r ΓZ) h_eq
    have h_cast_t : tZ ≈ (Equiv.cast (congrArg TW.State h_sys_eq) tZ) :=
      TW.state_equiv_coherence h_sys_eq tZ
    have h_ceq_ts :
        (Equiv.cast (congrArg TW.State h_sys_eq) tZ) ≈ sZ :=
      TW.scale_eq_coherence (Γ := ΓZ) (X := Z) (h_eq := h_eq) (ht₁ := ht.ne')
    have h_tZ_sZ : tZ ≈ sZ := thermo_equiv_trans' h_cast_t h_ceq_ts
    -- Lift equivalences into compositions with X and Y via A3.
    have h_X_pair :
        comp_state (X, tZ) ≈ comp_state (X, sZ) :=
      ⟨TW.A3 (thermo_le_refl X) h_tZ_sZ.1, TW.A3 (thermo_le_refl X) h_tZ_sZ.2⟩
    have h_Y_pair :
        comp_state (Y, tZ) ≈ comp_state (Y, sZ) :=
      ⟨TW.A3 (thermo_le_refl Y) h_tZ_sZ.1, TW.A3 (thermo_le_refl Y) h_tZ_sZ.2⟩
    -- Transport the hypothesis along these equivalences.
    exact le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_X_pair) h_hyp) h_Y_pair
  · -- t < s. Let stm = s - t > 0.
    have h_stm_pos : 0 < s - t := sub_pos.mpr h_lt
    let tZ := scale_state ht.ne' Z
    let sZ := scale_state hs.ne' Z
    let stmZ := scale_state h_stm_pos.ne' Z
    let U := scale_state (add_pos ht h_stm_pos).ne' Z
    -- 1) s = t + (s - t): relate sZ to U using CEq and CCast.
    have h_sum_eq : s = t + (s - t) := by ring
    let h_sys_eq := congrArg (fun r => TW.scale r ΓZ) h_sum_eq
    have h_cast_s : sZ ≈ (Equiv.cast (congrArg TW.State h_sys_eq) sZ) :=
      TW.state_equiv_coherence h_sys_eq sZ
    have h_ceq_s :
        (Equiv.cast (congrArg TW.State h_sys_eq) sZ) ≈ U :=
      TW.scale_eq_coherence (Γ := ΓZ) (X := Z) (h_eq := h_sum_eq) (ht₁ := hs.ne')
    have h_sZ_U : sZ ≈ U :=
      ⟨thermo_le_trans h_cast_s.1 h_ceq_s.1, thermo_le_trans h_ceq_s.2 h_cast_s.2⟩
    -- 2) Recombination for s = t + (s - t): U ≈ (tZ, stmZ).
    have h_recomb := recombination_lemma ht h_stm_pos Z
    have h_recomb_sZ : sZ ≈ comp_state (tZ, stmZ) :=
      thermo_equiv_trans' h_sZ_U h_recomb
    -- 3) Lift recombination into the composition (A3).
    -- (X, sZ) ≈ (X, (tZ, stmZ))
    have h_LX : comp_state (X, sZ) ≈ comp_state (X, comp_state (tZ, stmZ)) :=
      ⟨TW.A3 (thermo_le_refl X) h_recomb_sZ.1, TW.A3 (thermo_le_refl X) h_recomb_sZ.2⟩
    -- (Y, sZ) ≈ (Y, (tZ, stmZ))
    have h_RY : comp_state (Y, sZ) ≈ comp_state (Y, comp_state (tZ, stmZ)) :=
      ⟨TW.A3 (thermo_le_refl Y) h_recomb_sZ.1, TW.A3 (thermo_le_refl Y) h_recomb_sZ.2⟩
    -- 4) Associativity (CA): (A, (B, C)) ≈ ((A, B), C).
    have h_assoc_L := assoc_equiv_L X tZ stmZ
    have h_assoc_R := assoc_equiv_L Y tZ stmZ
    -- 5) Apply hypothesis via A3: ((X, tZ), stmZ) ≺ ((Y, tZ), stmZ).
    have h_step := TW.A3 h_hyp (thermo_le_refl stmZ)
    -- 6) Combine the chain:
    -- (X, sZ) ≈ (X, (tZ, stmZ)) ≈ ((X, tZ), stmZ) ≺ ((Y, tZ), stmZ) ≈ (Y, (tZ, stmZ)) ≈ (Y, sZ).
    have h_left := le_of_equiv_le (thermo_equiv_trans' h_LX h_assoc_L) h_step
    have h_right_equiv := thermo_equiv_trans' (thermo_equiv_symm h_assoc_R) (thermo_equiv_symm h_RY)
    exact le_of_le_equiv h_left h_right_equiv

/-! ### Cancellation Law -/

set_option linter.unusedVariables false in
-- Helper to define the coefficients and their nonnegativity proofs.
lemma coeffs_ok (n k : Nat) (hkn : k ≤ n) (hn1 : 1 ≤ n) :
  let ε' := 1 / (n:ℝ)
  let hn_pos : 0 < (n:ℝ) := by exact_mod_cast hn1
  0 < ε' ∧ 0 ≤ (1 - (k:ℝ) * ε') ∧ 0 ≤ (k:ℝ) * ε' := by
  intros ε' hn_pos
  have hε'_pos : 0 < ε' := one_div_pos.mpr hn_pos
  have hε'_nonneg := le_of_lt hε'_pos
  have hk_nonneg : 0 ≤ (k:ℝ) := by exact_mod_cast Nat.cast_nonneg k
  have hb_nonneg := mul_nonneg hk_nonneg hε'_nonneg
  have hk_le_n : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hk_mul_le_one : (k : ℝ) * ε' ≤ 1 := by
    have hdiv : (k : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hn_pos).mpr hk_le_n
    simp_rw [ε', ← div_eq_mul_one_div]; assumption
  have ha_nonneg := sub_nonneg.mpr hk_mul_le_one
  exact ⟨hε'_pos, ha_nonneg, hb_nonneg⟩

-- Heterogeneous chain fold for dependently typed states.
lemma generalized_chain_fold' (Start End : (Σ (Γ : System), TW.State Γ))
      (P : Nat → (Σ (Γ : System), TW.State Γ)) (n : Nat)
      (h_start : P 0 = Start) (h_end : P n = End)
      (h_step : ∀ k, k < n → TW.le (P k).2 (P (k+1)).2) :
      TW.le Start.2 End.2 := by
  -- Induction on n, generalizing over End and the dependent data.
  revert End h_end h_step
  induction n with
  | zero =>
    intro End h_end h_step
    -- n=0. Start = P 0 = End.
    have h_eq : Start = End := by
      simpa [h_start] using h_end
    -- Rewrite End to Start and finish by reflexivity.
    rw [← h_eq]
    exact thermo_le_refl (Start.2)
  | succ n' ih =>
    intro End h_end h_step
    -- First, chain from P 0 to P n' using the IH with End := P n'.
    have h_ih : TW.le Start.2 (P n').2 :=
      ih (End := P n') (h_end := rfl)
         (h_step := fun k hk => h_step k (lt_trans hk (Nat.lt_succ_self n')))
    -- Then take the last step P n' ≺ P (n'+1) and rewrite End via h_end.
    have h_last : TW.le (P n').2 End.2 := by
      have h := h_step n' (Nat.lt_succ_self n')
      cases h_end
      simpa using h
    -- Combine using transitivity (A2).
    exact thermo_le_trans h_ih h_last

-- Coherence Helpers required for S0/Sn normalization.
/-- Helper: 1•X ≈ X (C1 Coherence via gscale_state) -/
lemma gscale_one_equiv {Γ} (X : TW.State Γ) :
  gscale_state (show 0 ≤ (1:ℝ) by norm_num) X ≈ X := by
  -- Normalize gscale_state for t=1 to scale_state.
  have h1pos : 0 < (1:ℝ) := by norm_num
  rw [gscale_state_pos (by norm_num) h1pos X]
  -- Combine CCast and C1 coherence.
  have h_cast := TW.state_equiv_coherence (TW.one_smul Γ) (scale_state h1pos.ne' X)
  have h_c1 := TW.one_smul_coherence (Γ := Γ) (X := X)
  exact thermo_equiv_trans' h_cast h_c1

/-- Helper: 0•X ≈ default (state of the Zero System). -/
lemma gscale_zero_equiv {Γ} (X : TW.State Γ) :
  gscale_state (show 0 ≤ (0:ℝ) by simp) X ≈ (default : TW.State TW.ZSystem) := by
  classical
  -- Casted default equals gscale_state at 0.
  have hz :
      gscale_state (show 0 ≤ (0:ℝ) by simp) X
        = (Equiv.cast (congrArg TW.State (by simp [TW.scale_zero_is_ZSystem]))).symm
            (TW.State_ZSystem_is_Unit.default) := by
    simp [gscale_state]
  -- default ≈ casted default via CCast.
  have h0_sys : (0 : ℝ) • Γ = TW.ZSystem := by simp [TW.scale_zero_is_ZSystem]
  have h_def_to_cast :
      (default : TW.State TW.ZSystem) ≈
        (Equiv.cast (congrArg TW.State h0_sys)).symm (default) := by
    simpa using
      (TW.state_equiv_coherence h0_sys.symm (default : TW.State TW.ZSystem))
  simpa [hz, h0_sys] using (thermo_equiv_symm h_def_to_cast)

/-- Helper: (ZSystem, X) ≈ X (CZ Coherence + CC) -/
lemma comp_Z_equiv_L {Γ} (X : TW.State Γ) :
  comp_state ((default : TW.State TW.ZSystem), X) ≈ X := by
  -- Swap and then apply the identity for Z on the right.
  have h_comm := comp_comm_equiv_clean (default : TW.State TW.ZSystem) X
  have h_CZ := TW.comp_ZSystem_is_identity Γ X
  exact thermo_equiv_trans' h_comm h_CZ

/-- **Theorem 2.1 (The Cancellation Law)**: (X, Z) ≺ (Y, Z) ⇒ X ≺ Y. -/
theorem CancellationLaw {ΓX ΓY ΓZ} (X : TW.State ΓX) (Y : TW.State ΓY) (Z : TW.State ΓZ)
    (h_main : comp_state (X, Z) ≺ comp_state (Y, Z)) : X ≺ Y := by
  apply stability_from_seq (X := X) (Y := Y) (Z := Z)
  refine ⟨1, by norm_num, ?_⟩
  intro ε hε
  -- 1. Choose ε' = 1/n ≤ ε.
  obtain ⟨n, hn1, hε'pos, hε'le⟩ := exists_inv_nat_le_eps hε.1 hε.2
  let ε' : ℝ := 1 / (n : ℝ)
  have hε'_eq : ε' = 1 / (n : ℝ) := rfl
  -- 2. Define the sequence of states S(k) using a Sigma type to handle varying systems.
  -- We define S(k) only for k ≤ n. We use an `if` condition to handle k > n gracefully.
  let S_sigma : Nat → (Σ (Γ : System), TW.State Γ) := fun k =>
    if h_k_le_n : k ≤ n then
      -- Get coefficients and nonnegativity proofs.
      let c := coeffs_ok n k h_k_le_n hn1
      -- Define the state S(k) = ((1-kε')•X, (kε'•Y, ε'•Z)). (Right-associated tripleR)
      let St := tripleR
                  (gscale_state c.2.1 X)
                  (gscale_state c.2.2 Y)
                  (gscale_state (le_of_lt c.1) Z)
      ⟨_, St⟩
    else
      -- Dummy value for k > n (not used in the chain).
      ⟨TW.ZSystem, default⟩
  -- 3. Prove the step lemma: S(k) ≺ S(k+1).
  have hstep_sigma : ∀ k, k < n → TW.le (S_sigma k).2 (S_sigma (k+1)).2 := by
    intro k hk
    -- Unfold S_sigma(k) and S_sigma(k+1).
    have hk_le_n : k ≤ n := le_of_lt hk
    have hk1_le_n : k+1 ≤ n := Nat.succ_le_of_lt hk
    -- We use `dsimp` to unfold the definitions based on the `if` conditions.
    dsimp [S_sigma]
    rw [dif_pos hk_le_n, dif_pos hk1_le_n]
    -- Apply the S_step lemma. The definitions align perfectly by construction.
    exact S_step X Y Z h_main hε'pos hε'_eq hk
  -- 4. Apply the generalized chain fold.
  -- Define Start (S0) and End (Sn).
  have h0_le_n : 0 ≤ n := Nat.zero_le n
  let c0 := coeffs_ok n 0 h0_le_n hn1
  let Start : (Σ (Γ : System), TW.State Γ) := ⟨_, tripleR (gscale_state c0.2.1 X) (gscale_state c0.2.2 Y) (gscale_state (le_of_lt c0.1) Z)⟩
  let cn := coeffs_ok n n (le_refl n) hn1
  let End : (Σ (Γ : System), TW.State Γ) := ⟨_, tripleR (gscale_state cn.2.1 X) (gscale_state cn.2.2 Y) (gscale_state (le_of_lt cn.1) Z)⟩
  -- Verify S_sigma 0 = Start and S_sigma n = End.
  have h_start_def : S_sigma 0 = Start := by dsimp [S_sigma]; rw [dif_pos h0_le_n]
  have h_end_def : S_sigma n = End := by dsimp [S_sigma]; rw [dif_pos (le_refl n)]
  -- Apply the chain fold: Start ≺ End.
  have h_chain := generalized_chain_fold' Start End S_sigma n h_start_def h_end_def hstep_sigma
  -- 5. Normalize Start and End states.
  -- Start = S(0) = (1•X, (0•Y, ε'•Z)). Goal: ≈ (X, ε'•Z).
  have h_Start_equiv : Start.2 ≈ comp_state (X, scale_state hε'pos.ne' Z) := by
    -- Identify components: 1•X, 0•Y, ε'•Z.
    -- Use gscale_eq_coherence and proof irrelevance to align definitions with 1, 0.
    have h_c0_1 : (1 - (0:ℝ) * ε') = 1 := by simp
    have h_c0_0 : (0:ℝ) * ε' = 0 := by simp
    have h_align_X :
        gscale_state c0.2.1 X ≈ gscale_state (show 0 ≤ (1:ℝ) by norm_num) X := by
      refine
        gscale_eq_coherence ?_ X c0.right.left
          (have this :=
            Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl true);
          this)
      simp_all only [one_div, inv_pos, Nat.cast_pos, Lean.Elab.WF.paramLet, gscale_state_pos, ↓reduceDIte, CharP.cast_eq_zero, zero_mul, sub_zero, zero_lt_one, le_refl,
        mul_pos_iff_of_pos_left, ε', S_sigma, Start, End]
    have h_align_Y :
        gscale_state c0.2.2 Y ≈ gscale_state (show 0 ≤ (0:ℝ) by norm_num) Y := by
      refine
        gscale_eq_coherence ?_ Y c0.right.right
          (have this :=
            Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero) (Eq.refl true);
          this)
      simp
    -- Apply Coherence Axioms.
    have h_X1 : gscale_state (show 0 ≤ (1:ℝ) by norm_num) X ≈ X := gscale_one_equiv X
    have h_Y0 : gscale_state (show 0 ≤ (0:ℝ) by norm_num) Y ≈ (default : TW.State TW.ZSystem) := gscale_zero_equiv Y
    -- Normalize Z component.
    have h_Zε' : gscale_state (le_of_lt c0.1) Z ≈ scale_state hε'pos.ne' Z := by
      simpa [gscale_state_pos (le_of_lt c0.1) c0.1] using
        (thermo_equiv_refl (scale_state hε'pos.ne' Z))
    -- Combine alignments using A3.
    have h_align :
        Start.2 ≈
        comp_state (gscale_state (show 0 ≤ (1:ℝ) by norm_num) X,
                    comp_state (gscale_state (show 0 ≤ (0:ℝ) by norm_num) Y,
                                gscale_state (le_of_lt c0.1) Z)) := by
      exact
        ⟨ TW.A3 h_align_X.1 (TW.A3 h_align_Y.1 (thermo_le_refl (gscale_state (le_of_lt c0.1) Z))),
          TW.A3 h_align_X.2 (TW.A3 h_align_Y.2 (thermo_le_refl (gscale_state (le_of_lt c0.1) Z))) ⟩
    -- Reduce (1•X) and (0•Y), and remove ZSystem using CZ+CC.
    have h_reduce_inner :
        comp_state (gscale_state (show 0 ≤ (0:ℝ) by norm_num) Y,
                    gscale_state (le_of_lt c0.1) Z)
          ≈ comp_state ((default : TW.State TW.ZSystem),
                        scale_state hε'pos.ne' Z) :=
      ⟨ TW.A3 h_Y0.1 h_Zε'.1, TW.A3 h_Y0.2 h_Zε'.2 ⟩
    have h_reduce1 :
        comp_state (gscale_state (show 0 ≤ (1:ℝ) by norm_num) X,
                    comp_state (gscale_state (show 0 ≤ (0:ℝ) by norm_num) Y,
                                gscale_state (le_of_lt c0.1) Z))
          ≈ comp_state (gscale_state (show 0 ≤ (1:ℝ) by norm_num) X,
                        comp_state ((default : TW.State TW.ZSystem),
                                    scale_state hε'pos.ne' Z)) :=
      ⟨ TW.A3 (thermo_le_refl _) h_reduce_inner.1,
        TW.A3 (thermo_le_refl _) h_reduce_inner.2 ⟩
    have h_reduce2 :
        comp_state (gscale_state (show 0 ≤ (1:ℝ) by norm_num) X,
                    comp_state ((default : TW.State TW.ZSystem),
                                scale_state hε'pos.ne' Z))
          ≈ comp_state (X, scale_state hε'pos.ne' Z) := by
      -- First reduce 1•X to X using h_X1.
      have h_X1_lift :
          comp_state (gscale_state (show 0 ≤ (1:ℝ) by norm_num) X,
                      comp_state ((default : TW.State TW.ZSystem),
                                  scale_state hε'pos.ne' Z))
            ≈ comp_state (X,
                          comp_state ((default : TW.State TW.ZSystem),
                                      scale_state hε'pos.ne' Z)) :=
        ⟨ TW.A3 h_X1.1 (thermo_le_refl _),
          TW.A3 h_X1.2 (thermo_le_refl _) ⟩
      -- Then collapse (ZSystem, T) ≈ T using comp_Z_equiv_L.
      have h_cz := comp_Z_equiv_L (scale_state hε'pos.ne' Z)
      have h_cz_lift :
          comp_state (X,
                      comp_state ((default : TW.State TW.ZSystem),
                                  scale_state hε'pos.ne' Z))
            ≈ comp_state (X, scale_state hε'pos.ne' Z) :=
        ⟨ TW.A3 (thermo_le_refl _) h_cz.1,
          TW.A3 (thermo_le_refl _) h_cz.2 ⟩
      exact thermo_equiv_trans' h_X1_lift h_cz_lift
    have h_reduce := thermo_equiv_trans' h_reduce1 h_reduce2
    exact thermo_equiv_trans' h_align h_reduce
  -- End = S(n) = (0•X, (1•Y, ε'•Z)). Goal: ≈ (Y, ε'•Z).
  have h_End_equiv : End.2 ≈ comp_state (Y, scale_state hε'pos.ne' Z) := by
    -- Symmetric logic.
    have hn_ne0 : (n:ℝ) ≠ 0 := by simp; grind
    have h_cn_0 : (1 - (n:ℝ) * ε') = 0 := by
      simp [hε'_eq]; field_simp [hn_ne0]; grind
    have h_cn_1 : (n:ℝ) * ε' = 1 := by
      simp [hε'_eq]; field_simp [hn_ne0]
    -- Alignment.
    have h_align_X :
        gscale_state cn.2.1 X ≈ gscale_state (show 0 ≤ (0:ℝ) by norm_num) X :=
      gscale_eq_coherence (Γ := ΓX) (X := X)
        (h_eq := h_cn_0)
        (ht₁ := by simpa [hε'_eq] using cn.2.1)
        (ht₂ := by norm_num)
    have h_align_Y :
        gscale_state cn.2.2 Y ≈ gscale_state (show 0 ≤ (1:ℝ) by norm_num) Y :=
      gscale_eq_coherence (Γ := ΓY) (X := Y)
        (h_eq := h_cn_1)
        (ht₁ := by simpa [hε'_eq] using cn.2.2)
        (ht₂ := by norm_num)
    -- Reductions.
    have h_X0 : gscale_state (show 0 ≤ (0:ℝ) by norm_num) X ≈ (default : TW.State TW.ZSystem) := gscale_zero_equiv X
    have h_Y1 : gscale_state (show 0 ≤ (1:ℝ) by norm_num) Y ≈ Y := gscale_one_equiv Y
    have h_Zε' : gscale_state (le_of_lt cn.1) Z ≈ scale_state hε'pos.ne' Z := by
      simpa [gscale_state_pos (le_of_lt cn.1) cn.1] using
        (thermo_equiv_refl (scale_state hε'pos.ne' Z))
    -- Combine alignment using A3.
    have h_align :
        End.2 ≈
        comp_state (gscale_state (show 0 ≤ (0:ℝ) by norm_num) X,
                    comp_state (gscale_state (show 0 ≤ (1:ℝ) by norm_num) Y,
                                gscale_state (le_of_lt cn.1) Z)) := by
      exact
        ⟨ TW.A3 h_align_X.1 (TW.A3 h_align_Y.1 (thermo_le_refl (gscale_state (le_of_lt cn.1) Z))),
          TW.A3 h_align_X.2 (TW.A3 h_align_Y.2 (thermo_le_refl (gscale_state (le_of_lt cn.1) Z))) ⟩
    -- Reduce to (Y, ε'•Z) via h_X0, h_Y1 and CZ.
    have h_reduce_inner :
        comp_state (gscale_state (show 0 ≤ (1:ℝ) by norm_num) Y,
                    gscale_state (le_of_lt cn.1) Z)
          ≈ comp_state (Y, scale_state hε'pos.ne' Z) :=
      ⟨ TW.A3 h_Y1.1 h_Zε'.1, TW.A3 h_Y1.2 h_Zε'.2 ⟩
    have h_reduce1 :
        comp_state (gscale_state (show 0 ≤ (0:ℝ) by norm_num) X,
                    comp_state (gscale_state (show 0 ≤ (1:ℝ) by norm_num) Y,
                                gscale_state (le_of_lt cn.1) Z))
          ≈ comp_state ((default : TW.State TW.ZSystem),
                        comp_state (Y, scale_state hε'pos.ne' Z)) :=
      ⟨ TW.A3 h_X0.1 h_reduce_inner.1, TW.A3 h_X0.2 h_reduce_inner.2 ⟩
    have h_cz := comp_Z_equiv_L (comp_state (Y, scale_state hε'pos.ne' Z))
    have h_reduce2 :
        comp_state ((default : TW.State TW.ZSystem),
                    comp_state (Y, scale_state hε'pos.ne' Z))
          ≈ comp_state (Y, scale_state hε'pos.ne' Z) := h_cz
    exact thermo_equiv_trans' h_align (thermo_equiv_trans' h_reduce1 h_reduce2)
  -- 6. Combine chain result with equivalences.
  -- (X, ε'•Z) ≺ Start ≺ End ≺ (Y, ε'•Z).
  have h_final_ε' :
    comp_state (X, scale_state hε'pos.ne' Z) ≺
    comp_state (Y, scale_state hε'pos.ne' Z) :=
    le_of_le_equiv (le_of_equiv_le (thermo_equiv_symm h_Start_equiv) h_chain) h_End_equiv
  -- 7. Catalyst Amplification.
  -- We have (X, ε'•Z) ≺ (Y, ε'•Z) and ε' ≤ ε. We need (X, ε•Z) ≺ (Y, ε•Z).
  have h_amplified := catalyst_amplification X Y Z hε'pos hε.1 hε'le h_final_ε'
  exact h_amplified

end LY
