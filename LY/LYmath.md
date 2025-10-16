

### **Blueprint for Formalization of Lieb-Yngvason Thermodynamics**

This document provides the  mathematical statements from the paper "The Physics and Mathematics of the Second Law of Thermodynamics" (arXiv:cond-mat/9708200v2).

#### **I. Core Mathematical Framework (Section II)**

**1. Primitive Objects and Relations**
*   **Type:** `StateSpace`, denoted by `Γ`. A set of states.
*   **Type:** `State`, denoted by `X, Y, Z`. An element of a `StateSpace`.
*   **Primitive Relation:** Adiabatic Accessibility, `≺`. A binary relation on the set of all `State`s.

**2. Foundational Definitions**
*   **Adiabatic Equivalence (`∼ₐ`):**
    `X ∼ₐ Y := (X ≺ Y) ∧ (Y ≺ X)`
*   **Strict Accessibility / Irreversibility (`≺≺`):**
    `X ≺≺ Y := (X ≺ Y) ∧ ¬(Y ≺ X)`
*   **Comparability:**
    `Comparable(X, Y) := (X ≺ Y) ∨ (Y ≺ X)`
*   **Compound System State Space:**
    `Γ₁ × Γ₂` (Cartesian Product)
*   **Scaled System State Space (`Γ⁽ᵗ⁾`):**
    `Γ⁽ᵗ⁾ := {tX | X ∈ Γ}` for `t > 0`

**3. General Axioms of Adiabatic Accessibility (A1-A7)**
These are assumed to hold for all states in all (simple or compound) state spaces.
*   **A1 (Reflexivity):** `∀X, X ∼ₐ X`
*   **A2 (Transitivity):** `∀X,Y,Z, (X ≺ Y ∧ Y ≺ Z) ⇒ X ≺ Z`
*   **A3 (Consistency):** `∀X,X',Y,Y', (X ≺ X' ∧ Y ≺ Y') ⇒ (X,Y) ≺ (X',Y')`
*   **A4 (Scaling Invariance):** `∀X,Y, ∀t > 0, (X ≺ Y) ⇒ (tX ≺ tY)`
*   **A5 (Splitting and Recombination):** `∀X, ∀t ∈ (0,1), X ∼ₐ (tX, (1-t)X)`
*   **A6 (Stability):** `∀X,Y,Z₀,Z₁, ( (∀ε > 0, (X, εZ₀) ≺ (Y, εZ₁)) ) ⇒ X ≺ Y`
*   **A7 (Convex Combination):** For a convex state space `Γ`, `∀X,Y ∈ Γ, ∀t ∈ [0,1], (tX, (1-t)Y) ≺ tX + (1-t)Y`

**4. The Entropy Principle and Key Formulas**
*   **The Entropy Principle (Statement to be proven):** There exists a real-valued function `S` on all states such that:
    *   **a) Monotonicity:** `(X ≺ Y) ⇔ S(X) ≤ S(Y)` for all comparable `X, Y`.
    *   **b) Additivity:** `S((X,Y)) = S(X) + S(Y)`
    *   **c) Extensivity:** `S(tX) = tS(X)` for `t > 0`.
*   **Comparison Hypothesis (CH):** A property of a state space `Γ`.
    `CH(Γ) := ∀X,Y ∈ Γ, Comparable(X,Y)`
*   **Formula (2.14) - The Canonical Entropy:** The constructive definition of entropy for a single system `Γ` (assuming CH and reference states `X₀ ≺≺ X₁`).
    `SΓ(X) := sup{λ ∈ ℝ | ((1-λ)X₀, λX₁) ≺ X}`
*   **Formula (2.18) & (2.20) - Calibrated Universal Entropy:** The definition of a consistent entropy `S` for any state `X ∈ Γ` using a fixed reference system `Γ₀` with states `Z₀ ≺≺ Z₁` and a reference point `XΓ ∈ Γ`.
    `S(X) := S_{Γ×Γ₀}((X,Z₀) | (XΓ,Z₀), (XΓ,Z₁))`
    This is equivalent to the direct formula:
    `S(X) := sup{λ ∈ ℝ | (XΓ, λZ₁) ≺ (X, λZ₀)}`

#### **II. Simple Systems (Section III)**

**1. Definition**
*   A **Simple System** has a state space `Γ` that is a non-empty, convex, and open subset of `ℝⁿ⁺¹`.
*   States are represented by coordinates `X = (U, V)`, where `U ∈ ℝ` is the **internal energy** and `V ∈ ℝⁿ` are the **work coordinates**.

**2. Axioms for Simple Systems (S1-S3)**
These are assumed to hold for simple systems, in addition to A1-A7.
*   **S1 (Irreversibility):** `∀X ∈ Γ, ∃Y ∈ Γ` such that `X ≺≺ Y`.
*   **S2 (Lipschitz Tangent Planes):** For each `X ∈ Γ`, the forward sector `AX := {Y ∈ Γ | X ≺ Y}` has a **unique** support plane at `X`, denoted `Π_X`. The slope of this plane is finite and is given by a locally Lipschitz continuous function `P(X) = (P₁(X), ..., Pₙ(X))`, called the **pressure**.
*   **S3 (Connectedness of the Boundary):** The boundary `∂AX` is arcwise connected.

**3. Key Formulas and Theorems**
*   **Formula (3.3) - Tangent Plane Equation:** The plane `Π_X` at `X = (U₀, V₀)` is given by:
    `U - U₀ + ∑ᵢ Pᵢ(X)(Vᵢ - V₀ᵢ) = 0`
*   **Theorem 3.7 (Nested Forward Sectors):** For any two states `X, Y` in a simple system `Γ`, exactly one of the following holds:
    1.  `AX = AY` (i.e., `X ∼ₐ Y`)
    2.  `AY ⊂ Interior(AX)` (i.e., `X ≺≺ Y`)
    3.  `AX ⊂ Interior(AY)` (i.e., `Y ≺≺ X`)
    *(This theorem proves that CH holds for any simple system).*
*   **Formula (3.17) - Adiabat Surface Equation:** The surface of an adiabat `∂AX` is described by a function `uX(V)` which is the unique solution to the system of PDEs:
    `∂uX/∂Vⱼ (V) = -Pⱼ(uX(V), V)`
    with the initial condition `uX(V₀) = U₀` for `X = (U₀, V₀)`.

#### **III. Thermal Equilibrium (Section IV)**

**1. Definitions**
*   **Thermal Join (`∆₁₂`):** Given simple systems `Γ₁`, `Γ₂`, their thermal join `∆₁₂` is a new simple system with state space:
    `∆₁₂ := {(U, V₁, V₂) | U = U₁ + U₂, (U₁, V₁) ∈ Γ₁, (U₂, V₂) ∈ Γ₂}`
*   **Thermal Equilibrium (`∼ₜ`):** A relation between states of (possibly different) simple systems.
    `X ∼ₜ Y := (X,Y) ∼ₐ φ(X,Y)`
    where `X=(U₁,V₁), Y=(U₂,V₂)` and `φ(X,Y) = (U₁+U₂, V₁, V₂) ∈ ∆₁₂`.

**2. Axioms for Thermal Equilibrium (T1-T5)**
*   **T1 (Thermal Contact):** `∀X∈Γ₁, Y∈Γ₂, (X,Y) ≺ φ(X,Y)`
*   **T2 (Thermal Splitting):** `∀Z∈∆₁₂, ∃X∈Γ₁, Y∈Γ₂` such that `Z ∼ₐ (X,Y)`
*   **T3 (Zeroth Law):** `(X ∼ₜ Y ∧ Y ∼ₜ Z) ⇒ X ∼ₜ Z`
*   **T4 (Transversality):** `∀X∈Γ, ∃X₀,X₁∈Γ` such that `(X₀ ∼ₜ X₁) ∧ (X₀ ≺≺ X ≺≺ X₁)`
*   **T5 (Universal Temperature Range):** `∀X∈Γ₁, ∀V₂` in the work-coordinate space of `Γ₂, ∃Y∈Γ₂` such that `ρ(Y) = V₂` and `X ∼ₜ Y`.

**3. Key Theorems**
*   **Theorem 4.4 & 4.8 (CH for Compound Systems):** The axioms of thermal equilibrium (specifically T4) are sufficient to prove that the Comparison Hypothesis (CH) holds for any compound system composed of simple systems. This is the final step needed to guarantee the existence of a global entropy function `S`.

#### **IV. Temperature (Section V)**

**1. Definition**
*   **Temperature (`T`):** For a simple system, temperature is uniquely defined from the entropy function.
    `T(X) := (∂S(X)/∂U)⁻¹`
    *(The paper first proves `T₊ = T₋` to show the derivative exists and is unique).*

**2. Key Formulas and Theorems**
*   **Formula (5.3) - Condition for Thermal Equilibrium:**
    `X₁ ∼ₜ X₂ ⇔ T(X₁) = T(X₂)`
*   **Formula - Maxwell Prerequisite:**
    `∂S/∂Vⱼ = Pⱼ/T`
*   **Theorem 5.4 (Energy Flow):** If `T(X₁) > T(X₂)` and the systems are brought into thermal contact, the final energies `U'₁`, `U'₂` satisfy:
    `U'₁ < U₁` and `U'₂ > U₂`
*   **Formula (5.5) - Carnot Efficiency (`η_C`):**
    `η_C := 1 - (T₀/T₁)`

#### **V. Mixing and Chemical Reactions (Section VI)**

**1. Definitions**
*   **Connection between State Spaces (`Γ ≺ Γ'`):** `Γ` is connected to `Γ'` if `F(Γ, Γ') < ∞`.
*   **`F(Γ, Γ')` Function:** The minimal entropy change for a catalyzed process from `Γ` to `Γ'`.
    `F(Γ, Γ') := inf_{Γ₀} { E(Γ×Γ₀, Γ'×Γ₀) }`
    where `E` is the infimum over chains of direct adiabatic processes.

**2. Axiom**
*   **M (Absence of Sinks):** `(Γ ≺ Γ') ⇒ (Γ' ≺ Γ)`

**3. Key Formulas and Theorems**
*   **Theorem 6.1 - General Process Condition:** For a process between different systems `Γ` and `Γ'`:
    `X ≺ Y ⇔ SΓ(X) + F(Γ, Γ') ≤ SΓ'(Y)`
*   **Theorem 6.2 - Weak Entropy Principle:** Assuming Axiom M, additive constants `B(Γ)` can be chosen to define a global entropy `S(X) = SΓ(X) + B(Γ)` such that for **any** adiabatic process:
    `X ≺ Y ⇒ S(X) ≤ S(Y)`
*   **Formula (6.37) - "Good Case" Additive Constant:** In the physically realistic case where chemical elements form a basis:
    `B(Γ) = F(Γ, Λ([Γ]))`
    where `Λ([Γ])` is the state space of the constituent elements of `Γ`. In this case, the full entropy principle holds: `X ≺≺ Y ⇒ S(X) < S(Y)`.
