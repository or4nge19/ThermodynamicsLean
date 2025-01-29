# Formalization of "The Physics and Mathematics of the Second Law of Thermodynamics"

This Lean 4 file formalizes the main concepts and axioms presented in the paper
"The Physics and Mathematics of the Second Law of Thermodynamics" by Lieb and Yngvason.


## Main Concepts

- **State:** A representation of the equilibrium state of a thermodynamic system.
- **State Space:** A collection of states, potentially with additional structure (e.g., convex).
- **Simple System:** A state space with a single energy coordinate (U) and multiple work coordinates (V).
- **Adiabatic Accessibility:** A binary relation (≺) between states, indicating that one state can be reached from another through an adiabatic process.
- **Thermal Equilibrium:** A state of equilibrium between two systems in thermal contact, denoted by ∼T.
- **Entropy:** A function (S) on states that characterizes adiabatic accessibility and is additive for compound systems.
- **Temperature:** A function (T) derived from the entropy, representing the system's hotness.

## Axioms

The formalization is based on the following axioms, categorized into general axioms, axioms for simple systems, axioms for thermal equilibrium, and an axiom for mixtures and reactions.

### General Axioms (A1-A7)

- **A1 (Reflexivity):** X ∼A X
- **A2 (Transitivity):** X ≺ Y ∧ Y ≺ Z → X ≺ Z
- **A3 (Consistency):** X ≺ X' ∧ Y ≺ Y' → (X, Y) ≺ (X', Y')
- **A4 (Scaling Invariance):** X ≺ Y → tX ≺ tY for t > 0
- **A5 (Splitting and Recombination):** X ∼A (tX, (1-t)X) for 0 < t < 1
- **A6 (Stability):** If (X, εZ₀) ≺ (Y, εZ₁) for a sequence of ε's tending to zero, then X ≺ Y.
- **A7 (Convex Combination):** If X and Y are in the same convex state space, then (tX, (1-t)Y) ≺ tX + (1-t)Y for 0 ≤ t ≤ 1.

### Axioms for Simple Systems (S1-S3)

- **S1 (Irreversibility):** For each X, there exists Y such that X ≺≺ Y.
- **S2 (Lipschitz Tangent Planes):** Each forward sector AX has a unique tangent plane at X with a finite slope that is locally Lipschitz continuous.
- **S3 (Connectedness of the Boundary):** The boundary of each forward sector ∂AX is connected.

### Axioms for Thermal Equilibrium (T1-T5)

- **T1 (Thermal Contact):** For any two simple systems, there exists a thermal join, and a process of thermal equilibration.
- **T2 (Thermal Splitting):** A state in the thermal join can be split into two states in the original systems.
- **T3 (Zeroth Law):** If X ∼T Y and Y ∼T Z, then X ∼T Z.
- **T4 (Transversality):** For each X, there exist X₀ ∼T X₁ with X₀ ≺≺ X ≺≺ X₁.
- **T5 (Universal Temperature Range):** The range of accessible temperatures is the same for all systems.

### Axiom for Mixtures and Reactions (M)

- **M (Absence of Sinks):** If there is a process from Γ to Γ', then there is a process from Γ' to Γ.

## Structure of the Formalization

The Lean code defines structures for `State`, `StateSpace`, `ConvexStateSpace`, and `SimpleSystem`. It then introduces the adiabatic accessibility relation (≺), strict precedence (≺≺), and adiabatic equivalence (∼A).
The forward sector and its boundary are defined, followed by axioms A1-A7.
The code then defines functions to get U, V, states and state spaces, as well as the product and scaled state spaces and states.
Next, the code defines thermal join, thermal equilibrium and its related axioms T1-T5.
Finally, it defines the entropy and temperature, and the concept of an adiabat and isotherm.
The code includes placeholders (sorries) for the proofs of the axioms and for some definitions that require further elaboration.
The goal is to eventually provide a complete and rigorous formalization of the second law of thermodynamics as presented in the paper.
