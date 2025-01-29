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

## Main Theorems and Proofs

The main goal is to prove the entropy principle (EP), which states the existence of an additive and extensive entropy function that characterizes adiabatic accessibility. The proof relies on the axioms and involves several key steps:

1. **Derivation of the Comparison Principle (CH):**
   - CH is first derived for simple systems (Theorem 3.7) using axioms A1-A7 and S1-S3.
   - It is then extended to scaled copies of a single simple system (Theorem 4.4) using the transversality axiom T4.
   - Finally, CH is established for products of different simple systems (Theorem 4.8) by introducing the concept of entropy calibrators (Theorem 4.7) and utilizing the thermal join.

2. **Construction of Entropy:**
   - With CH established, the existence of an entropy function for each simple system is guaranteed (Theorem 2.2).
   - The entropy function is shown to be concave (Theorem 2.8) and continuously differentiable (Theorem 5.3).
   - The temperature is defined as the derivative of entropy with respect to energy (Theorem 5.1), and its continuity is proved (Theorem 5.2).

3. **Additivity and Extensivity:**
   - The entropy is shown to be additive for compound systems formed by taking products of simple systems (Theorem 4.8).
   - The extensivity of entropy is ensured by the scaling invariance axiom A4.

4. **Uniqueness of Entropy:**
   - Theorem 5.6 establishes that the entropy is uniquely determined (up to an affine transformation) by the adiabats and isotherms.
   - Theorem 6.1 shows that the entropy difference between two states connected by an adiabatic process is determined by a constant F(Γ, Γ'), independent of the specific states.

5. **Fixing Additive Constants:**
   - Theorem 6.2 addresses the problem of fixing the additive entropy constants for different systems.
   - It proves that under the assumption of axiom M (absence of sinks), the constants can be chosen such that entropy never decreases in any adiabatic process, even when mixing and chemical reactions are involved.
   - The proof relies on the Hahn-Banach theorem and the concept of connected state spaces.

## TODO's

- **Completing the Proofs:** The current formalization includes several `sorry` placeholders, indicating missing proofs. These proofs need to be formalized in Lean, which may involve developing new lemmas and tactics.
- **Addressing the Strong Form of the Entropy Principle:** Theorem 6.2 establishes a weak form of the entropy principle. Proving the strong form (i.e., X ≺≺ Y implies S(X) < S(Y) for all cases) requires further investigation and potentially stronger assumptions.
- **Formalizing Mixtures and Chemical Reactions:** Section VI provides a framework for dealing with mixtures and chemical reactions. This framework needs to be fully formalized, including the definition of appropriate state spaces and the derivation of relevant properties.



