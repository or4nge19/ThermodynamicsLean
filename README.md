
# Formalization of the Lieb-Yngvason Axiomatic Framework for the Second Law of Thermodynamics

This project contains a (partial/ongoing) formalization in the Lean 4 proof assistant of the axiomatic framework for the second law of thermodynamics, as developed by Elliott H. Lieb and Jakob Yngvason. The work establishes the existence and properties of an entropy function from a set of physically motivated axioms governing the relation of adiabatic accessibility between states.

The goal of this project is to provide a machine-verified account of the mathematical arguments presented in the source papers, ensuring that every logical step is sound.

## Source Material

The formalization is based on the theory presented in the following two papers. It primarily follows the detailed mathematical structure and proofs of the *Physics Reports* article.

1.  Lieb, E. H., & Yngvason, J. (1999). **The Physics and Mathematics of the Second Law of Thermodynamics**. *Physics Reports*, 310(1), 1-96.
2.  Lieb, E. H., & Yngvason, J. (1998). **A Guide to Entropy and the Second Law of Thermodynamics**. *Notices of the American Mathematical Society*, 45(5), 571-581.

## Formalization Structure

The project is organized into a series of modules that attempt to mirror the logical development of the theory in the original paper.

*   `LY/Axioms.lean`: Defines the core `ThermoWorld` class, the basic concepts of systems and states, the axioms of adiabatic accessibility (A1-A6), and the coherence axioms.
*   `LY/Stability.lean`: Focuses on the Stability Axiom (A6) and derives the δ-ε formulation from the sequential one.
*   `LY/Algebra.lean`: Provides lemmas for algebraic manipulation of compound states, deriving cast-free versions of the coherence axioms.
*   `LY/Recombination.lean`: Contains the proof of the Recombination Lemma and its generalization to non-negative scalars.
*   `LY/Cancellation.lean`: Contains the complete, formal proof of the Cancellation Law.
*   `LY/Consequences.lean`: Formalizes the immediate consequences of the axioms and the Cancellation Law, such as the properties of strict accessibility.
*   `LY/Entropy/Principle.lean`: Defines the abstract `EntropyFunction` structure.
*   `LY/Entropy/Construction.lean`: Contains the main constructive proof of the existence and properties of a canonical entropy function.
  

#### **1. Axiomatic Framework** (`LY/Axioms.lean`)

This module corresponds to **Section II.A (Basic concepts)** and **Section II.C (Assumptions about the order relation)**.

*   The `ThermoWorld` class formalizes the concepts of "Systems and their state spaces," "Composition," and "Scaling."
*   Axioms **A1-A6** are direct translations of the six axioms listed in Section II.C.
*   The module also introduces a set of *coherence axioms* (e.g., `comp_assoc_coherence`). These are a necessary step in formalization to make rigorous the paper's informal "identification" of systems that are definitionally equal (e.g., `(A⊗B)⊗C` and `A⊗(B⊗C)`). They connect system-level equalities to state-level adiabatic equivalence (`≈`).

#### **2. The Cancellation Law** (`LY/Cancellation.lean`)

This file contains the formal proof of the **Cancellation Law (Theorem 2.1)**, which is stated in Section II.C. The paper provides a brief sketch of the proof. This module provides a complete verification, including:

*   The `S_step` lemma, which proves the core inductive step of the argument.
*   The `catalyst_amplification` lemma, which corresponds to **Lemma 2.2**.
*   The final application of Axiom A6 (Stability) to complete the proof.

#### **3. Immediate Consequences** (`LY/Consequences.lean`)

This module formalizes the results presented in **Section II.C** that follow from the axioms and the Cancellation Law.

*   **Lemmas 2.3, 2.4, and 2.5**: These lemmas, concerning the properties of the zero system, composition, and scaling, are directly formalized.
*   **Lemma 2.6**: The properties of strict accessibility (`≺≺`) are proven, relying on the Cancellation Law as described in the paper.

#### **4. Entropy Construction** (`LY/Entropy/Construction.lean`)

This module is the largest and corresponds to the constructive proof of entropy presented in **Section II.D (The construction of entropy for a single system)** and **Section II.E (Construction of a universal entropy...)**.

*   **`CanonicalEntropyContext`**, **`ReferenceState`**, and **`GenRefAccessible`**: These definitions directly match the setup at the beginning of Section II.E. The `GenRefAccessible` function formalizes the three cases for the parameter `λ` described in the paper.
*   **`CanonicalEntropyContext.S`**: The entropy function is defined as `sSup (LambdaSet X)`, which is **Equation (2.14)** in the paper.
*   **Well-definedness of Entropy**: The proofs that `LambdaSet X` is bounded above and non-empty correspond to the arguments for **Lemma 2.7**.
*   **Monotonicity of Reference States**: The `StrictReferenceState_monotone` lemma proves that `λ < μ` implies `R_λ ≺≺ R_μ`, a key component of the construction.
*   **Continuity and Normalization**: The module proves the **Continuity Lemma (Lemma 2.8)**, which shows that the supremum of the lambda set is attained (`S(X) ∈ LambdaSet X`). It then proves the normalization properties `S(X₀) = 0` and `S(X₁) = 1`, which are part of **Theorem 2.2**.

## License

The code in this repository is released under the Apache 2.0 license.
