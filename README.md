# Quantum Mechanics in Lean!

A simple library for proofs about quantum mechanics in Lean. Made as a final project for CSCI1951x: Formal Proof and Verification.

### Main tasks of this project

-   Represent particles/states conveniently as a complex vector space
-   Define an inner product on quantum states so that the lemmas related to inner products can be used for proofs.
-   Define a tensor product between quantum states (and operators on the states) to represent pairs of particles
-   Proof of the no-cloning theorem

### No-Cloning Theorem

I proved the no-cloning theorem using a proof based on what we covered in APMA1931W: Probabilities in Quantum Mechanics. The theorem states that no unitary operator (the ones used to represent the passage of time in quantum mechanics) can turn an arbitrary quantum state into a copy of the desired state. This is done using properties of unitary operators to show that the two states must be related somehow, which violates our assumption that the two states are independent.

### Important Files:

[`/src/quantum_state.lean`](https://github.com/brayden-gg/Quantum_FPV/blob/master/src/quantum_state.lean) - Defines a quantum state object and basic notation

[`/src/inner_product.lean`](https://github.com/brayden-gg/Quantum_FPV/blob/master/src/inner_product.lean) - Defines and proves that inner products of quantum states satisfy the axioms of an inner product space

[`/src/operators.lean`](https://github.com/brayden-gg/Quantum_FPV/blob/master/src/operators.lean) - Basic examples of operators on a quantum state

[`/src/paired_states.lean`](https://github.com/brayden-gg/Quantum_FPV/blob/master/src/paired_states.lean) - Defines a tensor product of quantum states, allowing us to represent a state of multiple particles

[`/src/no_cloning_thm.lean`](https://github.com/brayden-gg/Quantum_FPV/blob/master/src/no_cloning_thm.lean) - Proof of the no-cloning theorem
