# Quantum Mechanics in Lean!

A simple library for proofs about quantum mechanics in Lean. Made as a final project for CSCI1951x: Formal Proof and Verification.

### Main tasks of this project

-   Represent particles/states conveniently as a complex vector space
-   Define an inner product on quantum states so that the lemmas related to inner products can be used for proofs.
-   Define a tensor product between quantum states (and operators on the states) to represent pairs of particles
-   Proof of the no-cloning theorem

### No-Cloning Theorem

I proved the no-cloning theorem using a proof we covered in APMA1931W: Probabilities in Quantum Mechanics. The theorem states that no unitary operator (the ones used to represent the passage of time in quantum mechanics) can turn an arbitrary quantum state into a copy of the desired state. This is done using properties of unitary operators to show that the two states must be related somehow, which violates our assumption that the two states are independent.
