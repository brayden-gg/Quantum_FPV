import data.complex.basic
import data.matrix.basic
import analysis.inner_product_space.basic
import data.complex.is_R_or_C

/-!
 Definition of quantum state and relevant 
-/

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace quantum

-- dimensions of vectors and matrices (must be positive)
variables {n m p q : ℕ} 
axiom n_pos : 0 < n
axiom m_pos : 0 < m
axiom p_pos : 0 < p
axiom q_pos : 0 < q

/- 
 Quantum State is represented as a column vector, |ψ⟩ (for kets)
 and row vector ⟨ψ| (for bras). The conjugate transpose of a bra
 vector is its corresponding ket.
-/
@[reducible]
def QState (m n : ℕ) := matrix (fin m) (fin n) ℂ

instance has_add : has_add (QState m n) := matrix.has_add
instance has_smul : has_smul ℂ (QState m n) := matrix.has_smul
 

infixl ` ⬝ `:50 := matrix.mul
postfix `†`:100 := matrix.conj_transpose
postfix `^*`:100 := star
def im := complex.I

-- some common states for spin-1/2 particles
def z_plus : QState 2 1 := ![![1], ![0]] -- particle in spin up state in the +z direction
def z_minus : QState 2 1 := ![![0], ![1]] -- particle in spin down  state in thr -z direction
noncomputable def x_plus : QState 2 1 := ![![real.sqrt (1/2)], ![real.sqrt (1/2)]]
noncomputable def x_minus : QState 2 1 := ![![real.sqrt (1/2)], ![-real.sqrt (1/2)]]
noncomputable def y_plus : QState 2 1 := ![![real.sqrt (1/2)], ![im*real.sqrt (1/2)]]
noncomputable def y_minus : QState 2 1 := ![![real.sqrt (1/2)], ![-im*real.sqrt (1/2)]]

-- conventient notation for quantum states
notation `|z₊⟩` := z_plus
notation `|z₋⟩` := z_minus
notation `|x₊⟩` := x_plus
notation `|x₋⟩` := x_minus
notation `|y₊⟩` := y_plus
notation `|y₋⟩` := y_minus

notation `z₊` := z_plus
notation `z₋` := z_minus
notation `x₊` := x_plus
notation `x₋` := x_minus
notation `y₊` := y_plus
notation `y₋` := y_minus

-- corresponding ket vectors
notation `⟨z₊|` := z_plus†
notation `⟨z₋|` := z_minus†
notation `⟨x₊|` := x_plus†
notation `⟨x₋|` := x_minus†
notation `⟨y₊|` := y_plus†
notation `⟨y₋|` := y_minus†

end quantum