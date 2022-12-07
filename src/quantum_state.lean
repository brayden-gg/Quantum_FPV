import data.complex.basic
import data.matrix.basic
import analysis.inner_product_space.basic
import data.complex.is_R_or_C

/-!
 Definition of quantum state
-/

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace quantum

@[reducible]
def QState (m n : ℕ) := matrix (fin m) (fin n) ℂ

instance has_add {m n : ℕ} : has_add (QState m n) := matrix.has_add
instance has_smul {m n : ℕ} : has_smul ℂ (QState m n) := matrix.has_smul
-- instance has_mul {i j k : ℕ} : has_mul (matrix (fin i) (fin j)) (QState k i) := matrix.has_mul
-- instance QState_to_matrix {m n : ℕ} : has_coe (QState m n) (matrix (fin n) (fin m)) :=
 

infixl ` ⬝ `:50 := matrix.mul
postfix `†`:100 := matrix.conj_transpose
postfix `^*`:100 := star
def im := complex.I

def z_plus : QState 2 1 := ![![1], ![0]] -- particle in spin up state in the +z direction
def z_minus : QState 2 1 := ![![0], ![1]] -- particle in spin down  state in thr -z direction
noncomputable def x_plus : QState 2 1 := ![![real.sqrt (1/2)], ![real.sqrt (1/2)]]
noncomputable def x_minus : QState 2 1 := ![![real.sqrt (1/2)], ![-real.sqrt (1/2)]]
noncomputable def y_plus : QState 2 1 := ![![real.sqrt (1/2)], ![im*real.sqrt (1/2)]]
noncomputable def y_minus : QState 2 1 := ![![real.sqrt (1/2)], ![-im*real.sqrt (1/2)]]

-- conventient notation fo
notation `z₊` := z_plus
notation `z₋` := z_minus
notation `x₊` := x_plus
notation `x₋` := x_minus
notation `y₊` := y_plus
notation `y₋` := y_minus

-- #eval (![![1, 0], ![0, 1]] ⬝ z_plus )

end quantum