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

infixl ` ⬝ `:50 := matrix.mul
postfix `†`:100 := matrix.conj_transpose
postfix `^*`:100 := star
def im := complex.I

end quantum