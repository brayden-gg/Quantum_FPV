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

-- dimensions of vectors and matrices
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
-- instance has_smul : has_smul ℂ (QState m n) := matrix.has_smul
 

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

notation `⟨z₊|` := z_plus†
notation `⟨z₋|` := z_minus†
notation `⟨x₊|` := x_plus†
notation `⟨x₋|` := x_minus†
notation `⟨y₊|` := y_plus†
notation `⟨y₋|` := y_minus†



lemma fin_division {a b : ℕ} (a_pos : 0 < a) (b_pos : 0 < b) (i : fin (a * b)) : ↑i / b < a :=
calc (↑i) / b
  < (a * b) / b : by begin
  have hlt : ↑i < (a * b), by exact fin.is_lt i,
  apply (iff.mpr (nat.div_lt_iff_lt_mul q_pos)),
  have hdiv_self : a * b / b * b = a * b, by begin
    simp [nat.div_self q_pos, nat.mul_div_cancel],
    apply or.intro_left,
    apply nat.mul_div_cancel a q_pos,
  end,
  rw [hdiv_self],
  exact hlt,
end
... = a : by exact nat.mul_div_cancel a b_pos

lemma fin_mod {a b : ℕ} (i : fin (a * b)) (b_pos : 0 < b): ↑i % b < b := begin
  apply nat.mod_lt i,
  exact b_pos,
end


def tensor_prod (A : matrix (fin m) (fin n) ℂ) (B : matrix (fin q) (fin p) ℂ) : matrix (fin (m * q)) (fin (n * p)) ℂ :=
 λi j, (A (@fin.mk m (i / q) (fin_division m_pos q_pos i)) (@fin.mk n (j / p) (fin_division n_pos p_pos j)))
  * (B (@fin.mk q (i % q) (fin_mod i q_pos)) (@fin.mk p (j % p) (fin_mod j q_pos)))


infixl ` ⊗ `: 100 := tensor_prod

-- useful for rewriting the 
lemma tensor_prod_vec (A B : QState 2 1) : 
  A ⊗ B = !![(A 0 0) * (B 0 0); (A 0 0) * (B 1 0); (A 1 0) * (B 0 0); (A 1 0) * (B 1 0)] :=
begin
  rw [tensor_prod],
  funext i j,
  fin_cases *; simp;
  {sorry}
end

lemma tensor_prod_matrix (A B : matrix (fin 2) (fin 2) ℂ) 
 : A ⊗ B = ![![(A 0 0) * (B 0 0), (A 0 0) * (B 0 1), (A 0 1) * (B 0 0), (A 0 1) * (B 0 1)],
   ![(A 0 0) * (B 1 0), (A 0 0) * (B 1 1), (A 0 1) * (B 1 0), (A 0 1) * (B 1 1)],
   ![(A 1 0) * (B 0 0), (A 1 0) * (B 0 1), (A 1 1) * (B 0 0), (A 1 1) * (B 0 1)],
   ![(A 1 0) * (B 1 0), (A 1 0) * (B 1 1), (A 1 1) * (B 1 0), (A 1 1) * (B 1 1)]] :=
begin
  rw [tensor_prod],
  funext i j,
  fin_cases *; simp;
  fin_cases *; simp;
  {sorry}
end


def z_plus_z_plus : QState 4 1 := |z₊⟩ ⊗ |z₊⟩
def z_minus_z_plus : QState 4 1 := |z₋⟩ ⊗ |z₊⟩
def z_plus_z_minus : QState 4 1 := |z₊⟩ ⊗ |z₋⟩
def z_minus_z_minus : QState 4 1 := |z₋⟩ ⊗ |z₋⟩

notation `|z₊z₊⟩` := z_plus_z_plus
notation `|z₋z₊⟩` := z_minus_z_plus
notation `|z₊z₋⟩` := z_plus_z_minus
notation `|z₋z₋⟩` := z_minus_z_minus

lemma z_plus_z_plus_is_basis : |z₊z₊⟩ = !![1; 0; 0; 0] :=
begin
  rw [z_plus_z_plus, tensor_prod_vec, z_plus],
  simp,
end

end quantum