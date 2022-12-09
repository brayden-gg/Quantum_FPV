import .quantum_state
import .inner_product
import .operators
import .paired_states
import .basic_examples

namespace quantum

variables {n m p q : ℕ} 

/-
 No unitary operator can exist that transforms any given quantum state
 into a copy of another quantum state

 - "Raw materials", |r⟩ : an arbetrary quantum state to be transformed by U.
 Since the specific value of r is nor important, we simply set it to the |z₊⟩ state
 - "Charlie", |c⟩ : a  quantum state to be cloned 
-/

theorem no_cloning : 
 ¬∃(U : matrix (fin (4)) (fin (4)) ℂ), unitary U ∧ (∀(c : matrix (fin 2) (fin 1) ℂ), U ⬝ (c ⊗ z₊) = (c ⊗ c)) :=
begin
  apply not.intro,
  intro U_exists,
  apply exists.elim U_exists,
  intros U U_conds,
  apply and.elim U_conds,
  intros U_unitary U_clones,
  rw [unitary] at U_unitary,
  -- take two nonequal, nonorthogonal quantum states
  let c1 : QState 2 1 := z_plus, 
  let c2 : QState 2 1 := x_plus,
  -- derive contradiction by showing that their inner product must be 0 or 1
  have clone_c1 : U ⬝ c1 ⊗ z₊ = c1 ⊗ c1, by apply U_clones c1,
  have clone_c2 : U ⬝ c2 ⊗ z₊ = c2 ⊗ c2, by apply U_clones c2,
  
  have ip_eq_square : ⟪c1|c2⟫ = ⟪c1|c2⟫*⟪c1|c2⟫, 
  calc ⟪c1|c2⟫ 
   = ⟪c1|c2⟫ * 1 : by ring
   ... = ⟪c1|c2⟫ * ⟪z₊|z₊⟫ : by rw [eq.symm z_plus_prod_z_plus']
   ... = ⟪(c1 ⊗ z₊)|(c2 ⊗ z₊)⟫ : by rw [inner_prod_indep_states_eq_prod]
   ... = ⟪(c1 ⊗ z₊)|(1 ⬝ (c2 ⊗ z₊))⟫ : by simp
   ... = ⟪(c1 ⊗ z₊)|((U† ⬝ U) ⬝ (c2 ⊗ z₊))⟫ : by rw [U_unitary]
   ... = ⟪(c1 ⊗ z₊)|(U† ⬝ (U ⬝ (c2 ⊗ z₊)))⟫ : by  rw [matrix.mul_assoc]
   ... = ⟪(c1 ⊗ z₊)|(U† ⬝ (c2 ⊗ c2))⟫ : by rw [clone_c2]
   ... = ⟪(U ⬝ (c1 ⊗ z₊))|(c2 ⊗ c2)⟫ : by rw [inner_prod_matrix_ct]
   ... = ⟪(c1 ⊗ c1)|(c2 ⊗ c2)⟫ : by rw [clone_c1]
   ...= ⟪c1|c2⟫*⟪c1|c2⟫ : by rw [inner_prod_indep_states_eq_prod],

  -- if the inner product equals its own square, must be 0 or 1
  have ip_eq_zero_or_one : ⟪c1|c2⟫ = 0 ∨ ⟪c1|c2⟫ = 1, by begin
    apply or_iff_not_imp_left.mpr,
    intro not_zero,
    calc ⟪c1|c2⟫ 
     = ⟪c1|c2⟫ * 1 : by ring
     ... = ⟪c1|c2⟫ * (⟪c1|c2⟫ * ⟪c1|c2⟫⁻¹) : by rw [complex.mul_inv_cancel not_zero]
     ... = (⟪c1|c2⟫ * ⟪c1|c2⟫) * ⟪c1|c2⟫⁻¹ : by rw [mul_assoc]
     ... = ⟪c1|c2⟫ * ⟪c1|c2⟫⁻¹ : by rw [eq.symm ip_eq_square]
     ... = 1 : by rw [complex.mul_inv_cancel not_zero],
  end,

  -- hoerver, already know since nonequal, nonorthogonal, inner product must not equal 0 or 1
  -- (in this case 1/2)
  have ip_c1_c2 : 1/2 = |⟪c1|c2⟫|², from eq.symm z_plus_prod_x_plus,
  apply or.elim ip_eq_zero_or_one,
  {intro ip_eq_zero,
   simp [ip_eq_zero] at ip_c1_c2,
   exact ip_c1_c2},
   {intro ip_eq_one,
   simp [ip_eq_one] at ip_c1_c2,
   exact (succ_ne_self 1) ip_c1_c2},
end

end quantum