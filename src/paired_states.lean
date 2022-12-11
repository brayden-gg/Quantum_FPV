import .quantum_state
import .inner_product
import .helper_lemmas

namespace quantum

variables {n m p q : ℕ} 

/-
  The tensor product of multiple particles contains all the information 
  about the particles. The particles are said to be be independent when 
  the state is factorable into a tensor prouct of the particles and said
  to be entangled when it is not.
-/


@[reducible]
def mk_fin_div {m p : ℕ} (i : fin (m*p)) : fin m :=
  @fin.mk m ((i : ℕ)/p) (fin_div m_pos p_pos i)

@[reducible]
def mk_fin_mod {m p : ℕ} (i : fin (m*p)) : fin p :=
  @fin.mk p ((i : ℕ)%p) (fin_mod i p_pos)

def tensor_prod (A : matrix (fin m) (fin n) ℂ) (B : matrix (fin p) (fin q) ℂ) : matrix (fin (m * p)) (fin (n * q)) ℂ :=
 λi j, (A (@mk_fin_div m p i) (@mk_fin_div n q j))
  * (B (@mk_fin_mod m p i) (@mk_fin_mod n q j))


infixl ` ⊗ `: 150 := tensor_prod

-- special case of tensor product for 2D vectors (spin 1/2 particles)
lemma tensor_prod_vec (A B : QState 2 1) : 
  A ⊗ B = !![(A 0 0) * (B 0 0); (A 0 0) * (B 1 0); (A 1 0) * (B 0 0); (A 1 0) * (B 1 0)] :=
begin
  rw [tensor_prod],
  funext i j,
  fin_cases *; simp [anon_fin2]; fin_cases *; simp [anon_fin1, mk_fin_div, mk_fin_mod],
  {apply or.intro_left,
   rw [anon_fin_helf]},
  {rw [fn_is_vec, matrix.cons_append, matrix.empty_append],
   simp [anon_fin1_2]},
  {simp [matrix.vec_head, matrix.cons_append],
   rw [anon_fin_three_halves, anon_fin_3_mod_2]}
end

def z_plus_z_plus : QState 4 1 := |z₊⟩ ⊗ |z₊⟩
def z_minus_z_plus : QState 4 1 := |z₋⟩ ⊗ |z₊⟩
def z_plus_z_minus : QState 4 1 := |z₊⟩ ⊗ |z₋⟩
def z_minus_z_minus : QState 4 1 := |z₋⟩ ⊗ |z₋⟩

notation `|z₊z₊⟩` := z_plus_z_plus
notation `|z₋z₊⟩` := z_minus_z_plus
notation `|z₊z₋⟩` := z_plus_z_minus
notation `|z₋z₋⟩` := z_minus_z_minus

lemma inner_prod_indep_states_eq_prod (u v u' v' : QState 2 1) :
 ⟪(u ⊗ v)|(u' ⊗ v')⟫ = ⟪u|u'⟫ * ⟪v|v'⟫ :=
begin
  simp [inner_product_apply, tensor_prod_vec],
  rw [distrib_prop],
  rw [two_times_two_is_four],
  rw [extract_sum],
  rw [show (2 : fin 4) = @fin.succ 4 1, by refl],
  rw [show (↑(fin.succ (1 : fin 4)) : fin 4) = ((fin.succ (1 : fin 4)) : fin 4), by refl],
  rw [matrix.cons_val_zero, matrix.cons_val_zero, matrix.cons_val_one, matrix.cons_val_one],
  rw [matrix.cons_val_succ, matrix.vec_head, matrix.vec_head, matrix.cons_val_zero, matrix.cons_val_zero],
  rw [show (↑(1 : fin 4) : fin 3) = (1 : fin 3), by refl],
  rw [matrix.cons_val_one, matrix.cons_val_succ, matrix.cons_val_one],
  rw [show (3 : fin 4) = @fin.succ 4 (@fin.succ 4 1), by refl],
  rw [show (↑(fin.succ (↑(fin.succ (1 : fin 4)) : fin 4)) : fin 4) = ((fin.succ (fin.succ (1 : fin 4))) : fin 4), by refl],
  rw [matrix.vec_head, matrix.vec_head, matrix.cons_val_succ, matrix.cons_val_succ, matrix.cons_val_succ, matrix.cons_val_succ, matrix.cons_val_zero, matrix.cons_val_zero],
  rw [show (↑(1 : fin 4) : fin 2) = (1 : fin 2), by refl],
  rw [matrix.cons_val_one, matrix.cons_val_one, matrix.vec_head, matrix.vec_head],
  calc  (u 0 0 * v 0 0)^* * (u' 0 0 * v' 0 0) + 
        (u 0 0 * v 1 0)^* * (u' 0 0 * v' 1 0) + 
        (u 1 0 * v 0 0)^* * (u' 1 0 * v' 0 0) + 
        (u 1 0 * v 1 0)^* * (u' 1 0 * v' 1 0) 
   = ((u 0 0)^* * (v 0 0)^*) * (u' 0 0 * v' 0 0) + 
        ((u 0 0)^* * (v 1 0)^*) * (u' 0 0 * v' 1 0) + 
        ((u 1 0)^* * (v 0 0)^*) * (u' 1 0 * v' 0 0) + 
        ((u 1 0)^* * (v 1 0)^*) * (u' 1 0 * v' 1 0) : by rw [star_mul', star_mul', star_mul', star_mul']
  ... = (u 0 0)^* * u' 0 0 * ((v 0 0)^* * v' 0 0) + 
        (u 0 0)^* * u' 0 0 * ((v 1 0)^* * v' 1 0) + 
        (u 1 0)^* * u' 1 0 * ((v 0 0)^* * v' 0 0) + 
        (u 1 0)^* * u' 1 0 * ((v 1 0)^* * v' 1 0) : by ring,
end



end quantum