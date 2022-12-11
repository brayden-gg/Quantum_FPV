import .quantum_state
import .inner_product

namespace quantum

variables {n m p q : ℕ} 

lemma fin_div {a b : ℕ} (a_pos : 0 < a) (b_pos : 0 < b) (i : fin (a * b)) : ↑i / b < a :=
calc (↑i) / b
  < (a * b) / b : by begin
  have hlt : ↑i < (a * b), by exact fin.is_lt i,
  apply (iff.mpr (nat.div_lt_iff_lt_mul b_pos)),
  have hdiv_self : a * b / b * b = a * b, by begin
    simp [nat.div_self b_pos, nat.mul_div_cancel],
    apply or.intro_left,
    apply nat.mul_div_cancel a b_pos,
  end,
  rw [hdiv_self],
  exact hlt,
end
... = a : by exact nat.mul_div_cancel a b_pos

lemma fin_mod {a b : ℕ} (i : fin (a * b)) (b_pos : 0 < b): ↑i % b < b := begin
  apply nat.mod_lt i,
  exact b_pos,
end

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

lemma anon_fin2 {p} : (⟨0, p⟩: fin (2*2)) = (0 : fin 4) := rfl
lemma anon_fin1 {p} : (⟨0, p⟩: fin (1*1)) = (0 : fin 1) := rfl
lemma anon_fin1_2 {p} : (⟨1, p⟩: fin (2*2)) = (1 : fin 4) := rfl
lemma anon_fin_helf {p} : (⟨1/2, p⟩: fin 2) = (0 : fin 2) := rfl
lemma anon_fin_three_halves {p} : (⟨(↑(3 : fin 4) : ℕ)/2, p⟩: fin 2) = (1 : fin 2) := rfl
lemma anon_fin_one {p} : (⟨((↑(2 : fin (4))) : ℕ)/2, p⟩: fin 2) = (1 : fin 2) := rfl
lemma anon_fin_two_halves {p} : (⟨(↑(2 : fin 4) : ℕ)/2, p⟩: fin 2) = (1 : fin 2) := rfl
lemma anon_fin_3_mod_2 {p} : (⟨(↑(3 : fin 4) : ℕ) % 2, p⟩: fin 2) = (1 : fin 2) := rfl

lemma two_times_two_is_four {f : fin 4 → ℂ} :
 (λ(x : fin (2 * 2)), f x) = (λ(x : fin (4)), f x) := rfl

lemma fn_is_vec (x : ℂ) : 
  (λ (i : fin 1), x) = matrix.vec_cons x matrix.vec_empty :=
begin
  funext i,
  simp,
end

-- useful for rewriting the 
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

lemma z_plus_z_plus_is_basis : |z₊z₊⟩ = !![1; 0; 0; 0] :=
begin
  rw [z_plus_z_plus, tensor_prod_vec, z_plus],
  simp,
end

lemma distrib_prop (a b c d : ℂ) : 
 (a + b) * (c + d) = a*c + a*d + b*c + b*d :=
begin
  ring
end

lemma extract_sum {f : fin 4 → ℂ} :
 finset.univ.sum (λ(x : fin 4), f x) = f 0 + f 1 + f 2 + f 3 := 
begin 
  simp [fin.sum_univ_succ],
  rw [show fin.succ 2 = (3 : fin 4), by refl],
  calc f 0 + (f 1 + (f 2 + f 3))
   = f 0 + ((f 1 + f 2) + f 3) : by rw [add_assoc]
   ... = (f 0 + (f 1 + f 2)) + f 3 : by rw [add_assoc (f 0) (f 1 + f 2) (f 3)]
   ... = f 0 + f 1 + f 2 + f 3 : by rw [add_assoc (f 0) (f 1) (f 2)],
end

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
     =  ((u 0 0)^* * (v 0 0)^*) * (u' 0 0 * v' 0 0) + 
        (u 0 0 * v 1 0)^* * (u' 0 0 * v' 1 0) + 
        (u 1 0 * v 0 0)^* * (u' 1 0 * v' 0 0) + 
        (u 1 0 * v 1 0)^* * (u' 1 0 * v' 1 0) : by rw [star_mul']
  ... = ((u 0 0)^* * (v 0 0)^*) * (u' 0 0 * v' 0 0) + 
        ((u 0 0)^* * (v 1 0)^*) * (u' 0 0 * v' 1 0) + 
        (u 1 0 * v 0 0)^* * (u' 1 0 * v' 0 0) + 
        (u 1 0 * v 1 0)^* * (u' 1 0 * v' 1 0) : by rw [star_mul']
  ... = ((u 0 0)^* * (v 0 0)^*) * (u' 0 0 * v' 0 0) + 
        ((u 0 0)^* * (v 1 0)^*) * (u' 0 0 * v' 1 0) + 
        ((u 1 0)^* * (v 0 0)^*) * (u' 1 0 * v' 0 0) + 
        (u 1 0 * v 1 0)^* * (u' 1 0 * v' 1 0) : by rw [star_mul']
  ... = ((u 0 0)^* * (v 0 0)^*) * (u' 0 0 * v' 0 0) + 
        ((u 0 0)^* * (v 1 0)^*) * (u' 0 0 * v' 1 0) + 
        ((u 1 0)^* * (v 0 0)^*) * (u' 1 0 * v' 0 0) + 
        ((u 1 0)^* * (v 1 0)^*) * (u' 1 0 * v' 1 0) : by rw [star_mul']
  ... = (u 0 0)^* * u' 0 0 * ((v 0 0)^* * v' 0 0) + 
        (u 0 0)^* * u' 0 0 * ((v 1 0)^* * v' 1 0) + 
        (u 1 0)^* * u' 1 0 * ((v 0 0)^* * v' 0 0) + 
        (u 1 0)^* * u' 1 0 * ((v 1 0)^* * v' 1 0) : by ring,
end



end quantum