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


def tensor_prod (A : matrix (fin m) (fin n) ℂ) (B : matrix (fin p) (fin q) ℂ) : matrix (fin (m * p)) (fin (n * q)) ℂ :=
 λi j, (A (fin.mk (i / p) (fin_div m_pos p_pos i)) (fin.mk (j / q) (fin_div n_pos q_pos j)))
  * (B (fin.mk (i % p) (fin_mod i q_pos)) (fin.mk (j % q) (fin_mod j q_pos)))


infixl ` ⊗ `: 150 := tensor_prod

-- useful for rewriting the 
lemma tensor_prod_vec (A B : QState 2 1) : 
  A ⊗ B = !![(A 0 0) * (B 0 0); (A 0 0) * (B 1 0); (A 1 0) * (B 0 0); (A 1 0) * (B 1 0)] :=
begin
  rw [tensor_prod],
  funext i j,
  fin_cases *; simp;
  {have vec_to_fn : matrix.vec_cons (A 0 0 * B 0 0) (matrix.vec_cons 
                      (A 0 0 * B 1 0) (matrix.vec_cons 
                        (A 1 0 * B 0 0) (λ (i : fin 1), A 1 0 * B 1 0)))
    = λi, if i = 0 then (A 0 0 * B 0 0) else 
                      (if i = 1 then (A 0 0 * B 1 0) else 
                        (if i = 2 then ( A 1 0 * B 0 0) else 
                          (A 1 0 * B 1 0))), {
     funext k,
     fin_cases k with [0, 1, 2, 3]; simp,
     {rw [if_neg (show (2 : fin 4) ≠ 0, from dec_trivial), 
          if_neg (show (2 : fin 4) ≠ 1, from dec_trivial)]},
     {simp [matrix.vec_head,
            if_neg (show (3 : fin 4) ≠ 0, from dec_trivial), 
            if_neg (show (3 : fin 4) ≠ 1, from dec_trivial),
            if_neg (show (3 : fin 4) ≠ 2, from dec_trivial)]}
    },
    rw [vec_to_fn],
    sorry,
    -- have fin4_has_zero : 0 < 2 * 2, by dec_trivial,
    -- have if_is_true : ite ((⟨0, fin4_has_zero⟩ : fin 4) = (0 : fin 4)) (A 0 0 * B 0 0) (7) = (A 0 0 * B 0 0), by {
    --   rw [if_pos (show (⟨0, fin4_has_zero⟩ : fin 4) = (0 : fin 4), from dec_trivial)],
    -- },
    -- rw [fin.constructor],
    -- rw [if_is_true],
    -- let my_zero : fin (2 * 2) := ⟨0, eq.rec (list.forall_mem_cons.mp (list.fin_range._proof_1 (2 * 2))).left (eq.trans (eq.trans (congr (congr_arg nat.add (eq.trans (eq.trans (congr (congr_arg nat.mul (eq.refl 2)) nat.nat_zero_eq_zero) nat.mul_def) (mul_zero 2))) nat.nat_zero_eq_zero) nat.add_def) (add_zero 0))⟩,
    -- have hz : my_zero = (0 : fin 4), from dec_trivial,
    
    -- rw [if_pos hz],
    -- rw [if_pos (show (⟨0, 
    -- eq.rec (list.forall_mem_cons.mp (list.fin_range._proof_1 (2 * 2))).left (eq.trans (eq.trans (congr (congr_arg nat.add (eq.trans (eq.trans (congr (congr_arg nat.mul (eq.refl 2)) nat.nat_zero_eq_zero) nat.mul_def) (mul_zero 2))) nat.nat_zero_eq_zero) nat.add_def) (add_zero 0))⟩ : fin 4) = (0 : fin 4), from dec_trivial)],

  }
end

lemma tensor_prod_matrix (A B : matrix (fin 2) (fin 2) ℂ) 
 : A ⊗ B = ![![(A 0 0) * (B 0 0), (A 0 0) * (B 0 1), (A 0 1) * (B 0 0), (A 0 1) * (B 0 1)],
   ![(A 0 0) * (B 1 0), (A 0 0) * (B 1 1), (A 0 1) * (B 1 0), (A 0 1) * (B 1 1)],
   ![(A 1 0) * (B 0 0), (A 1 0) * (B 0 1), (A 1 1) * (B 0 0), (A 1 1) * (B 0 1)],
   ![(A 1 0) * (B 1 0), (A 1 0) * (B 1 1), (A 1 1) * (B 1 0), (A 1 1) * (B 1 1)]] :=
begin
  simp [tensor_prod],
  funext i j,
  fin_cases *; simp;
  fin_cases *; simp;
  {sorry} -- use proof from before 
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

lemma inner_prod_indep_states_eq_prod (u v u' v' : QState 2 1) :
 ⟪(u ⊗ v)|(u' ⊗ v')⟫ = ⟪u|u'⟫ * ⟪v|v'⟫ :=
begin
  simp [inner_product_apply, tensor_prod_vec],
  rw [distrib_prop],
  sorry -- sum clearly equals other sum
end

end quantum