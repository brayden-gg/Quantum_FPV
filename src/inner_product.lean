import .quantum_state
import .paired_states

namespace quantum

/-
  Defines an quantum states as an instance of an inner product space as
  well as some useful lemmas for combining inner products with operators,
  tensor products etc.
-/

variables {n m p q : ℕ} 

def inner_product {n : ℕ} : QState n 1 → QState n 1 → ℂ :=
 λφ ψ, matrix.trace ((φ†) ⬝ ψ) 

notation `⟪` u `|` v `⟫` := inner_product u v
notation `|` z `|²`:= complex.norm_sq z

--helpers for inner_product
lemma ip_to_trace {n : ℕ} (ψ φ : QState n 1) : 
 ⟪φ|ψ⟫ = finset.univ.sum (λ (x : fin 1), (matrix.diag (φ† ⬝ ψ) x)) :=
calc ⟪φ|ψ⟫
  = matrix.trace (φ† ⬝ ψ) : by rw [inner_product]
... = finset.univ.sum (λ (x : fin 1), (matrix.diag (φ† ⬝ ψ) x)) : by rw [matrix.trace]

lemma mul_ct_def {n : ℕ} (ψ φ : QState n 1) : 
 φ† ⬝ ψ = λ (i k : fin 1), (matrix.dot_product (λ (j : fin n), φ† i j) (λ (j : fin n), ψ j k)) := 
by rw [matrix.mul]

lemma dot_prod_def {n : ℕ} (ψ φ : QState n 1) : 
 (λ(i : fin 1) (k : fin 1), (matrix.dot_product (λ (j : fin n), φ† i j) (λ (j : fin n), ψ j k))) = (λ(i : fin 1) (k : fin 1), finset.univ.sum (λ (j : fin n), (φ† i j) * (ψ j k))) :=
begin
  funext i j,
  rw [matrix.dot_product],
end

lemma conj_transpose_def {n : ℕ} (ψ : QState n 1) (i : fin n) (j : fin 1) :
 (ψ†) j i = (ψ i j)^* := 
by rw [matrix.conj_transpose_apply]

lemma conj_tranpose_in_sum {n : ℕ} (ψ : QState n 1) : 
 ∀(i k : fin 1), (λ (j : fin n), (ψ† i j) * ψ j k) = (λ (j : fin n), (ψ j i)^* * ψ j k) :=
begin
  intros i k,
  funext j,
  rw [conj_transpose_def],
end

lemma inner_product_apply {n : ℕ} (φ ψ: QState n 1) :
 ⟪φ|ψ⟫ = (finset.sum finset.univ (λ (x : fin 1), matrix.diag (λ (i k : fin 1), finset.sum finset.univ (λ (j : fin n), ((φ†) i j) * ((ψ) j k))) x)) :=
begin
  rw [ip_to_trace, mul_ct_def, dot_prod_def],
end

lemma le_iff_ge {a b : ℝ} : b ≤ a ↔ a ≥ b:= iff.rfl
lemma gt_of_ge_and_ne {a b : ℝ} (hne: ¬a = b) (hge : a ≥ b) : a > b := 
begin
  exact ne.lt_of_le (ne.symm hne) hge
end

lemma zero_of_sum_eq_zero {n : ℕ} (x : fin n → ℂ) :
 finset.sum finset.univ (λ(i : fin n), complex.norm_sq (x i) : fin n → ℂ) = 0 → ∀(i : fin n), complex.norm_sq (x i) = 0 := 
begin
  intro hzero,
  intro i,
  have h_re_zero : (finset.sum finset.univ (λ(i : fin n), (complex.norm_sq (x i)))) = 0, {
    norm_cast at hzero,
    exact hzero,
  },
  apply (finset.sum_eq_zero_iff_of_nonneg _).mp h_re_zero,
  {simp},
  {intros j j_in_set,
  apply complex.norm_sq_nonneg,}
end


instance inner_product_space {n : ℕ} : inner_product_space.core ℂ (QState n 1) :=
 {inner := λφ ψ, ⟪φ|ψ⟫,
  conj_sym := begin
    intros φ ψ,
    rw [star_ring_end_apply],
    calc ⟪ψ|φ⟫^*
     = (matrix.trace (ψ† ⬝ φ))^* : by rw [inner_product]
     ... = (matrix.trace ((ψ† ⬝ φ)††))^* : by rw [matrix.conj_transpose_conj_transpose]
     ... = (matrix.trace ((φ† ⬝ ψ††)†))^* : by rw [matrix.conj_transpose_mul]
     ... = (matrix.trace ((φ† ⬝ ψ)†))^* : by rw [matrix.conj_transpose_conj_transpose]
     ... = (matrix.trace (φ† ⬝ ψ))^*^* : by rw [matrix.trace_conj_transpose]
     ... = matrix.trace (φ† ⬝ ψ) : by rw [star_star]
     ... = ⟪φ|ψ⟫ : by rw [inner_product],
  end,
  add_left := begin
    intros ψ₁ ψ₂ φ,
    calc ⟪(ψ₁ + ψ₂)|φ⟫
      = matrix.trace ((ψ₁ + ψ₂)† ⬝ φ) : by rw [inner_product]
      ... = matrix.trace ((ψ₁† + ψ₂†) ⬝ φ) : by rw [matrix.conj_transpose_add]
      ... = matrix.trace ((ψ₁† ⬝ φ) + (ψ₂† ⬝ φ)) : by rw [matrix.add_mul]
      ... = matrix.trace (ψ₁† ⬝ φ) + matrix.trace (ψ₂† ⬝ φ) : by rw [matrix.trace_add]
      ... = ⟪ψ₁|φ⟫ + ⟪ψ₂|φ⟫ : by rw [inner_product],
  end,
  smul_left := begin
    intros φ ψ c,
    rw [star_ring_end_apply],
    calc ⟪c • φ|ψ⟫
      = matrix.trace ((c • φ)† ⬝ ψ) : by rw [inner_product]
      ... = (c^*) * (matrix.trace (φ† ⬝ ψ)) : by begin rw [matrix.conj_transpose_smul], simp end
      ... = (c^*) * ⟪φ|ψ⟫ : by rw [inner_product],
      end,
  nonneg_re := begin
    intro ψ,
    rw [le_iff_ge],
    calc (is_R_or_C.re ⟪ψ|ψ⟫)
     = is_R_or_C.re (finset.sum finset.univ (λ (x : fin 1), matrix.diag (λ (i k : fin 1), finset.sum finset.univ (λ (j : fin n), ((ψ†) i j) * ψ j k)) x)) :
     by rw [ip_to_trace, mul_ct_def, dot_prod_def]
     ... = finset.sum finset.univ (λ (x : fin n), (ψ x 0).re * (ψ x 0).re + (ψ x 0).im * (ψ x 0).im) : by simp
     ... = finset.sum finset.univ (λ (x : fin n), complex.norm_sq (ψ x 0)) : by simp [complex.norm_sq_apply]
     ... ≥ 0 : by begin
      have h_psi_nonneg : ∀ (i : fin n), i ∈ finset.univ → 0 ≤ complex.norm_sq (ψ i 0), {
        intros i hi,
        exact complex.norm_sq_nonneg (ψ i 0)
      },
      exact finset.sum_nonneg h_psi_nonneg,
     end
  end,
  definite := begin
    intros ψ hzero,

    have hsum : ⟪ψ|ψ⟫ = finset.sum finset.univ (λ (x : fin n), complex.norm_sq (ψ x 0)), {
      rw [inner_product_apply],
      simp,
      apply eq.symm,
      simp [complex.norm_sq_eq_conj_mul_self],
    },
    
    rw [hsum] at hzero,

    have h_component_zero: ∀(i : fin n), complex.norm_sq (ψ i 0) = 0, {
        apply zero_of_sum_eq_zero (λ(x : fin n), (ψ x 0)),
        exact hzero,
    },

    have all_components_zero: ∀ (i : fin n) (j : fin 1), ψ i j = 0, {
        intros i j,
        apply complex.norm_sq_eq_zero.mp,
        have hj : j = 0, by simp,
        rw [hj],
        exact h_component_zero i,
    },
    funext i j,
    exact all_components_zero i j,
  end}

lemma inner_prod_matrix_ct (ψ φ : QState n 1) (M : matrix (fin n) (fin n) ℂ) :
 ⟪φ|(M† ⬝ ψ)⟫ = ⟪(M ⬝ φ)|ψ⟫ :=
calc  ⟪φ|(M† ⬝ ψ)⟫
 = matrix.trace (φ† ⬝ (M† ⬝ ψ)) : by rw [inner_product] 
 ... = matrix.trace ((φ† ⬝ M†) ⬝ ψ) : by rw [matrix.mul_assoc]
 ... = matrix.trace ((φ† ⬝ M†)†† ⬝ ψ) : by rw [matrix.conj_transpose_conj_transpose]
 ... = matrix.trace ((M†† ⬝ φ††)† ⬝ ψ) : by rw [matrix.conj_transpose_mul]
 ... = matrix.trace ((M ⬝ φ††)† ⬝ ψ) : by rw [matrix.conj_transpose_conj_transpose]
 ... = matrix.trace ((M ⬝ φ)† ⬝ ψ) : by rw [matrix.conj_transpose_conj_transpose]
 ... = ⟪(M ⬝ φ)|ψ⟫ : by rw [inner_product]

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
 -- probability of finding particle in the +z state in the -z state
-- (they are orthogonal so will be zero)
lemma z_plus_prod_z_minus : |⟪z₊|z₋⟫|² = 0 :=
begin
  rw [inner_product_apply, z_plus, z_minus],
  simp,
end

-- probability of finding particle in the +z state in the +z state
-- (they are equal and normlized so will be one)
lemma z_plus_prod_z_plus : |⟪z₊|z₊⟫|² = 1 :=
begin
  rw [inner_product_apply, z_plus],
  simp,
end

lemma z_plus_prod_z_plus' : ⟪z₊|z₊⟫ = 1 :=
begin
  rw [inner_product_apply, z_plus],
  simp,
end

-- probability of finding particle in the +z state in the +x state
lemma z_plus_prod_x_plus : |⟪z₊|x₊⟫|² = 1/2 :=
begin
  rw [inner_product_apply, z_plus, x_plus],
  simp,
end

-- probability of finding particle in the +z state in the -x state
lemma z_plus_prod_x_minus : |⟪z₊|x₋⟫|² = 1/2 :=
begin
  rw [inner_product_apply, z_plus, x_minus],
  simp,
end

-- probability of finding particle in the +z state in the +y state
lemma z_plus_prod_y_plus : |⟪z₊|y₊⟫|² = 1/2 :=
begin
  rw [inner_product_apply, z_plus, y_plus],
  simp,
end

-- simple example of a state representing a pair of particles
lemma z_plus_z_plus_is_basis : |z₊z₊⟩ = !![1; 0; 0; 0] :=
begin
  rw [z_plus_z_plus, tensor_prod_vec, z_plus],
  simp,
end

end quantum