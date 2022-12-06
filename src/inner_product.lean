import .quantum_state

namespace quantum

def inner_product {n : ℕ} : QState n 1 → QState 1 n → ℂ :=
 λφ ψ, matrix.trace (φ ⬝ ψ) 

notation `⟨` u `|` v `⟩` := inner_product (u†) v
notation `|` z `|²`:= complex.norm_sq z

--helpers for inner_product
lemma ip_to_trace {n : ℕ} (ψ φ : QState 1 n) : 
 ⟨φ|ψ⟩ = finset.univ.sum (λ (i : fin n), (matrix.diag (φ† ⬝ ψ) i)) :=
calc ⟨φ|ψ⟩
  = matrix.trace (φ† ⬝ ψ) : by rw [inner_product]
... = finset.univ.sum (λ (i : fin n), (matrix.diag (φ† ⬝ ψ) i)) : by rw [matrix.trace]

lemma mul_ct_def {n : ℕ} (ψ φ : QState 1 n) : 
 φ† ⬝ ψ = λ (i : fin n) (k : fin n), (matrix.dot_product (λ (j : fin 1), φ† i j) (λ (j : fin 1), ψ j k)) := 
by rw [matrix.mul]

lemma dot_prod_def {n : ℕ} (ψ φ : QState 1 n) : 
 (λ(i : fin n) (k : fin n), (matrix.dot_product (λ (j : fin 1), φ† i j) (λ (j : fin 1), ψ j k))) = (λ(i : fin n) (k : fin n), finset.univ.sum (λ (j : fin 1), (φ† i j) * (ψ j k))) :=
begin
  funext i j,
  rw [matrix.dot_product],
  -- exact (dot_prod_def ψ φ i j),
end

lemma conj_transpose_def {n : ℕ} (ψ : QState 1 n) (i : fin 1) (j : fin n) :
 (ψ†) j i = (ψ i j)^* := 
by rw [matrix.conj_transpose_apply]

lemma conj_tranpose_in_sum {n : ℕ} (ψ : QState 1 n) : 
 ∀(i k : fin n), (λ (j : fin 1), (ψ† i j) * ψ j k) = (λ (j : fin 1), (ψ j i)^* * ψ j k) :=
begin
  intros i k,
  funext j,
  rw [conj_transpose_def],
end

lemma inner_product_apply {n : ℕ} (φ ψ: QState 1 n) :
 ⟨φ|ψ⟩ = (finset.sum finset.univ (λ (i : fin n), matrix.diag (λ (i k : fin n), finset.sum finset.univ (λ (j : fin 1), ((φ†) i j) * ((ψ) j k))) i)) :=
begin
  rw [ip_to_trace, mul_ct_def, dot_prod_def]
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
  sorry,
  -- apply (finset.sum_eq_zero_iff_of_nonneg _).mp hzero,
  -- {simp},
  -- {intros j j_in_set,
  -- apply complex.norm_sq_nonneg,}
end


instance inner_product_space {n : ℕ} : inner_product_space.core ℂ (QState 1 n) :=
 {inner := λφ ψ, ⟨φ|ψ⟩,
  conj_sym := begin
    intros φ ψ,
    rw [star_ring_end_apply],
    calc ⟨ψ|φ⟩^*
     = (matrix.trace (ψ† ⬝ φ))^* : by rw [inner_product]
     ... = (matrix.trace ((ψ† ⬝ φ)††))^* : by rw [matrix.conj_transpose_conj_transpose]
     ... = (matrix.trace ((φ† ⬝ ψ††)†))^* : by rw [matrix.conj_transpose_mul]
     ... = (matrix.trace ((φ† ⬝ ψ)†))^* : by rw [matrix.conj_transpose_conj_transpose]
     ... = (matrix.trace (φ† ⬝ ψ))^*^* : by rw [matrix.trace_conj_transpose]
     ... = matrix.trace (φ† ⬝ ψ) : by rw [star_star]
     ... = ⟨φ|ψ⟩ : by rw [inner_product],
  end,
  add_left := begin
    intros ψ₁ ψ₂ φ,
    calc ⟨(ψ₁ + ψ₂)|φ⟩
      = matrix.trace ((ψ₁ + ψ₂)† ⬝ φ) : by rw [inner_product]
      ... = matrix.trace ((ψ₁† + ψ₂†) ⬝ φ) : by rw [matrix.conj_transpose_add]
      ... = matrix.trace ((ψ₁† ⬝ φ) + (ψ₂† ⬝ φ)) : by rw [matrix.add_mul]
      ... = matrix.trace (ψ₁† ⬝ φ) + matrix.trace (ψ₂† ⬝ φ) : by rw [matrix.trace_add]
      ... = ⟨ψ₁|φ⟩ + ⟨ψ₂|φ⟩ : by rw [inner_product],
  end,
  smul_left := begin
    intros φ ψ c,
    rw [star_ring_end_apply],
    calc ⟨c • φ|ψ⟩
      = matrix.trace ((c • φ)† ⬝ ψ) : by rw [inner_product]
      ... = (c^*) * (matrix.trace (φ† ⬝ ψ)) : by begin rw [matrix.conj_transpose_smul], simp end
      ... = (c^*) * ⟨φ|ψ⟩ : by rw [inner_product],
      end,
  nonneg_re := begin
    intro ψ,
    rw [le_iff_ge],
    calc (is_R_or_C.re ⟨ψ|ψ⟩)
     = is_R_or_C.re (finset.sum finset.univ (λ (i : fin n), matrix.diag (λ (i k : fin n), finset.sum finset.univ (λ (j : fin 1), ((ψ†) i j) * ψ j k)) i)) :
     by rw [ip_to_trace, mul_ct_def, dot_prod_def]
     ... = finset.sum finset.univ (λ (x : fin n), (ψ 0 x).re * (ψ 0 x).re + (ψ 0 x).im * (ψ 0 x).im) : by simp
     ... = finset.sum finset.univ (λ (x : fin n), complex.norm_sq (ψ 0 x)) : by simp [complex.norm_sq_apply]
     ... ≥ 0 : by begin
      have h_psi_nonneg : ∀ (i : fin n), i ∈ finset.univ → 0 ≤ complex.norm_sq (ψ 0 i), {
        intros i hi,
        exact complex.norm_sq_nonneg (ψ 0 i)
      },
      exact finset.sum_nonneg h_psi_nonneg,
     end
  end,
  definite := begin
    intros ψ hzero,

    have hsum : ⟨ψ|ψ⟩ = finset.sum finset.univ (λ (x : fin n), complex.norm_sq (ψ 0 x)), {
      rw [inner_product_apply],
      simp,
      apply eq.symm,
      simp [complex.norm_sq_eq_conj_mul_self],
    },
    
    rw [hsum] at hzero,

    have h_component_zero: ∀(i : fin n), complex.norm_sq (ψ 0 i) = 0, {
        apply zero_of_sum_eq_zero (λ(x : fin n), (ψ 0 x)),
        exact hzero,
    },

    have all_components_zero: ∀ (i : fin 1) (j : fin n), ψ i j = 0, {
        intros i j,
        apply complex.norm_sq_eq_zero.mp,
        have hi : i = 0, by simp,
        rw [hi],
        exact h_component_zero j,
    },
    funext i j,
    exact all_components_zero i j,
  end}

  end quantum