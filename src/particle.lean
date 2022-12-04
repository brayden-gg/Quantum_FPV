import data.complex.basic
import data.matrix.basic
import analysis.inner_product_space.basic
import data.complex.is_R_or_C

/-!
 TODO: explain what the project is!
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


def inner_product {n : ℕ} : QState n 1 → QState 1 n → ℂ :=
 λφ ψ, matrix.trace (φ ⬝ ψ) 

notation `⟨` u `|` v `⟩` := inner_product (u†) v

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

-- lemma conj_tranpose_sum {n : ℕ} (ψ : QState 1 n) : 
--  (λ (i k : fin n), finset.sum finset.univ (λ (j : fin 1), (ψ† i j) * ψ j k)) = (λ (i k : fin n), finset.sum finset.univ (λ (j : fin 1), (ψ j i)^* * ψ j k)) :=
-- begin
--   funext i k,
--   -- rw [finset.val_disj_sum],
--   -- rw [conj_transpose_in_sum],
-- end

-- lemma please {n : ℕ} (ψ : QState 1 n) : 
--  (λ (i : fin n), matrix.diag (λ (i k : fin n), finset.sum finset.univ (λ (j : fin 1), (ψ† i j) * ψ j k)) i) = (λ (i : fin n), matrix.diag (λ (i k : fin n), finset.sum finset.univ (λ (j : fin 1), (ψ j i)^* * ψ j k)) i) :=
-- begin
--   funext i,
--   -- rw [conj_transpose_in_sum],
-- end


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
    calc (is_R_or_C.re ⟨ψ|ψ⟩)
     = is_R_or_C.re (finset.sum finset.univ (λ (i : fin n), matrix.diag (λ (i k : fin n), finset.sum finset.univ (λ (j : fin 1), ((ψ†) i j) * ψ j k)) i)) :
     by rw [ip_to_trace, mul_ct_def, dot_prod_def]
     ... = finset.sum finset.univ (λ (x : fin n), (ψ 0 x).re * (ψ 0 x).re + (ψ 0 x).im * (ψ 0 x).im) : by simp
     ... = finset.sum finset.univ (λ (x : fin n), complex.norm_sq (ψ 0 x)) : by simp [complex.norm_sq_apply]
     ... ≥ finset.sum finset.univ (λ (x : fin n), 0) : by sorry
     ... = 0 : by simp
  end,
  definite := begin
    intros ψ hzero,
    have hsum : ⟨ψ|ψ⟩ = finset.sum finset.univ (λ (x : fin n), complex.norm_sq (ψ 0 x)), {
      rw [ip_to_trace, mul_ct_def, dot_prod_def],
      simp,
      apply eq.symm,
      simp [complex.norm_sq_eq_conj_mul_self],
    },
    rw [hsum] at hzero,
    sorry
  end}

def u : QState 1 2 := ![![1, 0]]
def d : QState 1 2 := ![![0, 1]]
noncomputable def r : QState 1 2 := ![![real.sqrt (1/2), real.sqrt (1/2)]]

-- notation |u⟩ := u
-- notation |d⟩ := d
-- notation |r⟩ := r

-- lemma u_perp_d : ⟨u|d⟩ = 0 :=
-- begin
--   sorry
-- end

-- lemma u_normed : is_normed u :=
-- begin
--   rw [is_normed, inner_product, bra_of_ket, u],
--   simp,
--   rw conj,
--   simp,
--   rw conj,
--   simp [complex.conj_of_real],
  
-- end

-- lemma mixed_state : ⟨r|u⟩ * ⟨u|r⟩ = 1 / 2 := 
-- begin
  
-- end

end quantum