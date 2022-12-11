import .quantum_state
import .inner_product

namespace quantum

-- for when lean gets confused about ⟨0, _⟩ = 0 etc.
lemma anon_fin2 {p} : (⟨0, p⟩: fin (2*2)) = (0 : fin 4) := rfl
lemma anon_fin1 {p} : (⟨0, p⟩: fin (1*1)) = (0 : fin 1) := rfl
lemma anon_fin1_2 {p} : (⟨1, p⟩: fin (2*2)) = (1 : fin 4) := rfl
lemma anon_fin_helf {p} : (⟨1/2, p⟩: fin 2) = (0 : fin 2) := rfl
lemma anon_fin_three_halves {p} : (⟨(↑(3 : fin 4) : ℕ)/2, p⟩: fin 2) = (1 : fin 2) := rfl
lemma anon_fin_one {p} : (⟨((↑(2 : fin (4))) : ℕ)/2, p⟩: fin 2) = (1 : fin 2) := rfl
lemma anon_fin_two_halves {p} : (⟨(↑(2 : fin 4) : ℕ)/2, p⟩: fin 2) = (1 : fin 2) := rfl
lemma anon_fin_3_mod_2 {p} : (⟨(↑(3 : fin 4) : ℕ) % 2, p⟩: fin 2) = (1 : fin 2) := rfl

-- showing that fin supports division for tensor product def'n
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

-- showing that fin supports mod for tensor product def'n
lemma fin_mod {a b : ℕ} (i : fin (a * b)) (b_pos : 0 < b): ↑i % b < b := begin
  apply nat.mod_lt i,
  exact b_pos,
end

-- for when lean gets confused that 2*2 = 4
lemma two_times_two_is_four {f : fin 4 → ℂ} :
 (λ(x : fin (2 * 2)), f x) = (λ(x : fin (4)), f x) := rfl

-- converts function to matrix
lemma fn_is_vec (x : ℂ) : 
  (λ (i : fin 1), x) = matrix.vec_cons x matrix.vec_empty :=
begin
  funext i,
  simp,
end

-- FOIL method
lemma distrib_prop (a b c d : ℂ) : 
 (a + b) * (c + d) = a*c + a*d + b*c + b*d :=
begin
  ring
end

-- sum of four elements is equal to adding the elements
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

end quantum