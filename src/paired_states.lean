import .quantum_state
import .helper_lemmas

namespace quantum

variables {n m p q : ℕ} 

/-
  The tensor product of multiple particles' states contains all the information 
  about the particles. The particles are said to be be independent when 
  the state is factorable into a tensor prouct of the two states and said
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
  fin_cases *; simp [anon_0_fin4]; fin_cases *; simp [anon_0_fin1, mk_fin_div, mk_fin_mod],
  {apply or.intro_left,
   rw [anon_half_fin2]},
  {rw [fn_is_vec, matrix.cons_append, matrix.empty_append],
   simp [anon_1_fin4]},
  {simp [matrix.vec_head, matrix.cons_append],
   rw [anon_three_halves_fin2, anon_3_mod_2_fin2]}
end

def z_plus_z_plus : QState 4 1 := |z₊⟩ ⊗ |z₊⟩
def z_minus_z_plus : QState 4 1 := |z₋⟩ ⊗ |z₊⟩
def z_plus_z_minus : QState 4 1 := |z₊⟩ ⊗ |z₋⟩
def z_minus_z_minus : QState 4 1 := |z₋⟩ ⊗ |z₋⟩

notation `|z₊z₊⟩` := z_plus_z_plus
notation `|z₋z₊⟩` := z_minus_z_plus
notation `|z₊z₋⟩` := z_plus_z_minus
notation `|z₋z₋⟩` := z_minus_z_minus

end quantum