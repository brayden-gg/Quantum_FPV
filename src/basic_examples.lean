import .quantum_state
import .inner_product

namespace quantum

def z_plus : QState 1 2 := ![![1, 0]] -- particle in spin up state in the +z direction
def z_minus : QState 1 2 := ![![0, 1]] -- particle in spin down  state in thr -z direction
noncomputable def x_plus : QState 1 2 := ![![real.sqrt (1/2), real.sqrt (1/2)]]
noncomputable def x_minus : QState 1 2 := ![![real.sqrt (1/2), -real.sqrt (1/2)]]
noncomputable def y_plus : QState 1 2 := ![![real.sqrt (1/2), im*real.sqrt (1/2)]]
noncomputable def y_minus : QState 1 2 := ![![real.sqrt (1/2), -im*real.sqrt (1/2)]]

-- conventient notation fo
notation `z₊` := z_plus
notation `z₋` := z_minus
notation `x₊` := x_plus
notation `x₋` := x_minus
notation `y₊` := y_plus
notation `y₋` := y_minus

-- probability of finding particle in the +z state in the
lemma z_plus_prod_z_minus : |⟨z₊|z₋⟩|² = 0 :=
begin
  rw [inner_product_apply, z_plus, z_minus],
  simp,
end

lemma z_plus_prod_z_plus : |⟨z₊|z₊⟩|² = 1 :=
begin
  rw [inner_product_apply, z_plus],
  simp,
end

lemma z_plus_prod_x_plus : |⟨z₊|x₊⟩|² = 1/2 :=
begin
  rw [inner_product_apply, z_plus, x_plus],
  simp,
end

lemma z_plus_prod_x_minus : |⟨z₊|x₋⟩|² = 1/2 :=
begin
  rw [inner_product_apply, z_plus, x_minus],
  simp,
end

lemma z_plus_prod_y_plus : |⟨z₊|y₊⟩|² = 1/2 :=
begin
  rw [inner_product_apply, z_plus, y_plus],
  simp,
end

end quantum

