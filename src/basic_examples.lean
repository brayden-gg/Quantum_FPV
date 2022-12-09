import .quantum_state
import .inner_product

namespace quantum

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

-- lemma x_plus_prod_x_plus : |⟪x₊|y₊⟫|² = 1/2 :=
-- begin
--   rw [inner_product_apply, x_plus, y_plus],
--   have unsquare : ((↑(real.sqrt 2))⁻¹ * (↑(real.sqrt 2))⁻¹) = (1/2 : ℂ), {
--     sorry
--   },

--   have unsquare2 : ((↑(real.sqrt 2))⁻¹ * (im * (↑(real.sqrt 2))⁻¹)) = (im * 1/2 : ℂ), {
--     sorry
--   },
--   -- have hdef : (im / 2) = {re:= 0, im := 1/2}, {
--   --   simp [complex.mul_im],
--   -- },
--   have i_im : (2⁻¹ * im).re = 0, {
--     simp,
--     exact complex.I_re,
--   },

--   have i_re : (complex.I * 2⁻¹).im = 2⁻¹, {
--     simp [complex.I_mul_im 2⁻¹],
--     ring_nf,
--   },
--   simp [unsquare, unsquare2, complex.norm_sq_apply, i_im, i_re],
--   ring_nf,
-- end

end quantum

