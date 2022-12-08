import .quantum_state
import data.complex.exponential
import data.matrix.kronecker

namespace quantum

def Id : matrix (fin 2) (fin 2) ℂ :=
  ![![1, 0],
    ![0, 1]]

def σ_x : matrix (fin 2) (fin 2) ℂ := 
 ![![0,  1],
   ![1, 0]]

def σ_y : matrix (fin 2) (fin 2) ℂ := 
 ![![0,  -im],
   ![im, 0]]

def σ_z : matrix (fin 2) (fin 2) ℂ := 
 ![![1,  0],
   ![0, -1]]

-- corresponds to measurement in z direction
lemma z_plus_eigenval_σ_z : matrix.mul σ_z |z₊⟩ = |z₊⟩ :=
begin
  rw [σ_z, quantum.z_plus, matrix.mul],
  funext i j,
  simp,
end

lemma z_minus_eigenval_σ_z : matrix.mul σ_z |z₋⟩ = -|z₋⟩ :=
begin
  rw [σ_z, quantum.z_minus, matrix.mul],
  funext i j,
  simp,
end

end quantum