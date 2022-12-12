import .quantum_state
import data.complex.exponential

namespace quantum

variables {n m p q : ℕ} 

-- measurement operators in are hermitian
def hermitian (U : matrix (fin n) (fin n) ℂ) : Prop :=
 U = U†

-- time evolution operators are usually unitary
def unitary (U : matrix (fin n) (fin n) ℂ) : Prop :=
 U† ⬝ U = 1

-- a weaker condition than unitary that may be useful
def normal (U : matrix (fin n) (fin n) ℂ) : Prop :=
 (U† ⬝ U) = (U ⬝ U†)

def Id : matrix (fin 2) (fin 2) ℂ :=
  ![![1, 0],
    ![0, 1]]

-- The pauli spin matrix in the x direction
def σ_x : matrix (fin 2) (fin 2) ℂ := 
 ![![0,  1],
   ![1, 0]]

-- The pauli spin matrix in the y direction
def σ_y : matrix (fin 2) (fin 2) ℂ := 
 ![![0,  -im],
   ![im, 0]]

-- The pauli spin matrix in the z direction
def σ_z : matrix (fin 2) (fin 2) ℂ := 
 ![![1,  0],
   ![0, -1]]

-- corresponds to measurement in z direction
lemma z_plus_eigenval_σ_z : σ_z ⬝ |z₊⟩ = |z₊⟩ :=
begin
  rw [σ_z, quantum.z_plus, matrix.mul],
  funext i j,
  simp,
end

lemma z_minus_eigenval_σ_z : σ_z ⬝ |z₋⟩ = -|z₋⟩ :=
begin
  rw [σ_z, quantum.z_minus, matrix.mul],
  funext i j,
  simp,
end

end quantum