import KLS.IntegratedEnergyInfinite

/-! Rank-one tensor coordinates agree with ordinary vectors and matrix action. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n : ℕ}

def rankOneTensor (v : Fin n → ℝ) : (Fin 1 → Fin n) → ℝ := fun a => v (a 0)

theorem sum_rankOne {f : Fin n → ℝ} : (∑ a : Fin 1 → Fin n, f (a 0)) = ∑ i, f i := by
  exact (Equiv.funUnique (Fin 1) (Fin n)).sum_comp f

theorem rankOneTensor_dot (u v : Fin n → ℝ) :
    rankOneTensor u ⬝ᵥ rankOneTensor v = u ⬝ᵥ v := by
  exact sum_rankOne (f := fun i => u i * v i)

theorem tensorMatrix_rankOne (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    tensorMatrix A *ᵥ rankOneTensor v = rankOneTensor (A *ᵥ v) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, tensorMatrix, tensorMatrixFamily, Fin.prod_univ_one, rankOneTensor]
  exact sum_rankOne (f := fun i => A (a 0) i * v i)

theorem tensorSlot_rankOne (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    tensorSlot (0 : Fin 1) A *ᵥ rankOneTensor v = rankOneTensor (A *ᵥ v) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, tensorSlot_eq_update, tensorMatrixFamily,
    Fin.prod_univ_one, Function.update_self, rankOneTensor]
  exact sum_rankOne (f := fun i => A (a 0) i * v i)

/-- The rank-one slice of a matrix acting on a fixed direction. -/
def covarianceSliceCLM (u : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ((Fin 1 → Fin n) → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A => rankOneTensor (A *ᵥ u)
    map_add' := by intros; ext a; simp [rankOneTensor, Matrix.add_mulVec]
    map_smul' := by intros; ext a; simp [rankOneTensor, Matrix.smul_mulVec] }

end KLS.TensorEnergy
end
