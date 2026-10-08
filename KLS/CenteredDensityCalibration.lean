import KLS.UniformGeometricC2Regularity

open Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A central-density calibration changes just one diagonal entry. This
preserves a quantitative bound by the density's actual distance from one. -/
def centeredDensityMatrix (i₀ : Fin n) (d : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => if i = i₀ then d else 1)

lemma centeredDensityMatrix_det (i₀ : Fin n) (d : ℝ) :
    (centeredDensityMatrix i₀ d).det = d := by
  simp [centeredDensityMatrix, Matrix.det_diagonal]

lemma centeredDensityMatrix_posDef (i₀ : Fin n) {d : ℝ} (hd : 0 < d) :
    (centeredDensityMatrix i₀ d).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  split_ifs <;> positivity

lemma centeredDensityMatrix_increment_apply (i₀ : Fin n) (d : ℝ) (x : Space n) :
    matrixAction (centeredDensityMatrix i₀ d - 1) x =
      ((d - 1) * x i₀) • EuclideanSpace.single i₀ 1 := by
  rw [matrixAction_sub_matrices, matrixAction_one_apply]
  ext i
  simp only [matrixAction_apply, centeredDensityMatrix, Matrix.diagonal_apply, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, PiLp.sub_apply,
    PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  by_cases hi : i = i₀
  · subst i
    simp only [ite_true, mul_one]
    ring
  · simp only [hi, ite_false, one_mul, sub_self]

lemma norm_centeredDensityMatrix_increment_le (i₀ : Fin n) (d : ℝ) :
    ‖matrixAction (centeredDensityMatrix i₀ d - 1)‖ ≤ |d - 1| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
  intro x
  rw [centeredDensityMatrix_increment_apply, norm_smul, Real.norm_eq_abs, abs_mul,
    PiLp.norm_single, norm_one, mul_one]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x i₀) (abs_nonneg _)

end KLS
end
