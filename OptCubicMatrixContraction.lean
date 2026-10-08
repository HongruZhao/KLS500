import OptCompactCubicMixed
import KLS.ThirdCumulantMatrixSeed
import Mathlib.Analysis.InnerProductSpace.Dual

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem isotropic_cumulantTensor_three_integral (hμ : IsCompact μ.support)
    (hiso : IsIsotropic μ) (v : Fin 3 → Space n) :
    cumulantTensor μ 3 v = ∫ y, inner ℝ y (v 0) * inner ℝ y (v 1) * inner ℝ y (v 2) ∂μ := by
  rw [cumulantTensor_three_apply hμ]
  simp only [tiltThirdCumulant, tiltAverage, tilted_const, real_inner_comm,
    hiso.integral_inner, sub_zero]

theorem inner_thirdCumulantMatrix_eq_integral (hμ : IsCompact μ.support)
    (x z : Space n) :
    inner ℝ x ((thirdCumulantMatrix μ z).toEuclideanLin x) =
      ∫ y, inner ℝ y z * (inner ℝ y x)^2 ∂μ := by
  have hi (i j : Fin n) : Integrable
      (fun y : Space n => (inner ℝ y z * y i * y j) * x j * x i) μ :=
    integrable_of_continuous_compact_support_measure hμ (by fun_prop)
  have hm (M : Matrix (Fin n) (Fin n) ℝ) :
      inner ℝ x (M.toEuclideanLin x) = ∑ i : Fin n, ∑ j : Fin n, M i j * x j * x i := by
    rw [inner_eq_coordinate_sum]
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Finset.sum_mul]
  have hp (y : Space n) : (inner ℝ y x)^2 =
      ∑ i : Fin n, ∑ j : Fin n, (x i * y i) * (x j * y j) := by
    rw [inner_eq_coordinate_sum]
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, ∫ y : Space n,
        (inner ℝ y z * y i * y j) * x j * x i ∂μ := by
      rw [hm]
      simp only [thirdCumulantMatrix, integral_mul_const]
    _ = ∫ y : Space n, ∑ i : Fin n, ∑ j : Fin n,
        (inner ℝ y z * y i * y j) * x j * x i ∂μ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hi i j)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hp]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem cubic_slice_basis_eq_covariance_quadratic (hμ : IsCompact μ.support)
    (hiso : IsIsotropic μ) (x : Space n) (k : Fin n) :
    curryCubic (cumulantTensor μ 3) x x (EuclideanSpace.single k 1) =
      inner ℝ x ((thirdCumulantMatrix μ (EuclideanSpace.single k 1)).toEuclideanLin x) := by
  rw [curryCubic_apply, isotropic_cumulantTensor_three_integral hμ hiso,
    inner_thirdCumulantMatrix_eq_integral hμ]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem admissible_thirdCumulantMatrix_cubic_seed_four
    (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) (x : Space n) :
    ∑ k, (inner ℝ x ((thirdCumulantMatrix μ (EuclideanSpace.single k 1)).toEuclideanLin x))^2 ≤
      4 * ‖x‖^4 := by
  have hs := admissible_cumulantTensor_three_slice_norm_le hμ hadm x
  have he := (EuclideanSpace.basisFun (Fin n) ℝ).norm_dual (curryCubic (cumulantTensor μ 3) x x)
  simp only [EuclideanSpace.basisFun_apply,
    cubic_slice_basis_eq_covariance_quadratic hμ hadm.isotropic] at he
  rw [← he]
  nlinarith [norm_nonneg (curryCubic (cumulantTensor μ 3) x x)]

end KLS.ConstantReduction
end
