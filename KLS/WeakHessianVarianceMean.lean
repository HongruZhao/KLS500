import KLS.WeakMatrixCongruence
import KLS.WeakHessianMean
import KLS.HessianEntryBrascampLieb

open Matrix InnerProductSpace MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ContDiff ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem memLp_hessianCongruence_entry_C11 {φ : Space n → ℝ} {G : ℝ≥0}
    [IsFiniteMeasure (potentialMeasure φ)] (hG : LipschitzWith G (gradient φ))
    (R : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    MemLp (fun x => hessianCongruence φ R x a b) 2 (potentialMeasure φ) :=
  memLp_two_matrixCongruence_raw
    (fun i j => memLp_actual_hessian_entry_of_global_gradient_lipschitz hG i j 2) R a b

theorem integral_hessianCongruence_entry_C11 {φ : Space n → ℝ} {G : ℝ≥0}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    (hG : LipschitzWith G (gradient φ))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (R : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    (∫ x, hessianCongruence φ R x a b ∂potentialMeasure φ) = (R * R.transpose) a b := by
  change (∫ x, (R * coordinateHessian φ x * R.transpose) a b ∂potentialMeasure φ) = _
  rw [integral_matrix_congruence_entry
    (fun i j => (memLp_actual_hessian_entry_of_global_gradient_lipschitz (μ := potentialMeasure φ) hG i j 2).integrable (by norm_num))]
  have heq : Matrix.of (fun i j => ∫ x, coordinateHessian φ x i j ∂potentialMeasure φ) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    exact integral_actual_hessian_entry_eq_one_C11 hφ hG hiso i j
  rw [heq, Matrix.mul_one]

/-- The centered matrix trace moment is already the sum of genuine scalar
variances at C1,1. No PDE identity or variance inequality is assumed. -/
theorem sum_variance_hessianCongruence_C11 {φ : Space n → ℝ} {G : ℝ≥0}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    (hG : LipschitzWith G (gradient φ))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (R : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a, ∑ b, ProbabilityTheory.variance (fun x => hessianCongruence φ R x a b)
      (potentialMeasure φ)) =
      (∫ x, hessianTraceSquare φ (R.transpose * R) x ∂potentialMeasure φ) -
        ((R.transpose * R) * (R.transpose * R)).trace := by
  have hf2 (a b : Fin n) := memLp_hessianCongruence_entry_C11 hG R a b
  have hvar (a b : Fin n) :
      ProbabilityTheory.variance (fun x => hessianCongruence φ R x a b) (potentialMeasure φ) =
      (∫ x, hessianCongruence φ R x a b ^ 2 ∂potentialMeasure φ) - (R * R.transpose) a b ^ 2 := by
    rw [variance_eq_sub (hf2 a b), integral_hessianCongruence_entry_C11 hφ hG hiso]
    rfl
  simp_rw [hvar, Finset.sum_sub_distrib]
  have hmean : (∑ a, ∑ b, (R * R.transpose) a b ^ 2) =
      ((R.transpose * R) * (R.transpose * R)).trace := by
    simpa only [Matrix.mul_one, matrixFrobeniusSq] using
      matrixFrobeniusSq_affine_congruence R 1 Matrix.isSymm_one
  rw [hmean]
  congr 1
  calc
    (∑ a, ∑ b, ∫ x, hessianCongruence φ R x a b ^ 2 ∂potentialMeasure φ) =
        ∑ a, ∫ x, ∑ b, hessianCongruence φ R x a b ^ 2 ∂potentialMeasure φ := by
      apply Finset.sum_congr rfl
      intro a _
      exact (integral_finsetSum Finset.univ (fun b _ => (hf2 a b).integrable_sq)).symm
    _ = ∫ x, ∑ a, ∑ b, hessianCongruence φ R x a b ^ 2 ∂potentialMeasure φ :=
      (integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ
        (fun b _ => (hf2 a b).integrable_sq))).symm
    _ = _ := by
      apply integral_congr_ae
      have hs : ∀ᵐ x ∂potentialMeasure φ, (coordinateHessian φ x).IsSymm :=
        (withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal (Real.exp (-φ x)))).ae_le
          (actual_hessian_ae_symmetric_of_locallyLipschitz_gradient hφ.locallyLipschitz hG.locallyLipschitz)
      filter_upwards [hs] with x hx
      exact matrixFrobeniusSq_affine_congruence R (coordinateHessian φ x) hx

end KLS
end
