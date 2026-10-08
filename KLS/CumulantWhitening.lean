import KLS.CumulantAffine

/-! The dimension-dependent bound is transported by the actual covariance
whitening, keeping the distinguished direction's covariance factor. -/
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n r : ℕ}

theorem inverse_whitener_square {A P : Matrix (Fin n) (Fin n) ℝ}
    (hwhite : P * A * P = 1) : P⁻¹ * P⁻¹ = A := by
  have hp : IsUnit P.det := by
    apply isUnit_iff_ne_zero.mpr
    intro he
    have h := congrArg Matrix.det hwhite
    simp only [Matrix.det_mul, he, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  calc
    _ = P⁻¹ * 1 * P⁻¹ := by simp
    _ = P⁻¹ * (P * A * P) * P⁻¹ := by rw [hwhite]
    _ = (P⁻¹ * P) * A * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [Matrix.nonsing_inv_mul _ hp, Matrix.mul_nonsing_inv _ hp]; simp

theorem norm_inverse_whitener_sq {A P : Matrix (Fin n) (Fin n) ℝ}
    (hPs : P.transpose = P) (hwhite : P * A * P = 1) (u : Space n) :
    ‖matrixAction P⁻¹ u‖ ^ 2 = inner ℝ u (matrixAction A u) := by
  rw [← real_inner_self_eq_norm_sq, inner_matrixAction_transpose,
    Matrix.transpose_nonsing_inv, hPs, ← MomentMap.matrixAction_mul_apply,
    inverse_whitener_square hwhite]

theorem cumulantTensor_whitened_evaluation {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) (hr : 1 ≤ r)
    (hp : (covarianceMatrix μ).PosDef) (u : Space n) (a : Fin r → Fin n) :
    cumulantTensor μ (r+1) (Fin.cons u (fun s =>
      matrixAction (inverseSqrtMatrix (covarianceMatrix μ)) (EuclideanSpace.single (a s) (1 : ℝ)))) =
    cumulantTensor (whitenedMeasure μ) (r+1) (Fin.cons
      (matrixAction (inverseSqrtMatrix (covarianceMatrix μ))⁻¹ u)
      (fun s => EuclideanSpace.single (a s) (1 : ℝ))) := by
  let P := inverseSqrtMatrix (covarianceMatrix μ)
  have hPs : P.transpose = P := (inverseSqrtMatrix_isSymm _).eq
  have hwhite : P * covarianceMatrix μ * P = 1 := by
    simpa only [P, (inverseSqrtMatrix_isSymm (covarianceMatrix μ)).eq] using
      inverseSqrtMatrix_mul_self_mul_transpose hp
  have hdet : IsUnit P.det := by
    apply isUnit_iff_ne_zero.mpr
    intro he
    have hh := congrArg Matrix.det hwhite
    simp only [Matrix.det_mul, he, zero_mul, Matrix.det_one] at hh
    exact zero_ne_one hh
  rw [whitenedMeasure, cumulantTensor_affineMatrixMeasure hμ (by omega), hPs]
  congr 1
  funext j
  refine Fin.cases ?_ (fun s => rfl) j
  change u = matrixAction P (matrixAction P⁻¹ u)
  rw [← MomentMap.matrixAction_mul_apply, Matrix.mul_nonsing_inv _ hdet]
  ext i
  simp [matrixAction_apply, Matrix.one_apply]

theorem sq_cumulantTensor_whitened_le {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) (hlc : measureLogConcave μ)
    (hr : 1 ≤ r) (hp : (covarianceMatrix μ).PosDef) (u : Space n) (a : Fin r → Fin n) :
    (cumulantTensor μ (r+1) (Fin.cons u (fun s =>
      matrixAction (inverseSqrtMatrix (covarianceMatrix μ)) (EuclideanSpace.single (a s) (1 : ℝ)))))^2 ≤
    cumulantAprioriConstant n (r+1)^2 * inner ℝ u (matrixAction (covarianceMatrix μ) u) := by
  let P := inverseSqrtMatrix (covarianceMatrix μ)
  have hPs : P.transpose = P := (inverseSqrtMatrix_isSymm _).eq
  have hwhite : P * covarianceMatrix μ * P = 1 := by
    simpa only [P, (inverseSqrtMatrix_isSymm (covarianceMatrix μ)).eq] using
      inverseSqrtMatrix_mul_self_mul_transpose hp
  have hn := norm_cumulantTensor_le_apriori (isCompact_support_whitenedMeasure hμ)
    hlc.whitenedMeasure (whitenedMeasure_isIsotropic hlc.memLp_id hp) (r+1)
  rw [cumulantTensor_whitened_evaluation hμ hr hp]
  have hv := (cumulantTensor (whitenedMeasure μ) (r+1)).le_opNorm
    (Fin.cons (matrixAction P⁻¹ u) (fun s => EuclideanSpace.single (a s) (1 : ℝ)))
  have hprod : (∏ j : Fin (r+1), ‖(Fin.cons (matrixAction P⁻¹ u)
      (fun s => EuclideanSpace.single (a s) (1 : ℝ)) : Fin (r+1) → Space n) j‖) = ‖matrixAction P⁻¹ u‖ := by
    rw [Fin.prod_univ_succ]
    simp
  rw [hprod] at hv
  have hv' := hv.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (cumulantAprioriConstant_nonneg _ _) (norm_nonneg _)) |>.mpr hv'
  rw [mul_pow, norm_inverse_whitener_sq hPs hwhite] at hs
  simpa only [Real.norm_eq_abs, sq_abs] using hs

end KLS
end
#print axioms KLS.sq_cumulantTensor_whitened_le
