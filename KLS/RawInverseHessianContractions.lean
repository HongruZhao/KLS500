import KLS.TensorInverseMetric

open Matrix
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section
namespace KLS

variable {n : ℕ}

/-- The actual Hessian cancels the final inverse factor in the column
contraction used by bounded compact H1 testing. -/
theorem raw_inverse_hessian_column_times_hessian
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) (hu : IsUnit H.det)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a j k : Fin n) :
    (∑ i, (H⁻¹ * T j * H⁻¹) a i * H k i) = (H⁻¹ * T j) a k := by
  calc
    _ = ∑ i, (H⁻¹ * T j * H⁻¹) a i * H i k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hH.apply i k]
    _ = ((H⁻¹ * T j * H⁻¹) * H) a k := Matrix.mul_apply.symm
    _ = (H⁻¹ * T j) a k := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

/-- The remaining raw weak-third-tensor contraction is the ordered trace
Gram entry. Both adjacent tensor symmetries are explicit. -/
theorem raw_inverse_hessian_column_times_third
    (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hfirst : ∀ a k i, T a k i = T k a i)
    (hlast : ∀ a k i, T a k i = T a i k) (j k : Fin n) :
    (∑ a, ∑ i, (H⁻¹ * T j * H⁻¹) a i * T a k i) =
      (H⁻¹ * T j * H⁻¹ * T k).trace := by
  calc
    _ = ∑ a, ∑ i, (H⁻¹ * T j * H⁻¹) a i * T k a i := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      rw [hfirst a k i]
    _ = _ := matrix_entrywise_contraction_eq_trace _ _
      (Matrix.IsSymm.ext fun a i => (hlast k a i).symm)

end KLS
end
