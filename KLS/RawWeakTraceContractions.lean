import KLS.RawHessianTraceTerms

open Matrix
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

lemma raw_trace_sum_four_block_swap (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  exact Finset.sum_comm

/-- The weak-test contraction is an identity on raw matrix and tensor
values. Its application needs the actual weak derivative of the test. -/
theorem raw_weak_hessian_trace_left
    (H B : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ b, (T b).IsSymm) (χ : ℝ) (dχ : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, H⁻¹ a b *
      (dχ a * (B * H * B) i j + χ * (B * T a * B) i j) * T b i j) =
      (∑ a, ∑ b, H⁻¹ a b * dχ a * (B * H * B * T b).trace) +
        χ * rawHessianTraceGradientTerm H B T := by
  rw [raw_trace_sum_four_block_swap]
  have hp (a b : Fin n) :
      (∑ i, ∑ j, H⁻¹ a b *
        (dχ a * (B * H * B) i j + χ * (B * T a * B) i j) * T b i j) =
      H⁻¹ a b * dχ a * (B * H * B * T b).trace +
        χ * (H⁻¹ a b * (B * T a * B * T b).trace) := by
    rw [← matrix_entrywise_contraction_eq_trace _ _ (hT b),
      ← matrix_entrywise_contraction_eq_trace _ _ (hT b)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hp, Finset.sum_add_distrib]
  rw [rawHessianTraceGradientTerm]
  simp only [Finset.mul_sum]

/-- Contraction of a literal weak Hessian right side preserves the matrix
order. No classical Hessian or third derivative is used. -/
theorem raw_weak_hessian_trace_right
    {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) (hM : M.PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (∑ i, ∑ j, (B * H * B) i j *
      (-H i j + (H * M * H) i j + (H⁻¹ * T i * H⁻¹ * T j).trace)) =
      -rawHessianTraceSquare H B + rawHessianTraceTargetTerm H M B +
        rawHessianTraceThirdTerm H B T := by
  have hK : (H * M * H).PosSemidef := by
    simpa only [hH.isHermitian.eq] using hM.conjTranspose_mul_mul_same H
  have hQ := matrixTraceGram_posSemidef hH.posSemidef.inv T hT
  change (∑ i, ∑ j, (B * H * B) i j *
    (-H i j + (H * M * H) i j + matrixTraceGram H⁻¹ T i j)) = _
  simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [matrix_entrywise_contraction_eq_trace _ _ hH.isHermitian.isSymm,
    matrix_entrywise_contraction_eq_trace _ _ hK.isHermitian.isSymm,
    matrix_entrywise_contraction_eq_trace _ _ hQ.isHermitian.isSymm]
  rfl

end KLS
end
