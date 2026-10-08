import KLS.TensorInverseMetric

open Matrix
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

/-- The trace energy is defined on actual matrix values and an explicitly
supplied raw weak third tensor. No classical third derivative is used. -/
def rawHessianTraceSquare (H B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (B * H * B * H).trace

def rawHessianTraceGradientTerm (H B : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, H⁻¹ i j * (B * T i * B * T j).trace

def rawHessianTraceTargetTerm (H M B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ((B * H * B) * (H * M * H)).trace

def rawHessianTraceThirdTerm (H B : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ((B * H * B) * matrixTraceGram H⁻¹ T).trace

theorem rawHessianTrace_terms_nonneg
    {H M B : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hM : M.PosSemidef) (hB : B.PosSemidef)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    0 ≤ rawHessianTraceGradientTerm H B T ∧
      0 ≤ rawHessianTraceTargetTerm H M B ∧
      0 ≤ rawHessianTraceThirdTerm H B T := by
  have hBHB : (B * H * B).PosSemidef := by
    simpa only [hB.isHermitian.eq] using hH.posSemidef.conjTranspose_mul_mul_same B
  have hTarget : (H * M * H).PosSemidef := by
    simpa only [hH.isHermitian.eq] using hM.conjTranspose_mul_mul_same H
  exact ⟨inverse_weighted_traceGram_nonneg hH.posSemidef.inv hB T hT,
    trace_mul_nonneg_of_posSemidef hBHB hTarget,
    trace_mul_nonneg_of_posSemidef hBHB (matrixTraceGram_posSemidef hH.posSemidef.inv T hT)⟩

/-- Both tensor symmetries are explicit; they must be obtained from the
actual weak derivative identities before applying this algebraic result. -/
theorem rawHessianTrace_gradient_le_third
    {H B : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) (hB : B.IsSymm)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hfirst : ∀ i j k, T i j k = T j i k)
    (hlast : ∀ i j k, T i j k = T i k j) :
    rawHessianTraceGradientTerm H B T ≤ rawHessianTraceThirdTerm H B T := by
  have hT (i : Fin n) : (T i).IsSymm :=
    Matrix.IsSymm.ext (fun j k => (hlast i j k).symm)
  have hQ := matrixTraceGram_posSemidef hH.posSemidef.inv T hT
  unfold rawHessianTraceGradientTerm rawHessianTraceThirdTerm
  rw [← matrix_entrywise_contraction_eq_trace _ _ hQ.isHermitian.isSymm]
  exact inverse_metric_trace_tensor_comparison hH hB T hfirst hlast

end KLS
end
