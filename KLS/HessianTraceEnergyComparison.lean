import KLS.HessianTraceL1DriftIntegration
import KLS.TensorInverseMetric

/-!
# Integrated comparison of the actual Hessian trace energies

The weighted tensor comparison bounds the first evolution contraction by
half the Hessian trace-square integral. All four integrability obligations
come from the actual diffusion identity and the L¹-drift cutoff argument.
-/

open Matrix InnerProductSpace MeasureTheory Set Filter
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace KLS

variable {n : ℕ}

theorem integral_hessianTraceGradientTerm_le_half_square {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hφconv : ConvexOn ℝ univ φ) (hVconv : ConvexOn ℝ univ V)
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hLφ : Integrable (hessianMetricDiffusion φ V φ) (potentialMeasure φ))
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    (∫ x, hessianTraceGradientTerm φ B x ∂potentialMeasure φ) ≤
      (1 / 2 : ℝ) * ∫ x, hessianTraceSquare φ B x ∂potentialMeasure φ := by
  obtain ⟨hSi, hAi, hDi, hCi, hid⟩ :=
    hessianTrace_moment_identity_of_integrable_drift
      hφ hV hφconv hVconv hpos hMA hLφ hH hB
  have hAC := integral_mono hAi hCi
    (hessianTraceGradientTerm_le_third (hφ.of_le (by norm_num)) hpos hB.isHermitian.isSymm)
  have hD : 0 ≤ ∫ x, hessianTraceTargetTerm φ V B x ∂potentialMeasure φ :=
    integral_nonneg fun x => (hessianTrace_evolution_terms_nonneg
      (hφ.of_le (by norm_num)) hV hVconv hpos hB x).2.1
  linarith

end KLS
end

#print axioms KLS.integral_hessianTraceGradientTerm_le_half_square
