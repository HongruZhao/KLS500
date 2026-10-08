import KLS.HessianTraceIntegration
import KLS.HessianMetricL1DriftExtension

/-!
# The actual integrated trace identity under L¹ potential drift

This version is compatible with unbounded gradient ranges and globally
positive target densities. Integrability of the actual Lφ remains explicit.
-/

open Matrix InnerProductSpace MeasureTheory Set Filter
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

theorem hessianTrace_moment_identity_of_integrable_drift {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hφconv : ConvexOn ℝ univ φ) (hVconv : ConvexOn ℝ univ V)
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hLφ : Integrable (hessianMetricDiffusion φ V φ) (potentialMeasure φ))
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    Integrable (hessianTraceSquare φ B) (potentialMeasure φ) ∧
      Integrable (hessianTraceGradientTerm φ B) (potentialMeasure φ) ∧
      Integrable (hessianTraceTargetTerm φ V B) (potentialMeasure φ) ∧
      Integrable (hessianTraceThirdTerm φ B) (potentialMeasure φ) ∧
      (∫ x, hessianTraceSquare φ B x ∂potentialMeasure φ) =
        (∫ x, hessianTraceGradientTerm φ B x ∂potentialMeasure φ) +
        (∫ x, hessianTraceTargetTerm φ V B x ∂potentialMeasure φ) +
        (∫ x, hessianTraceThirdTerm φ B x ∂potentialMeasure φ) := by
  have hS := contDiff_hessianTraceSquare hφ B
  obtain ⟨C, hC⟩ := exists_bound_hessianTraceSquare hH B
  have hSi : Integrable (hessianTraceSquare φ B) (potentialMeasure φ) :=
    (integrable_const C).mono' hS.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  obtain ⟨hLi, hLzero⟩ := integrable_hessianMetricDiffusion_and_integral_eq_zero_of_integrable_drift
    hφ hV hφconv hpos hMA hLφ hS hC
    (hessianMetricDiffusion_hessianTraceSquare_add_nonneg hφ hV hVconv hpos hMA hB)
  have hsum : Integrable (fun x => hessianTraceGradientTerm φ B x + hessianTraceTargetTerm φ V B x +
      hessianTraceThirdTerm φ B x) (potentialMeasure φ) := by
    convert! (hLi.add (hSi.const_mul 2)).const_mul (1 / 2 : ℝ) using 1
    funext x
    have heq := hessianMetricDiffusion_hessianTraceSquare hφ hV hpos hMA B x
    change hessianTraceGradientTerm φ B x + hessianTraceTargetTerm φ V B x +
      hessianTraceThirdTerm φ B x = (1 / 2 : ℝ) *
        (hessianMetricDiffusion φ V (hessianTraceSquare φ B) x + 2 * hessianTraceSquare φ B x)
    linarith
  have hn (x : Space n) := hessianTrace_evolution_terms_nonneg
    (hφ.of_le (by norm_num)) hV hVconv hpos hB x
  obtain ⟨hAc, hDc, hCc⟩ := continuous_hessianTrace_evolution_terms hφ hV hpos B
  have hAi : Integrable (hessianTraceGradientTerm φ B) (potentialMeasure φ) := by
    apply hsum.mono' hAc.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hn x).1]
    linarith [(hn x).2.1, (hn x).2.2]
  have hDi : Integrable (hessianTraceTargetTerm φ V B) (potentialMeasure φ) := by
    apply hsum.mono' hDc.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hn x).2.1]
    linarith [(hn x).1, (hn x).2.2]
  have hCi : Integrable (hessianTraceThirdTerm φ B) (potentialMeasure φ) := by
    apply hsum.mono' hCc.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hn x).2.2]
    linarith [(hn x).1, (hn x).2.1]
  refine ⟨hSi, hAi, hDi, hCi, ?_⟩
  have heq : (∫ x, hessianMetricDiffusion φ V (hessianTraceSquare φ B) x + 2 * hessianTraceSquare φ B x
      ∂potentialMeasure φ) = ∫ x, 2 * (hessianTraceGradientTerm φ B x + hessianTraceTargetTerm φ V B x +
        hessianTraceThirdTerm φ B x) ∂potentialMeasure φ := by
    apply integral_congr_ae
    exact Eventually.of_forall (hessianMetricDiffusion_hessianTraceSquare hφ hV hpos hMA B)
  rw [integral_add hLi (hSi.const_mul 2), integral_const_mul, hLzero,
    integral_const_mul, integral_add
      (f := fun x => hessianTraceGradientTerm φ B x + hessianTraceTargetTerm φ V B x)
      (g := hessianTraceThirdTerm φ B) (hAi.add hDi) hCi, integral_add hAi hDi] at heq
  linarith

end KLS
end

#print axioms KLS.hessianTrace_moment_identity_of_integrable_drift
