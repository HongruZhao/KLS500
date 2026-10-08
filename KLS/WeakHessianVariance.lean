import KLS.WeakHessianCongruenceEnergy
import KLS.C1DiffusionLiouville

open Matrix InnerProductSpace MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ContDiff ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The original raw weak finite-energy estimate, with diffusion-range
density proved directly at C1 regularity. -/
theorem brascampLieb_variance_raw_weak_C11
    {φ f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hG : LocallyLipschitz (gradient φ))
    (hpos : ∀ᵐ x, (coordinateHessian φ x).PosDef)
    (hf2 : MemLp f 2 (potentialMeasure φ))
    (hFl : ∀ i, LocallyIntegrable (F i) volume)
    (hFw : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i)
    (hinv : Integrable (rawInverseHessianGradientForm φ F) (potentialMeasure φ)) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      ∫ x, rawInverseHessianGradientForm φ F x ∂potentialMeasure φ :=
  brascampLieb_variance_raw_weak_of_rangeDense hφ hG hpos hf2 hFl hFw hinv
    (diffusionRangeDense_of_contDiff_C1 hφ)

theorem hasLocalWeakCoordinateDerivative_actual_hessianCongruence
    {φ : Space n → ℝ} {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hG : LocallyLipschitz (gradient φ))
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian φ x i j) (fun x => T x k i j) k)
    (R : Matrix (Fin n) (Fin n) ℝ) (k a b : Fin n) :
    HasLocalWeakCoordinateDerivative (fun x => hessianCongruence φ R x a b)
      (fun x => (R * T x k * R.transpose) a b) k :=
  hasLocalWeakCoordinateDerivative_matrixCongruence_raw (hTw k)
    (fun i j _ hS => memLp_top_actual_hessian_of_locallyLipschitz_gradient hG i j hS)
    (hTl k) R a b

/-- Genuine scalar weak Brascamp--Lieb bounds for all congruence entries
sum to the exact centered trace estimate at original C1,1 regularity. -/
theorem rawHessianTrace_variance_control_of_factor_C11
    {φ : Space n → ℝ} {G : ℝ≥0} {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hG : LipschitzWith G (gradient φ))
    (hpos : ∀ᵐ x, (coordinateHessian φ x).PosDef)
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian φ x i j) (fun x => T x k i j) k)
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (R : Matrix (Fin n) (Fin n) ℝ)
    (hA : Integrable (fun x => rawHessianTraceGradientTerm (coordinateHessian φ x)
      (R.transpose * R) (T x)) (potentialMeasure φ)) :
    (∫ x, rawHessianTraceSquare (coordinateHessian φ x) (R.transpose * R) ∂potentialMeasure φ) -
      ((R.transpose * R) * (R.transpose * R)).trace ≤
        ∫ x, rawHessianTraceGradientTerm (coordinateHessian φ x) (R.transpose * R) (T x)
          ∂potentialMeasure φ := by
  have hTs : ∀ᵐ x, ∀ k, (T x k).IsSymm := by
    filter_upwards [actual_weak_third_tensor_ae_symmetric hφ.locallyLipschitz
      hG.locallyLipschitz hTl hTw] with x hx
    exact fun k => Matrix.IsSymm.ext (fun i j => (hx k j i).2)
  change (∫ x, hessianTraceSquare φ (R.transpose * R) x ∂potentialMeasure φ) - _ ≤ _
  rw [← sum_variance_hessianCongruence_C11 hφ hG hiso R,
    ← sum_integral_raw_energy_hessianCongruence hpos hTl hTs R hA]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  exact brascampLieb_variance_raw_weak_C11 hφ hG.locallyLipschitz hpos
    (memLp_hessianCongruence_entry_C11 hG R a b)
    (fun k => locallyIntegrable_of_memLp_two_on_compacts (fun S hS =>
      memLp_two_matrixCongruence_raw (fun i j => hTl k i j S hS) R a b))
    (fun k => hasLocalWeakCoordinateDerivative_actual_hessianCongruence hG.locallyLipschitz hTl hTw R k a b)
    (integrable_raw_hessianCongruence_energy hpos hTl hTs R hA a b)

/-- The actual spectral square root yields the bound for every PSD matrix.
The only global energy premise is integrability of the actual raw trace term. -/
theorem rawHessianTrace_variance_control_C11
    {φ : Space n → ℝ} {G : ℝ≥0} {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hG : LipschitzWith G (gradient φ))
    (hpos : ∀ᵐ x, (coordinateHessian φ x).PosDef)
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian φ x i j) (fun x => T x k i j) k)
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef)
    (hA : Integrable (fun x => rawHessianTraceGradientTerm (coordinateHessian φ x) B (T x))
      (potentialMeasure φ)) :
    (∫ x, rawHessianTraceSquare (coordinateHessian φ x) B ∂potentialMeasure φ) - (B * B).trace ≤
      ∫ x, rawHessianTraceGradientTerm (coordinateHessian φ x) B (T x) ∂potentialMeasure φ := by
  obtain ⟨R, _, hR⟩ := exists_symmetric_matrix_square_root hB
  have hAR : Integrable (fun x => rawHessianTraceGradientTerm (coordinateHessian φ x)
      (R.transpose * R) (T x)) (potentialMeasure φ) := by simpa only [hR] using hA
  simpa only [hR] using rawHessianTrace_variance_control_of_factor_C11 hφ hG hpos hTl hTw hiso R hAR

end KLS
end
