import KLS.WeightedResolventIntegralDisplacement

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal NNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The actual two-step defect pairing is the loss of centered L2 energy. -/
theorem weightedMassResolvent_square_defect_pairing_eq (hφ : Continuous φ)
    {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (potentialMeasure φ)) :
    inner ℝ (f-weightedMassResolvent φ ht (weightedMassResolvent φ ht f)) f =
      ‖CenteredL2.center (potentialMeasure φ) f‖ ^ 2-
        ‖weightedResolvent φ ht (CenteredL2.center (potentialMeasure φ) f)‖ ^ 2 := by
  have horth : inner ℝ (weightedMassProjection φ f) (CenteredL2.center (potentialMeasure φ) f)=0 := by
    rw [weightedMassProjection_apply,inner_smul_left,conj_trivial,
      CenteredL2.inner_oneLp,CenteredL2.integral_center,mul_zero]
  have horthR : inner ℝ (weightedMassProjection φ f) (weightedResolvent φ ht f)=0 := by
    rw [weightedMassProjection_apply,inner_smul_left,conj_trivial,
      CenteredL2.inner_oneLp,weightedResolvent_integral_eq_zero hφ ht,mul_zero]
  have hdecomp : weightedMassProjection φ f+CenteredL2.center (potentialMeasure φ) f=f := by
    rw [weightedMassProjection_apply,CenteredL2.center]
    abel
  have hnf := norm_add_sq_real (weightedMassProjection φ f) (CenteredL2.center (potentialMeasure φ) f)
  rw [hdecomp,horth,mul_zero,add_zero] at hnf
  have hnR := norm_add_sq_real (weightedMassProjection φ f) (weightedResolvent φ ht f)
  rw [← weightedMassResolvent_apply,horthR,mul_zero,add_zero] at hnR
  rw [inner_sub_left,real_inner_self_eq_norm_sq,weightedMassResolvent_symmetric,
    real_inner_self_eq_norm_sq,weightedResolvent_center hφ ht]
  linarith

/-- The genuine Poincare resolvent contraction gives a lower bound on the
actual defect pairing, with its exact time-dependent factor. -/
theorem weightedMassResolvent_square_defect_pairing_ge
    (hφ : Continuous φ) {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ))
    {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (potentialMeasure φ)) :
    (1-((C : ℝ)/((C : ℝ)+t)) ^ 2)*‖CenteredL2.center (potentialMeasure φ) f‖ ^ 2 ≤
      inner ℝ (f-weightedMassResolvent φ ht (weightedMassResolvent φ ht f)) f := by
  rw [weightedMassResolvent_square_defect_pairing_eq hφ ht]
  have hnorm := weightedResolvent_norm_le_of_poincareConstant hφ hC ht
    (CenteredL2.center (potentialMeasure φ) f)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  rw [mul_pow] at hs
  nlinarith

end KLS
end
