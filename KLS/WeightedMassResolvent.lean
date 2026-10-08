import KLS.WeightedResolventIteration

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace NNReal

noncomputable section
namespace KLS
variable {n : ℕ} (φ : Space n → ℝ) [IsProbabilityMeasure (potentialMeasure φ)]

/-- Projection onto actual constant functions, with the actual integral as coefficient. -/
def weightedMassProjection :
    Lp ℝ 2 (potentialMeasure φ) →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  (innerSL ℝ (CenteredL2.oneLp (potentialMeasure φ))).smulRight
    (CenteredL2.oneLp (potentialMeasure φ))

theorem weightedMassProjection_apply (g : Lp ℝ 2 (potentialMeasure φ)) :
    weightedMassProjection φ g =
      (∫ x, g x ∂potentialMeasure φ) • CenteredL2.oneLp (potentialMeasure φ) := by
  simp [weightedMassProjection, CenteredL2.inner_oneLp]

theorem weightedMassProjection_symmetric (f g : Lp ℝ 2 (potentialMeasure φ)) :
    inner ℝ (weightedMassProjection φ f) g = inner ℝ f (weightedMassProjection φ g) := by
  rw [weightedMassProjection_apply, weightedMassProjection_apply, inner_smul_left, inner_smul_right,
    CenteredL2.inner_oneLp, real_inner_comm (CenteredL2.oneLp (potentialMeasure φ)) f,
    CenteredL2.inner_oneLp]
  simp only [conj_trivial]
  ring

/-- Restore the actual mean to the constructed centered resolvent. Order
preservation and gradient smoothing are not included in this definition. -/
def weightedMassResolvent {t : ℝ} (ht : 0 < t) :
    Lp ℝ 2 (potentialMeasure φ) →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  weightedMassProjection φ + weightedResolvent φ ht

theorem weightedMassResolvent_apply {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    weightedMassResolvent φ ht g = weightedMassProjection φ g + weightedResolvent φ ht g := rfl

theorem weightedMassResolvent_symmetric {t : ℝ} (ht : 0 < t)
    (f g : Lp ℝ 2 (potentialMeasure φ)) :
    inner ℝ (weightedMassResolvent φ ht f) g = inner ℝ f (weightedMassResolvent φ ht g) := by
  rw [weightedMassResolvent_apply, weightedMassResolvent_apply, inner_add_left, inner_add_right,
    weightedMassProjection_symmetric, weightedResolvent_symmetric]

variable {φ}

theorem weightedResolvent_one_eq_zero (hφ : Continuous φ) {t : ℝ} (ht : 0 < t) :
    weightedResolvent φ ht (CenteredL2.oneLp (potentialMeasure φ)) = 0 := by
  have hU : (0 : WeightedCenteredH1 φ) =
      weightedResolventH1 φ ht (CenteredL2.oneLp (potentialMeasure φ)) := by
    apply weightedResolvent_unique
    intro V
    simp only [map_zero, inner_zero_left, zero_apply, mul_zero, zero_add]
    rw [CenteredL2.inner_oneLp, weightedH1_integral_eq_zero hφ V]
  change weightedH1Value φ (weightedResolventH1 φ ht (CenteredL2.oneLp (potentialMeasure φ))) = 0
  rw [← hU, map_zero]

theorem weightedResolvent_center (hφ : Continuous φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    weightedResolvent φ ht (CenteredL2.center (potentialMeasure φ) g) = weightedResolvent φ ht g := by
  simp [CenteredL2.center, weightedResolvent_one_eq_zero hφ ht]

theorem weightedMassResolvent_ae {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    (weightedMassResolvent φ ht g : Space n → ℝ) =ᵐ[potentialMeasure φ]
      fun x => (∫ y, g y ∂potentialMeasure φ) + weightedResolvent φ ht g x := by
  rw [weightedMassResolvent_apply, weightedMassProjection_apply]
  filter_upwards [Lp.coeFn_add ((∫ y, g y ∂potentialMeasure φ) •
    CenteredL2.oneLp (potentialMeasure φ)) (weightedResolvent φ ht g),
    Lp.coeFn_smul (∫ y, g y ∂potentialMeasure φ) (CenteredL2.oneLp (potentialMeasure φ)),
    CenteredL2.oneLp_ae (potentialMeasure φ)] with x hx hy hz
  simp only [hx, Pi.add_apply, hy, Pi.smul_apply, smul_eq_mul, hz, mul_one]

/-- The constructed full resolvent preserves the actual integral. -/
theorem weightedMassResolvent_integral (hφ : Continuous φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    (∫ x, weightedMassResolvent φ ht g x ∂potentialMeasure φ) = ∫ x, g x ∂potentialMeasure φ := by
  rw [← CenteredL2.inner_oneLp, weightedMassResolvent_apply, inner_add_right,
    weightedMassProjection_apply, inner_smul_right, CenteredL2.inner_oneLp,
    CenteredL2.integral_oneLp, mul_one, CenteredL2.inner_oneLp,
    weightedResolvent_integral_eq_zero hφ ht g, add_zero]

/-- The same operator preserves the actual constant one. -/
theorem weightedMassResolvent_one (hφ : Continuous φ) {t : ℝ} (ht : 0 < t) :
    weightedMassResolvent φ ht (CenteredL2.oneLp (potentialMeasure φ)) =
      CenteredL2.oneLp (potentialMeasure φ) := by
  rw [weightedMassResolvent_apply, weightedResolvent_one_eq_zero hφ ht, add_zero,
    weightedMassProjection_apply, CenteredL2.integral_oneLp, one_smul]

theorem center_weightedMassResolvent (hφ : Continuous φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    CenteredL2.center (potentialMeasure φ) (weightedMassResolvent φ ht g) =
      weightedResolvent φ ht (CenteredL2.center (potentialMeasure φ) g) := by
  rw [CenteredL2.center, weightedMassResolvent_integral hφ ht g,
    weightedMassResolvent_apply, weightedMassProjection_apply,
    weightedResolvent_center hφ ht g]
  abel

/-- L2 contraction also holds for the full mass-preserving resolvent. -/
theorem weightedMassResolvent_norm_le (hφ : Continuous φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) : ‖weightedMassResolvent φ ht g‖ ≤ ‖g‖ := by
  have horth : inner ℝ (weightedMassProjection φ g) (CenteredL2.center (potentialMeasure φ) g) = 0 := by
    rw [weightedMassProjection_apply, inner_smul_left, CenteredL2.inner_oneLp,
      CenteredL2.integral_center, mul_zero]
  have horthR : inner ℝ (weightedMassProjection φ g) (weightedResolvent φ ht g) = 0 := by
    rw [weightedMassProjection_apply, inner_smul_left, CenteredL2.inner_oneLp,
      weightedResolvent_integral_eq_zero hφ ht g, mul_zero]
  have hg : weightedMassProjection φ g + CenteredL2.center (potentialMeasure φ) g = g := by
    rw [weightedMassProjection_apply, CenteredL2.center]
    abel
  have hgnorm := norm_add_sq_real (weightedMassProjection φ g) (CenteredL2.center (potentialMeasure φ) g)
  rw [hg, horth, mul_zero, add_zero] at hgnorm
  have hTnorm := norm_add_sq_real (weightedMassProjection φ g) (weightedResolvent φ ht g)
  rw [← weightedMassResolvent_apply, horthR, mul_zero, add_zero] at hTnorm
  have hR := weightedResolvent_norm_le φ ht (CenteredL2.center (potentialMeasure φ) g)
  rw [weightedResolvent_center hφ ht g] at hR
  nlinarith [norm_nonneg (weightedResolvent φ ht g),
    norm_nonneg (CenteredL2.center (potentialMeasure φ) g), norm_nonneg g,
    norm_nonneg (weightedMassResolvent φ ht g)]

/-- Spectral decay for actual centered iterates of the mass-preserving operator. -/
theorem weightedMassResolvent_iterate_center_norm_le (hφ : Continuous φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ))
    {t : ℝ} (ht : 0 < t) (k : ℕ) (g : Lp ℝ 2 (potentialMeasure φ)) :
    ‖CenteredL2.center (potentialMeasure φ) ((weightedMassResolvent φ ht)^[k] g)‖ ≤
      ((C : ℝ) / ((C : ℝ) + t)) ^ k * ‖CenteredL2.center (potentialMeasure φ) g‖ := by
  have he : CenteredL2.center (potentialMeasure φ) ((weightedMassResolvent φ ht)^[k] g) =
      (weightedResolvent φ ht)^[k] (CenteredL2.center (potentialMeasure φ) g) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', center_weightedMassResolvent hφ ht,
        ih, Function.iterate_succ_apply']
  rw [he]
  exact weightedResolvent_iterate_norm_le hφ hC ht k _

end KLS
end
