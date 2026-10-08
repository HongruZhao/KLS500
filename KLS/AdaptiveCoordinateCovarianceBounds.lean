import KLS.AdaptiveCoordinateCovariance

/-! Globally bounded true covariance gradients from compact base support. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.FiniteFeatureTilt
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem ae_norm_le_law (hμ : IsCompact μ.support) {R : ℝ}
    (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R) (p : Parameter n) :
    ∀ᵐ x ∂law μ p.1 p.2, ‖x‖ ≤ R := by
  haveI := law_isProbability hμ p.1 p.2
  filter_upwards [(law μ p.1 p.2).support_mem_ae] with x hx
  exact hR x (by rwa [support_law hμ] at hx)

theorem norm_coordinateCovariance_line_deriv_le (hμ : IsCompact μ.support)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R)
    (i j : Fin n) (z v : Fin (n+n*n) → ℝ) :
    ‖tiltThirdCumulant μ (exponent (decodeState z).1 (decodeState z).2)
      (fun x => x i) (fun x => x j) (coordinateScore v)‖ ≤
      coordinateCovarianceDerivativeBound n R * ‖v‖ := by
  have hb (k : Fin n) : ∀ᵐ x ∂μ.tilted (exponent (decodeState z).1 (decodeState z).2), ‖x k‖ ≤ R :=
    (ae_norm_le_law hμ hR (decodeState z)).mono fun x hx => (PiLp.norm_apply_le x k).trans hx
  have hs : ∀ᵐ x ∂μ.tilted (exponent (decodeState z).1 (decodeState z).2),
      ‖coordinateScore v x‖ ≤ coordinateScoreBound n R * ‖v‖ := by
    filter_upwards [ae_norm_le_law hμ hR (decodeState z)] with x hx
    exact abs_coordinateScore_le hR0 v x hx
  have hh := norm_tiltThirdCumulant_le_of_bounds hμ
    (continuous_exponent (decodeState z).1 (decodeState z).2) hR0 hR0
    (mul_nonneg (coordinateScoreBound_nonneg hR0) (norm_nonneg _)) (hb i) (hb j) hs
  calc _ ≤ 8 * R * R * (coordinateScoreBound n R * ‖v‖) := hh
    _ = _ := by unfold coordinateCovarianceDerivativeBound; ring

theorem norm_coordinateCovariance_sub_le (hμ : IsCompact μ.support)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R)
    (i j : Fin n) (z₁ z₂ : Fin (n+n*n) → ℝ) :
    ‖coordinateCovariance μ i j z₁ - coordinateCovariance μ i j z₂‖ ≤
      coordinateCovarianceDerivativeBound n R * ‖z₁ - z₂‖ := by
  have hd (u : ℝ) := hasDerivAt_coordinateCovariance_line hμ i j z₂ (z₁-z₂) u
  have hb (u : ℝ) := norm_coordinateCovariance_line_deriv_le hμ hR0 hR i j (z₂+u•(z₁-z₂)) (z₁-z₂)
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun u _ => (hd u).hasDerivWithinAt) (fun u _ => hb u)
  simpa only [one_smul, zero_smul, add_zero, add_sub_cancel] using hh

theorem norm_coordinateCovarianceGradient_le (hμ : IsCompact μ.support)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R)
    (i j : Fin n) (z : Fin (n+n*n) → ℝ) :
    ‖coordinateCovarianceGradient μ i j z‖ ≤ coordinateCovarianceDerivativeBound n R :=
  norm_fderiv_le_of_lip' ℝ (coordinateCovarianceDerivativeBound_nonneg hR0)
    (Eventually.of_forall fun w => norm_coordinateCovariance_sub_le hμ hR0 hR i j w z)

theorem coordinateCovarianceGradient_apply_eq_cumulant (hμ : IsCompact μ.support)
    (i j : Fin n) (z v : Fin (n+n*n) → ℝ) :
    coordinateCovarianceGradient μ i j z v =
      tiltThirdCumulant μ (exponent (decodeState z).1 (decodeState z).2)
        (fun x => x i) (fun x => x j) (coordinateScore v) := by
  have hp : HasDerivAt (fun u : ℝ => z + u • v) v 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z using 1 <;>
      simp only [Pi.add_apply, id_eq, one_smul, zero_add]
  have hc := (hasFDerivAt_coordinateCovariance hμ i j z).comp_hasDerivAt_of_eq 0 hp (by simp)
  have hc' : HasDerivAt (fun u : ℝ => coordinateCovariance μ i j (z + u • v))
      (coordinateCovarianceGradient μ i j z v) 0 := by
    convert hc using 1
    funext u
    rfl
  have hd := hasDerivAt_coordinateCovariance_line hμ i j z v 0
  apply hc'.unique
  simpa only [zero_smul, add_zero] using hd

theorem coordinateCovarianceHessian_apply_eq_cumulant (hμ : IsCompact μ.support)
    (i j : Fin n) (z u v : Fin (n+n*n) → ℝ) :
    coordinateCovarianceHessian μ i j z u v =
      tiltFourthCumulant μ (exponent (decodeState z).1 (decodeState z).2)
        (fun x => x i) (fun x => x j) (coordinateScore v) (coordinateScore u) := by
  have hp : HasDerivAt (fun a : ℝ => z + a • u) u 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z using 1 <;>
      simp only [Pi.add_apply, id_eq, one_smul, zero_add]
  have hc := (hasFDerivAt_coordinateCovarianceGradient hμ i j z).comp_hasDerivAt_of_eq 0 hp (by simp)
  have he := hc.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have he' : HasDerivAt (fun a : ℝ => coordinateCovarianceGradient μ i j (z+a•u) v)
      (coordinateCovarianceHessian μ i j z u v) 0 := by
    convert he using 1 <;> simp
  have hd := hasDerivAt_tiltThirdCumulant hμ
    (continuous_exponent (decodeState z).1 (decodeState z).2)
    (f := fun x => x i) (g := fun x => x j) (by fun_prop) (by fun_prop)
    (continuous_coordinateScore v) (continuous_coordinateScore u) 0
  have hd' : HasDerivAt (fun a : ℝ => coordinateCovarianceGradient μ i j (z+a•u) v)
      (tiltFourthCumulant μ (exponent (decodeState z).1 (decodeState z).2)
        (fun x => x i) (fun x => x j) (coordinateScore v) (coordinateScore u)) 0 := by
    simp_rw [coordinateCovarianceGradient_apply_eq_cumulant hμ]
    simpa only [coordinate_exponent_line, zero_mul, add_zero] using hd
  exact he'.unique hd'

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.norm_coordinateCovarianceGradient_le
#print axioms KLS.AdaptiveLocalization.coordinateCovarianceHessian_apply_eq_cumulant
