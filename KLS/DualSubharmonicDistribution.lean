import KLS.LocalNormalizedSubharmonicity
import KLS.LocalizedReciprocalEquation
import KLS.CompactLaplacianPairing

open MeasureTheory InnerProductSpace Matrix Set Filter Metric
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The negative actual normalized dual error with a vanishing correction. -/
def subharmonicNegativeDualError (u : Space n → ℝ) (c ε : ℝ) : Space n → ℝ :=
  fun p => -normalizedDualQuadraticError u 0 0 c ε p +
    (2 * ε) * centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 p

lemma subharmonicNegativeDualError_eq_truncated
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {c R δ ε : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ)
    {p : Space n} (hp : p ∈ ball (0 : Space n) (R / 4)) :
    subharmonicNegativeDualError u c ε p =
      subharmonicNormalizedError (truncatedLegendrePotential u (R + 1)) 0 0 (-c) ε p := by
  have he := truncatedLegendrePotential_eq_on_agreementRegion hu hc
    (ball_subset_truncatedConjugateAgreementRegion_of_quadratic_closeness hu hc hR hδ hclose hp)
  simp only [subharmonicNegativeDualError, subharmonicNormalizedError,
    normalizedDualQuadraticError, normalizedQuadraticError, he, centeredDualQuadratic,
    centeredQuadratic, sub_zero, inner_zero_right, inner_zero_left, zero_add, add_zero,
    matrixAction_one_apply, real_inner_self_eq_norm_sq]
  ring

/-- The inverse weak transport equation and primal density bound imply the
actual distribution inequality for the negative dual error. -/
theorem integral_subharmonicNegativeDualError_mul_laplacian_nonneg (hn : 0 < n)
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u) (hV : Continuous V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {c r s R δ ε : ℝ} (hε : 0 < ε) (hr : 0 < r) (hrs : r < s) (hsR : s < R / 4)
    (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) R,
      |Real.exp (-u x + V (gradient u x)) - 1| ≤ ε ^ 2)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball (0 : Space n) r) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ p, subharmonicNegativeDualError u c ε p * coordinateLaplacian φ p := by
  have hR : 0 < R := by linarith
  have hRm : 0 ≤ R + 1 := by linarith
  have htr := (lipschitzWith_truncatedLegendrePotential hLip.continuous hRm).continuous
  have htc := convexOn_truncatedLegendrePotential hLip.continuous hRm
  have hbound : ∀ x ∈ closedBall (0 : Space n) s,
      ∀ ψ : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun y => subharmonicNormalizedError (truncatedLegendrePotential u (R + 1))
        0 0 (-c) ε y - ψ y) x → 0 ≤ coordinateLaplacian ψ x := by
    intro x hx ψ hψ hm
    have hxU : x ∈ ball (0 : Space n) (R / 4) := lt_of_le_of_lt hx hsR
    have hd := reciprocal_density_log_bound_of_quadratic_closeness hu hc hV hR hδ hclose hdensity hxU
    exact subharmonicNormalizedError_upper_test_of_local_log_density hn htr htc hd.1
      (Real.exp_pos _) (isOpen_ball.mem_nhds hxU)
      (fun _S hS hSU => localized_truncatedConjugate_alexandrov_equation hLip hc hV.measurable
        hK hKc hpush hR hδ hclose hS hSU) (hψ.of_le (by simp)) 0 0 (-c) hε
      (by nlinarith [sq_nonneg ε, hd.2]) hm
  have hh := integral_mul_laplacian_nonneg_of_continuous_upper_tests_on_ball hr hrs
    (continuous_subharmonicNormalizedError htr 0 0 (-c) ε).continuousOn hbound hφ hφc hφs hφ0
  convert hh using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    dsimp only
    by_cases hp : p ∈ tsupport (coordinateLaplacian φ)
    · have hpU : p ∈ ball (0 : Space n) (R / 4) :=
        lt_trans (hφs (tsupport_coordinateLaplacian_subset φ hp)) (show r < R / 4 by linarith)
      rw [subharmonicNegativeDualError_eq_truncated hLip.continuous hc hR hδ hclose hpU]
    · rw [image_eq_zero_of_notMem_tsupport hp, mul_zero, mul_zero]

/-- Original finite-mass weak moment data supply every differentiability and
strict-convexity hypothesis needed for the reciprocal distribution inequality. -/
theorem moment_integral_subharmonicNegativeDualError_mul_laplacian_nonneg (hn : 0 < n)
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V) [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {c r s R M ε : ℝ} (hε : 0 < ε) (hr : 0 < r) (hrs : r < s) (hsR : s < R / 4)
    (hsmall : ε * M ≤ R ^ 2 / 16)
    (hbound : ∀ x ∈ closedBall (0 : Space n) R,
      |normalizedQuadraticError u 0 0 c ε x| ≤ M)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) R,
      |Real.exp (-u x + V (gradient u x)) - 1| ≤ ε ^ 2)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball (0 : Space n) r) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ p, subharmonicNegativeDualError u c ε p * coordinateLaplacian φ p := by
  apply integral_subharmonicNegativeDualError_mul_laplacian_nonneg hn hLip
    (moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush)
    (moment_strictConvexOn hLip hc hV hK.measurableSet hKc hpush) hV hK hKc hpush
    hε hr hrs hsR hsmall _ hdensity hφ hφc hφs hφ0
  intro x hx
  have hb := hbound x hx
  rw [normalizedQuadraticError, abs_div, abs_of_pos hε] at hb
  exact (div_le_iff₀ hε).mp hb |>.trans_eq (mul_comm M ε)

end KLS
end
