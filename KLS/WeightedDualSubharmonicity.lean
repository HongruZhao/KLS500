import KLS.WeightedReciprocalEquation
import KLS.DualSubharmonicDistribution

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual reciprocal subharmonicity for an independent source weight. -/
theorem weighted_integral_subharmonicNegativeDualError_mul_laplacian_nonneg (hn : 0 < n)
    {u W V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u) (hW : Continuous W) (hV : Continuous V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {c r s R δ ε : ℝ} (hε : 0 < ε) (hr : 0 < r) (hrs : r < s) (hsR : s < R / 4)
    (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) R,
      |Real.exp (-W x + V (gradient u x)) - 1| ≤ ε ^ 2)
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
    have hd := weighted_reciprocal_density_log_bound_of_quadratic_closeness hu hc hW hV hR hδ hclose hdensity hxU
    exact subharmonicNormalizedError_upper_test_of_local_log_density hn htr htc hd.1
      (Real.exp_pos _) (isOpen_ball.mem_nhds hxU)
      (fun _S hS hSU => weighted_localized_truncatedConjugate_alexandrov_equation hLip hc hW.measurable hV.measurable
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

end KLS
end
