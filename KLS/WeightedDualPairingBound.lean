import KLS.DualTransportRemainder
import KLS.WeightedDualTransportPairing
import KLS.WeightedMomentEnergy

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The primal and actual dual normalized errors have O(epsilon) difference
against each nonnegative compact Lipschitz test. The weighted moment
hypotheses supply the transport identity and the uniform local energy. -/
theorem weighted_primal_dual_pairing_bound (hn : 0 < n)
    {u W V ψ χ : Space n → ℝ} {L C : ℝ≥0} (hLip : LipschitzWith L u)
    (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    (hW : Continuous W) (hV : Continuous V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    (hψ : LipschitzWith C ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    {c ε R r S T M M₀ : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hR : 0 < R)
    (hRr : R ≤ r) (hrS : r < S) (hST : S < T)
    (hsmall : ε * M ≤ R ^ 2 / 16) (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀)
    (hψs : tsupport ψ ⊆ ball (0 : Space n) (R / 4))
    (hχs : tsupport χ ⊆ closedBall (0 : Space n) r)
    (hχone : ∀ x ∈ closedBall (0 : Space n) R, χ x = 1)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) T,
      |Real.exp (-W x + V (gradient u x)) - 1| ≤ ε ^ 2)
    (hbound : ∀ x ∈ closedBall (0 : Space n) T,
      |normalizedQuadraticError u 0 0 c ε x| ≤ M)
    (hψbound : ∀ x, |ψ x| ≤ M₀) :
    |∫ x, (normalizedQuadraticError u 0 0 c ε x - normalizedDualQuadraticError u 0 0 c ε x) * ψ x| ≤
      ε * M * ((C : ℝ) *
        (32 * (M + r ^ 2) ^ 2 * (∫ x, ∑ i, coordinateDerivative χ i x ^ 2) +
          2 * n * r ^ 2 * (∫ x, χ x ^ 2)) + ((C : ℝ) + M₀) * (∫ x, χ x ^ 2)) := by
  have hRT : R ≤ T := by linarith
  have hrT : r ≤ T := by linarith
  have hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ ε * M := by
    intro x hx
    exact abs_sub_quadratic_le_of_normalized_bound hε
      (hbound x (closedBall_subset_closedBall hRT hx))
  have hh := weighted_integral_primal_sub_dual_test_le_transport_difference hLip hu hc hW hV hK hKc hpush
    hR hsmall hε hclose hψ.continuous hψc hψs hψ0
  rw [abs_of_nonneg hh.1]
  apply hh.2.trans
  apply (le_abs_self _).trans
  have hb := abs_integral_weighted_transport_remainder_le hu hc hψ hχ.continuous hχc
    hR hsmall hε (by linarith : ε ≤ 1) hM hM₀ hclose (hψs.trans ball_subset_closedBall)
    hχone (fun x hx => hdensity x (closedBall_subset_closedBall hRT hx))
    (fun x hx => hbound x (closedBall_subset_closedBall hRT hx)) hψbound
  rw [integral_cutoff_norm_gradient_sq_eq_coordinate_energy] at hb
  have he := weighted_normalizedQuadraticError_caccioppoli hn hLip hu hc.convexOn hW hV hK hKc hpush hχ hχc
    0 0 c hε hεhalf (by linarith : 0 < S) hrS hST hχs hdensity hM
    (fun x hx => hbound x (closedBall_subset_closedBall hrT (hχs hx)))
  exact hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left he C.coe_nonneg) (le_refl _))
      (mul_nonneg hε.le hM))

end KLS
end
