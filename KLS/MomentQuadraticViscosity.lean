import KLS.QuadraticAlexandrovViscosity
import KLS.MomentPrimalC1

/-! Quadratic viscosity inequalities for the original weak moment transport.
The actual density continuity is obtained from the proved C1 endpoint; the
actual mass identity comes directly from the weak transport equation. -/

open MeasureTheory InnerProductSpace Matrix Set Filter
open scoped Topology ENNReal NNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem continuous_real_moment_density_closedTarget
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    Continuous (fun x => Real.exp (-u x + V (gradient u x))) := by
  have hg := continuous_gradient_of_subsingleton_convexSubgradient hLip hc
    (moment_convexSubgradient_subsingleton_closedTarget hLip hc hV hK hKc hpush)
  exact Real.continuous_exp.comp (hLip.continuous.neg.add (hV.comp hg))

lemma subgradient_volume_eq_lintegral_real_moment_density
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Measurable V)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsOpen S) :
    volume (convexSubgradientImage u S) =
      ∫⁻ x in S, ENNReal.ofReal (Real.exp (-u x + V (gradient u x))) ∂volume := by
  rw [← momentMongeAmpereMeasure_apply_eq_subgradientImage_volume_of_isOpen
    hLip hc hV hK hKc hpush hS, momentMongeAmpereMeasure,
    withDensity_apply _ hS.measurableSet]
  rfl

/-- Positive quadratic upper tests of the original weak potential satisfy the
correct Monge--Ampere viscosity inequality, with its actual moment density. -/
theorem moment_det_ge_density_of_positive_quadratic_upper_touch
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (x₀ p : Space n)
    (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ centeredQuadratic A x₀ p (u x₀) x) :
    Real.exp (-u x₀ + V (gradient u x₀)) ≤ A.det := by
  apply det_ge_density_of_positive_quadratic_upper_touch hLip.continuous
    (continuous_real_moment_density_closedTarget hLip hc hV hK hKc hpush).continuousAt
    (fun S hS => subgradient_volume_eq_lintegral_real_moment_density
      hLip hc hV.measurable hK.measurableSet hKc hpush hS) hA rfl htouch

/-- Positive quadratic lower tests of the original weak potential satisfy the
opposite Monge--Ampere viscosity inequality, with the same actual density. -/
theorem moment_det_le_density_of_positive_quadratic_lower_touch
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (x₀ p : Space n)
    (htouch : ∀ᶠ x in 𝓝 x₀, centeredQuadratic A x₀ p (u x₀) x ≤ u x) :
    A.det ≤ Real.exp (-u x₀ + V (gradient u x₀)) := by
  apply det_le_density_of_positive_quadratic_lower_touch hLip.continuous hc
    (continuous_real_moment_density_closedTarget hLip hc hV hK hKc hpush).continuousAt
    (Real.exp_nonneg _) (fun S hS => subgradient_volume_eq_lintegral_real_moment_density
      hLip hc hV.measurable hK.measurableSet hKc hpush hS) hA rfl htouch

end KLS
end

#print axioms KLS.continuous_real_moment_density_closedTarget
#print axioms KLS.moment_det_ge_density_of_positive_quadratic_upper_touch
#print axioms KLS.moment_det_le_density_of_positive_quadratic_lower_touch
