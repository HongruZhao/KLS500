import KLS.WeakMomentFirstFactor
import KLS.C11SublevelCutoff

open MeasureTheory Set Filter InnerProductSpace
open scoped ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The auxiliary tail supplies the actual inverse-Hessian energy identity
 under literal weak moment transport. All regularity and compact support
 used for the test are derived; no source C2/C3 assumption is needed. -/
theorem weak_moment_potentialSublevelTail_energy_identity
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hconv : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (x₀ : Space n) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x => c^2*‖deriv (deriv sublevelCutoffProfile) (c*potentialHeight u x₀ x)‖ *
      inverseHessianGradientForm u (potentialHeight u x₀) x) (potentialMeasure u) ∧
    (∫ x, c^2*‖deriv (deriv sublevelCutoffProfile) (c*potentialHeight u x₀ x)‖ *
      inverseHessianGradientForm u (potentialHeight u x₀) x ∂potentialMeasure u) =
      ∫ x, potentialSublevelTail u x₀ c x*hessianMetricDiffusion u V (potentialHeight u x₀) x
        ∂potentialMeasure u := by
  have hu := moment_contDiff_one_closedTarget hLip hconv hV.continuous hK hKc hpush
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hconv hV hVc hκ hstrong hK hKc hpush
  have hGh : LipschitzWith (⟨16/κ,by positivity⟩ : ℝ≥0) (gradient (potentialHeight u x₀)) := by
    rwa [gradient_potentialHeight]
  have htail := potentialSublevelTail_contDiff_one hu x₀ c
  have htailc := potentialSublevelTail_hasCompactSupport hLip.continuous hconv x₀ hc
  have ht := weak_moment_hessianMetricDiffusion_compact_first_factor
    hLip hconv hV hVc hκ hstrong hK hKc hpush hGh htail htailc
  have heq (x : Space n) :
      (∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j *
        coordinateDerivative (potentialSublevelTail u x₀ c) i x *
        coordinateDerivative (potentialHeight u x₀) j x) =
      -(c^2*‖deriv (deriv sublevelCutoffProfile) (c*potentialHeight u x₀ x)‖ *
        inverseHessianGradientForm u (potentialHeight u x₀) x) := by
    simp_rw [coordinateDerivative_potentialSublevelTail_C1 hu]
    unfold inverseHessianGradientForm
    simp only [Finset.mul_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi := ht.2.1
  have hibp := ht.2.2
  simp_rw [heq] at hi
  simp_rw [heq,integral_neg,neg_neg] at hibp
  constructor
  · convert hi.neg using 1
    funext x
    exact (neg_neg _).symm
  · exact hibp.symm

end KLS
end
