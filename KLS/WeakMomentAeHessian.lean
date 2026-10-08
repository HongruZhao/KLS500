import KLS.WeakMomentPointwiseHessianEquation
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open MeasureTheory Matrix Set Filter InnerProductSpace
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The coordinate Hessian uses the actual iterated derivatives; as a total
 derivative-defined function it is measurable, even before C2 regularity. -/
theorem measurable_coordinateHessian (u : Space n → ℝ) :
    Measurable (coordinateHessian u) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact measurable_fderiv_apply_const ℝ (coordinateDerivative u j) (EuclideanSpace.single i 1)

/-- At every derivative point of a Lipschitz gradient, all actual coordinate
 Hessian entries are bounded by the same Lipschitz constant. -/
theorem norm_coordinateHessian_le_of_gradient_lipschitz
    {u : Space n → ℝ} (hu : Differentiable ℝ u) {G : ℝ≥0}
    (hG : LipschitzWith G (gradient u)) {x : Space n}
    (hg : DifferentiableAt ℝ (gradient u) x) : ‖coordinateHessian u x‖ ≤ G := by
  have hder := hasFDerivAt_gradient_of_differentiableAt_gradient hu hg
  have hnorm : ‖matrixAction (coordinateHessian u x)‖ ≤ G := by
    rw [← hder.fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hG
  apply (Matrix.norm_le_iff G.coe_nonneg).mpr
  intro i j
  have hh := (PiLp.norm_apply_le (matrixAction (coordinateHessian u x) (EuclideanSpace.single j 1)) i).trans
    (((matrixAction (coordinateHessian u x)).le_opNorm (EuclideanSpace.single j 1)).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)))
  simpa [matrixAction_apply,PiLp.single_apply] using hh

/-- Rademacher plus genuine pointwise quadratic tests proves the actual
 Hessian Monge-Ampere equation almost everywhere from weak transport. -/
theorem weak_moment_ae_hessian_equation_of_gradient_lipschitz
    {u V : Space n → ℝ} {L G : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hG : LipschitzWith G (gradient u)) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian u x).PosDef ∧
      (coordinateHessian u x).det = Real.exp (-u x+V (gradient u x)) ∧
      HasFDerivAt (gradient u) (matrixAction (coordinateHessian u x)) x ∧
      ‖coordinateHessian u x‖ ≤ G := by
  have hu := (moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush).differentiable (by norm_num)
  filter_upwards [hG.ae_differentiableAt (μ := volume)] with x hx
  obtain ⟨hpos,heq,hder⟩ := weak_moment_hessian_equation_at_gradient_differentiableAt
    hLip hc hV hK hKc hpush hx
  exact ⟨hpos,heq,hder,norm_coordinateHessian_le_of_gradient_lipschitz hu hG hx⟩

end KLS
end
