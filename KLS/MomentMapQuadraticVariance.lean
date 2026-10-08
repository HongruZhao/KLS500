import KLS.GradientDualVariance
import KLS.MomentMapSteinBound
import KLS.QuadraticEnergy

/-!
# Quadratic variance reduction through the actual moment-map coupling

The proved Stein energy bound supplies the derivative dual bounds. The
resulting variance estimate still explicitly assumes diffusion-range density
for the actual target potential. It does not identify its matrix contraction
with Letwin's sharper transported contraction or assert the constant eight.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Filter Set
open scoped BigOperators ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma coordinateDerivative_matrixQuadratic (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (i : Fin n) (x : Space n) :
    coordinateDerivative (matrixQuadratic M) i x =
      2 * inner ℝ x (WithLp.toLp 2 (M i)) := by
  rw [coordinateDerivative_eq_gradient, gradient_matrixQuadratic M hM]
  simp only [PiLp.smul_apply, smul_eq_mul, matrixAction_coordinate_eq_inner]

/-- The actual moment-map Stein identity produces the quadratic derivative dual bounds. -/
theorem quadratic_gradient_dual_of_momentMap {φ V : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : Differentiable ℝ φ) (hgrad : ContDiff ℝ 1 (gradient φ))
    (hpush : MomentMap.gradientPushforward φ = potentialMeasure V)
    {B : ℝ} (hB : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ B)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (i : Fin n) :
    CoordinateGradientDualBound V (matrixQuadratic M) i
      (4 * ∫ x, ‖fderiv ℝ (gradient φ) x (WithLp.toLp 2 (M i))‖ ^ 2 ∂potentialMeasure φ) := by
  intro h hh hc
  have hb := MomentMap.integral_linear_test_sq_le_stein_energy hφ hgrad hh hc hB
    (WithLp.toLp 2 (M i))
  rw [hpush] at hb
  have heq : (∫ x, coordinateDerivative (matrixQuadratic M) i x * h x ∂potentialMeasure V) =
      2 * (∫ x, h x * inner ℝ x (WithLp.toLp 2 (M i)) ∂potentialMeasure V) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [coordinateDerivative_matrixQuadratic M hM]
      ring
  rw [heq]
  nlinarith

/-- A conditional quadratic variance bound with an actual gradient-derivative integral.
This is not the full quadratic estimate eight; moment-map representation, target
range density, and the sharper transported matrix estimate remain separate. -/
theorem quadratic_variance_le_momentMap_energy {φ V : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] [IsProbabilityMeasure (potentialMeasure V)]
    (hφ : Differentiable ℝ φ) (hgrad : ContDiff ℝ 1 (gradient φ))
    (hV : ContDiff ℝ 2 V) (hconv : ConvexOn ℝ univ V)
    (hpush : MomentMap.gradientPushforward φ = potentialMeasure V)
    {B : ℝ} (hB : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ B)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (hq : MemLp (matrixQuadratic M) 2 (potentialMeasure V))
    (hdense : DiffusionRangeDense V) :
    ProbabilityTheory.variance (matrixQuadratic M) (potentialMeasure V) ≤
      4 * ∑ i : Fin n,
        ∫ x, ‖fderiv ℝ (gradient φ) x (WithLp.toLp 2 (M i))‖ ^ 2 ∂potentialMeasure φ := by
  rw [Finset.mul_sum]
  exact variance_le_sum_gradient_dual_of_rangeDense hV hconv
    ((contDiff_matrixQuadratic M).of_le (by simp)) hq
    (fun i => mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
    (quadratic_gradient_dual_of_momentMap hφ hgrad hpush hB M hM) hdense

end KLS
end

#print axioms KLS.quadratic_gradient_dual_of_momentMap
#print axioms KLS.quadratic_variance_le_momentMap_energy
