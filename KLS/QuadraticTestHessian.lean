import KLS.MomentQuadraticViscosity
import KLS.WeightedDiffusion

/-! The matrix coefficient of the centered quadratic test is its actual
coordinate Hessian, defined through iterated Fréchet derivatives. -/

open MeasureTheory InnerProductSpace Matrix Set Filter
open scoped Topology ENNReal NNReal ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma contDiff_centeredQuadratic (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ p : Space n) (c : ℝ) : ContDiff ℝ ⊤ (centeredQuadratic A x₀ p c) := by
  have hd : ContDiff ℝ ⊤ (fun x : Space n => x - x₀) := contDiff_id.sub contDiff_const
  exact (contDiff_const.add (contDiff_const.inner ℝ hd)).add
    (contDiff_const.mul (hd.inner ℝ ((matrixAction A).contDiff.comp hd)))

lemma gradient_centeredQuadratic {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ p : Space n) (c : ℝ) (x : Space n) :
    gradient (centeredQuadratic A x₀ p c) x = p + matrixAction A (x - x₀) :=
  (eq_gradient_of_mem_convexSubgradient ((differentiable_centeredQuadratic A x₀ p c) x)
    (centeredQuadratic_slope_mem_subgradient hA x₀ p c x)).symm

lemma coordinateHessian_centeredQuadratic {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ p : Space n) (c : ℝ) (x : Space n) :
    coordinateHessian (centeredQuadratic A x₀ p c) x = A := by
  ext i j
  have heq : coordinateDerivative (centeredQuadratic A x₀ p c) j =
      fun y : Space n => p j + (matrixAction A (y - x₀)) j := by
    funext y
    rw [coordinateDerivative_eq_gradient, gradient_centeredQuadratic hA]
    rfl
  change coordinateDerivative (coordinateDerivative (centeredQuadratic A x₀ p c) j) i x = _
  rw [heq]
  have hd : HasFDerivAt (fun y : Space n => p j + (matrixAction A (y - x₀)) j)
      ((EuclideanSpace.proj (𝕜 := ℝ) j).comp (matrixAction A)) x := by
    convert (((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x
      ((matrixAction A).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀))).const_add (p j)) using 1 <;>
      simp
  rw [coordinateDerivative, hd.fderiv]
  change (matrixAction A (EuclideanSpace.single i 1)) j = A i j
  simp only [matrixAction_apply, PiLp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact hA.isHermitian.isSymm.apply i j

/-- Upper touching expressed with the actual iterated-derivative Hessian. -/
theorem moment_quadratic_upper_test_hessian_det_ge_density
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (x₀ p : Space n)
    (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ centeredQuadratic A x₀ p (u x₀) x) :
    Real.exp (-u x₀ + V (gradient u x₀)) ≤
      (coordinateHessian (centeredQuadratic A x₀ p (u x₀)) x₀).det := by
  rw [coordinateHessian_centeredQuadratic hA.posSemidef]
  exact moment_det_ge_density_of_positive_quadratic_upper_touch hLip hc hV hK hKc hpush hA x₀ p htouch

/-- Lower touching expressed with the same actual iterated-derivative Hessian. -/
theorem moment_quadratic_lower_test_hessian_det_le_density
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (x₀ p : Space n)
    (htouch : ∀ᶠ x in 𝓝 x₀, centeredQuadratic A x₀ p (u x₀) x ≤ u x) :
    (coordinateHessian (centeredQuadratic A x₀ p (u x₀)) x₀).det ≤
      Real.exp (-u x₀ + V (gradient u x₀)) := by
  rw [coordinateHessian_centeredQuadratic hA.posSemidef]
  exact moment_det_le_density_of_positive_quadratic_lower_touch hLip hc hV hK hKc hpush hA x₀ p htouch

end KLS
end

#print axioms KLS.coordinateHessian_centeredQuadratic
#print axioms KLS.moment_quadratic_upper_test_hessian_det_ge_density
#print axioms KLS.moment_quadratic_lower_test_hessian_det_le_density
