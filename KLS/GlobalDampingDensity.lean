import KLS.GlobalQuadraticDamping
import KLS.StrongBoundedDensityApproximation

/-! Actual global smooth strongly convex densities after damping and affine whitening. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology ContDiff
noncomputable section
namespace KLS
variable {n : ℕ}

def HasSmoothStronglyConvexDensity (μ : Measure (Space n)) : Prop :=
  ∃ (V : Space n → ℝ) (κ : ℝ), ContDiff ℝ (⊤ : ℕ∞) V ∧
    0 < κ ∧ StrongConvexOn univ κ V ∧ μ = potentialMeasure V

theorem quadraticDamping_eq_potentialMeasure_nonneg
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {V : Space n → ℝ}
    (hV : Measurable V) (heq : μ = potentialMeasure V) {ε : ℝ} (hε : 0 ≤ ε) :
    quadraticDamping μ ε = potentialMeasure (dampedPotential μ V ε) := by
  have hp : 0 < tiltPartition μ (fun y => -ε * ‖y‖ ^ 2) :=
    integral_exp_pos (integrable_exp_quadraticDamping μ hε)
  rw [quadraticDamping, tilted_eq_normalized_density]
  nth_rw 1 [heq]
  rw [potentialMeasure, ← withDensity_mul _ (by fun_prop) (by fun_prop), potentialMeasure]
  congr 1
  funext x
  simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  dsimp [dampedPotential]
  rw [show -(V x + ε * ‖x‖ ^ 2 + Real.log (tiltPartition μ (fun y => -ε * ‖y‖ ^ 2))) =
    -V x + (-ε * ‖x‖ ^ 2) - Real.log (tiltPartition μ (fun y => -ε * ‖y‖ ^ 2)) by ring,
    Real.exp_sub, Real.exp_add, Real.exp_log hp]
  ring

theorem measureLogConcave_quadraticDamping_of_potential
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {V : Space n → ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hc : ConvexOn ℝ univ V)
    (heq : μ = potentialMeasure V) {ε : ℝ} (hε : 0 ≤ ε) :
    measureLogConcave (quadraticDamping μ ε) := by
  rw [quadraticDamping_eq_potentialMeasure_nonneg hV.continuous.measurable heq hε]
  exact measureLogConcave_potentialMeasure (dampedPotential_contDiff hV ε).continuous.measurable
    (convexOn_of_strongConvexOn_nonneg (by positivity) (dampedPotential_strongConvex hc ε))

theorem affine_quadraticDamping_global_strongDensity
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {V : Space n → ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hc : ConvexOn ℝ univ V)
    (heq : μ = potentialMeasure V) {ε : ℝ} (hε : 0 < ε)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0) :
    HasSmoothStronglyConvexDensity (affineMatrixMeasure (quadraticDamping μ ε) A b) := by
  let W := dampedPotential μ V ε
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := dampedPotential_contDiff hV ε
  refine ⟨affineTransformedPotential W A b hA,
    (2 * ε) / (‖matrixAction A‖ + 1) ^ 2,
    affineTransformedPotential_contDiff hW A b hA, by positivity,
    affineTransformedPotential_strongConvex (by positivity) (dampedPotential_strongConvex hc ε)
      A b hA, ?_⟩
  change (quadraticDamping μ ε).map (affineMatrixEquiv A b hA) = _
  rw [quadraticDamping_eq_potentialMeasure_nonneg hV.continuous.measurable heq hε.le,
    map_potentialMeasure_affineMatrixEquiv hW.continuous.measurable]

end KLS
end
