import KLS.AffinePotentialCutoff
import KLS.GaussianSmoothApproximation

/-!
# Reduction to smooth densities on bounded open convex targets

The original class is first approximated by its actual isotropic compact
cutoffs, then by normalized Gaussian smoothing, and finally by a second
conditioning and covariance whitening. The last laws have smooth convex
potentials on the whole space restricted to bounded open ellipsoids. Exact
second and fourth moment limits pass the quadratic variance bound through
these three operations.
-/

open MeasureTheory ProbabilityTheory Set Filter Metric Matrix
open scoped ENNReal ContDiff Topology

noncomputable section
namespace KLS

/-- A finite globally smooth convex potential, restricted to a bounded open
convex set. Probability and isotropy remain separate genuine conditions. -/
def HasSmoothBoundedConvexDensity {n : ℕ} (μ : Measure (Space n)) : Prop :=
  ∃ (K : Set (Space n)) (V : Space n → ℝ),
    IsOpen K ∧ Convex ℝ K ∧ Bornology.IsBounded K ∧ K.Nonempty ∧
    ContDiff ℝ (⊤ : ℕ∞) V ∧ ConvexOn ℝ univ V ∧
    μ = (potentialMeasure V).restrict K

lemma hasSmoothBoundedConvexDensity_affine_cond {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hc : ConvexOn ℝ univ V) (heq : μ = potentialMeasure V)
    {r : ℝ} (hr : 0 < r) (hm : μ (closedBall (0 : Space n) r) ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0) :
    HasSmoothBoundedConvexDensity
      (affineMatrixMeasure (ProbabilityTheory.cond μ (closedBall (0 : Space n) r)) A b) := by
  let e := affineMatrixEquiv A b hA
  let W := fun x => V x + Real.log (μ.real (closedBall (0 : Space n) r))
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := hV.add contDiff_const
  have hcW : ConvexOn ℝ univ W := by
    convert hc.add_const (Real.log (μ.real (closedBall (0 : Space n) r))) using 1
  refine ⟨e '' ball 0 r, affineTransformedPotential W A b hA, ?_, ?_, ?_, ?_,
    affineTransformedPotential_contDiff hW A b hA,
    affineTransformedPotential_convex hcW A b hA, ?_⟩
  · exact e.toHomeomorph.isOpenMap _ isOpen_ball
  · exact Convex.affine_image e.toAffineEquiv.toAffineMap (convex_ball 0 r)
  · exact ((isCompact_closedBall (0 : Space n) r).image e.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  · exact (nonempty_ball.mpr hr).image e
  · change (ProbabilityTheory.cond μ (closedBall (0 : Space n) r)).map e = _
    rw [cond_closedBall_potentialMeasure hV.continuous.measurable heq hr.ne' hm]
    rw [map_restrict_affineMatrixEquiv, map_potentialMeasure_affineMatrixEquiv hW.continuous.measurable]

lemma inverseSqrtMatrix_det_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : (inverseSqrtMatrix A).det ≠ 0 := by
  intro hz
  have hh := congrArg Matrix.det (inverseSqrtMatrix_mul_self_mul_transpose hA)
  simp only [Matrix.det_mul, hz, zero_mul, Matrix.det_one] at hh
  exact zero_ne_one hh

/-- Every sufficiently large second cutoff has the explicit regular target
representation, including the affine Jacobian and normalization constant. -/
theorem admissibleMeasure.eventually_smoothBoundedDensity_whitenedBallCutoff
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hc : ConvexOn ℝ univ V) (heq : μ = potentialMeasure V)
    {R : ℝ} (hR : 0 < R) (hm : μ (closedBall (0 : Space n) R) ≠ 0) :
    ∀ᶠ k in atTop, HasSmoothBoundedConvexDensity (whitenedBallCutoffMeasure μ R k) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  filter_upwards [hμ.eventually_posDef_covarianceMatrix_ballCutoffMeasure hm] with k hk
  let Q := inverseSqrtMatrix (covarianceMatrix (ballCutoffMeasure μ R k))
  let b := -matrixAction Q (∫ x, x ∂ballCutoffMeasure μ R k)
  change HasSmoothBoundedConvexDensity (affineMatrixMeasure
    (ProbabilityTheory.cond μ (closedBall (0 : Space n) (R + k))) Q b)
  exact hasSmoothBoundedConvexDensity_affine_cond hV hc heq
    (by positivity) (cutoffMass_ne_zero hm k) Q b (inverseSqrtMatrix_det_ne_zero hk)

/-- The second cutoff and whitening reduce a globally smooth convex density
to the exact regular bounded target class. -/
theorem admissibleMeasure.quadraticVarianceEight_of_smoothBoundedDensity_of_smooth
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hc : ConvexOn ℝ univ V) (heq : μ = potentialMeasure V)
    (hregular : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothBoundedConvexDensity ν → QuadraticVarianceEight ν) :
    QuadraticVarianceEight μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨R, hR, hm, ha⟩ := hμ.exists_whitened_compact_cutoffs
  intro M hM
  refine ⟨hμ.logConcave.memLp_two_matrixQuadratic M, ?_⟩
  apply le_of_tendsto (hμ.tendsto_quadraticVariance_whitenedBallCutoffMeasure hm M)
  filter_upwards [ha, hμ.eventually_smoothBoundedDensity_whitenedBallCutoff hV hc heq hR hm]
    with k hak hrk
  exact (hregular _ hak.1 hrk M hM).2

/-- Full original compact-set log-concave isotropic class reduction. The only
remaining hypothesis is the desired inequality on the explicit regular
bounded target class; no moment-map existence or Hessian bound is assumed
for Gaussian convolution laws. -/
theorem admissibleMeasure.quadraticVarianceEight_of_smoothBoundedDensity
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hregular : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothBoundedConvexDensity ν → QuadraticVarianceEight ν) :
    QuadraticVarianceEight μ := by
  apply hμ.quadraticVarianceEight_of_isotropicGaussianFamily
  intro ν hν hc k
  let : IsProbabilityMeasure ν := hν.isProb
  have hr := (cutoffScale_pos k).ne'
  apply (hν.isotropicGaussianSmoothing hr).quadraticVarianceEight_of_smoothBoundedDensity_of_smooth
    (isotropicGaussianPotential_contDiff hc hr)
    (hν.isotropicGaussianPotential_convex hc hr)
    (hν.isotropicGaussianSmoothing_eq_exp_potential hc hr) hregular

end KLS
end

#print axioms KLS.hasSmoothBoundedConvexDensity_affine_cond
#print axioms KLS.admissibleMeasure.eventually_smoothBoundedDensity_whitenedBallCutoff
#print axioms KLS.admissibleMeasure.quadraticVarianceEight_of_smoothBoundedDensity
