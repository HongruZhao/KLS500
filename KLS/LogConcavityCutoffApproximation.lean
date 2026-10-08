import KLS.LogConcavityMoments
import KLS.LogConcavityRestriction
import KLS.ThirdCumulant
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Moments.Covariance

/-!
# Moment-preserving closed-ball cutoffs

This leaf constructs actual normalized restrictions to expanding closed balls.
It proves convergence of all integrable test integrals, hence polynomial norm
moments and isotropic first/second moments. Compact-set log-concavity is
preserved by the already-proved restriction theorem. The cutoffs need not be
isotropic at finite radius, and no smoothing or whitening theorem is asserted.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section
namespace KLS

/-- The actual probability-conditioning operation on an expanding closed ball. -/
def ballCutoffMeasure {n : ℕ} (μ : Measure (Space n)) (R : ℝ) (k : ℕ) :
    Measure (Space n) :=
  ProbabilityTheory.cond μ (closedBall (0 : Space n) (R + k))

theorem monotone_cutoffBalls {n : ℕ} (R : ℝ) :
    Monotone (fun k : ℕ => closedBall (0 : Space n) (R + k)) := by
  intro j k hjk
  apply closedBall_subset_closedBall
  linarith [(Nat.cast_le.mpr hjk : (j : ℝ) ≤ (k : ℝ))]

theorem iUnion_cutoffBalls {n : ℕ} (R : ℝ) :
    (⋃ k : ℕ, closedBall (0 : Space n) (R + k)) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨k, hk⟩ := exists_nat_gt (‖x‖ - R)
  exact mem_iUnion.mpr ⟨k, by simpa only [mem_closedBall, dist_zero_right] using
    (by linarith : ‖x‖ ≤ R + k)⟩

/-- Increasing closed-ball restrictions converge on every integrable test. -/
theorem tendsto_setIntegral_cutoffBalls {n : ℕ} {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : Integrable f μ) (R : ℝ) :
    Tendsto (fun k : ℕ => ∫ x in closedBall (0 : Space n) (R + k), f x ∂μ)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hi : IntegrableOn f (⋃ k : ℕ, closedBall (0 : Space n) (R + k)) μ := by
    simpa only [iUnion_cutoffBalls, integrableOn_univ] using hf
  simpa only [iUnion_cutoffBalls, setIntegral_univ] using
    tendsto_setIntegral_of_monotone (fun _ => measurableSet_closedBall)
      (monotone_cutoffBalls R) hi

/-- Normalizing masses tend to one; no condition on the initial radius is needed. -/
theorem tendsto_cutoffMass {n : ℕ} (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (R : ℝ) : Tendsto (fun k : ℕ => μ.real (closedBall (0 : Space n) (R + k)))
      atTop (𝓝 (1 : ℝ)) := by
  simpa using tendsto_setIntegral_cutoffBalls (integrable_const (1 : ℝ) (μ := μ)) R

/-- Actual normalized restrictions converge on every integrable real test. -/
theorem tendsto_integral_ballCutoffMeasure {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {f : Space n → ℝ} (hf : Integrable f μ) (R : ℝ) :
    Tendsto (fun k => ∫ x, f x ∂ballCutoffMeasure μ R k) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hmass := (tendsto_cutoffMass μ R).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have h := hmass.mul (tendsto_setIntegral_cutoffBalls hf R)
  simpa only [ballCutoffMeasure, ProbabilityTheory.cond, integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul, Measure.real, inv_one, one_mul] using h

theorem cutoffMass_ne_zero {n : ℕ} {μ : Measure (Space n)} {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) (k : ℕ) :
    μ (closedBall (0 : Space n) (R + k)) ≠ 0 := by
  apply ne_of_gt
  exact (pos_iff_ne_zero.mpr hR).trans_le
    (measure_mono (closedBall_subset_closedBall (le_add_of_nonneg_right (Nat.cast_nonneg k))))

theorem isProbabilityMeasure_ballCutoffMeasure {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) (k : ℕ) :
    IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
  cond_isProbabilityMeasure_of_finite (cutoffMass_ne_zero hR k) (measure_ne_top μ _)

/-- Every cutoff retains the exact compact-set definition of log-concavity. -/
theorem measureLogConcave.ballCutoff_logConcave {n : ℕ} {μ : Measure (Space n)}
    (hμ : measureLogConcave μ) (R : ℝ) (k : ℕ) :
    measureLogConcave (ballCutoffMeasure μ R k) :=
  hμ.cond_closed_convex isClosed_closedBall (convex_closedBall _ _)

theorem ballCutoffMeasure_closedBall_mem_ae {n : ℕ} (μ : Measure (Space n))
    (R : ℝ) (k : ℕ) :
    ∀ᵐ x ∂ballCutoffMeasure μ R k, x ∈ closedBall (0 : Space n) (R + k) := by
  rw [ae_iff]
  change ProbabilityTheory.cond μ (closedBall (0 : Space n) (R + k))
    (closedBall (0 : Space n) (R + k))ᶜ = 0
  rw [cond_apply measurableSet_closedBall]
  simp

theorem isCompact_support_ballCutoffMeasure {n : ℕ} (μ : Measure (Space n))
    (R : ℝ) (k : ℕ) : IsCompact (ballCutoffMeasure μ R k).support :=
  (isCompact_closedBall (0 : Space n) (R + k)).of_isClosed_subset
    (ballCutoffMeasure μ R k).isClosed_support (Measure.support_subset_of_isClosed isClosed_closedBall
      (ballCutoffMeasure_closedBall_mem_ae μ R k))

/-- The norm-moment truncation error is controlled by any higher norm moment. -/
theorem norm_pow_tail_le_higher_moment {n : ℕ} {μ : Measure (Space n)}
    {p q : ℕ} (hp : Integrable (fun x : Space n => ‖x‖ ^ p) μ)
    (hpq : Integrable (fun x : Space n => ‖x‖ ^ (p + q)) μ)
    {R : ℝ} (hR : 0 < R) :
    (∫ x in {x : Space n | R < ‖x‖}, ‖x‖ ^ p ∂μ) ≤
      (∫ x, ‖x‖ ^ (p + q) ∂μ) / R ^ q := by
  apply (le_div_iff₀ (pow_pos hR q)).mpr
  rw [← integral_mul_const]
  calc
    (∫ x in {x : Space n | R < ‖x‖}, ‖x‖ ^ p * R ^ q ∂μ) ≤
        ∫ x in {x : Space n | R < ‖x‖}, ‖x‖ ^ (p + q) ∂μ := by
      apply integral_mono_ae (hp.restrict.mul_const _) hpq.restrict
      filter_upwards [ae_restrict_mem (by measurability :
        MeasurableSet {x : Space n | R < ‖x‖})] with x hx
      rw [pow_add]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hx.le q) (by positivity)
    _ ≤ ∫ x, ‖x‖ ^ (p + q) ∂μ :=
      setIntegral_le_integral hpq (Eventually.of_forall fun x => by positivity)

/-- The fourth moment removed beyond radius R is at most the eighth moment
 divided by R^4. All moments are proved for the full compact-set class. -/
theorem measureLogConcave.fourthMoment_tail_le {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) {R : ℝ} (hR : 0 < R) :
    (∫ x in {x : Space n | R < ‖x‖}, ‖x‖ ^ 4 ∂μ) ≤
      (∫ x, ‖x‖ ^ 8 ∂μ) / R ^ 4 := by
  exact norm_pow_tail_le_higher_moment (p := 4) (q := 4) (hμ.integrable_norm_pow 4)
    (hμ.integrable_norm_pow 8) hR

/-- Every polynomial norm moment converges under the actual cutoff family. -/
theorem measureLogConcave.tendsto_norm_moment_ballCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) (R : ℝ) (p : ℕ) :
    Tendsto (fun k => ∫ x : Space n, ‖x‖ ^ p ∂ballCutoffMeasure μ R k)
      atTop (𝓝 (∫ x : Space n, ‖x‖ ^ p ∂μ)) :=
  tendsto_integral_ballCutoffMeasure (hμ.integrable_norm_pow p) R

theorem admissibleMeasure.tendsto_coordinate_ballCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (R : ℝ) (i : Fin n) :
    Tendsto (fun k => ∫ x : Space n, x i ∂ballCutoffMeasure μ R k) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  simpa only [hμ.isotropic.integral_coordinate] using
    tendsto_integral_ballCutoffMeasure (hμ.isotropic.integrable_coordinate i) R

theorem admissibleMeasure.tendsto_secondMoment_ballCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (R : ℝ) (i j : Fin n) :
    Tendsto (fun k => ∫ x : Space n, x i * x j ∂ballCutoffMeasure μ R k)
      atTop (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have h := tendsto_integral_ballCutoffMeasure (hμ.isotropic.2.2.1 i j) R
  have heq : (∫ x : Space n, x i * x j ∂μ) = (1 : Matrix (Fin n) (Fin n) ℝ) i j :=
    congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hμ.isotropic.2.2.2
  rwa [heq] at h


/-- Restriction and finite renormalization preserve Lp integrability. -/
theorem memLp_ballCutoffMeasure {n : ℕ} {μ : Measure (Space n)}
    {f : Space n → ℝ} {p : ℝ≥0∞} (hf : MemLp f p μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) (k : ℕ) :
    MemLp f p (ballCutoffMeasure μ R k) :=
  (hf.restrict _).smul_measure (ENNReal.inv_ne_top.mpr (cutoffMass_ne_zero hR k))

/-- The actual covariances of the cutoffs converge to the identity. At finite
radius these covariance matrices are not asserted to be exactly the identity. -/
theorem admissibleMeasure.tendsto_covariance_ballCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) (i j : Fin n) :
    Tendsto (fun k => ProbabilityTheory.covariance (fun x : Space n => x i)
      (fun x : Space n => x j) (ballCutoffMeasure μ R k))
      atTop (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have heq (k : ℕ) :
      ProbabilityTheory.covariance (fun x : Space n => x i) (fun x : Space n => x j)
          (ballCutoffMeasure μ R k) =
        (∫ x : Space n, x i * x j ∂ballCutoffMeasure μ R k) -
          (∫ x : Space n, x i ∂ballCutoffMeasure μ R k) *
            (∫ x : Space n, x j ∂ballCutoffMeasure μ R k) := by
    let : IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
      isProbabilityMeasure_ballCutoffMeasure hR k
    exact ProbabilityTheory.covariance_eq_sub
      (memLp_ballCutoffMeasure (hμ.isotropic.memLp_coordinate i) hR k)
      (memLp_ballCutoffMeasure (hμ.isotropic.memLp_coordinate j) hR k)
  have h := (hμ.tendsto_secondMoment_ballCutoffMeasure R i j).sub
    ((hμ.tendsto_coordinate_ballCutoffMeasure R i).mul
      (hμ.tendsto_coordinate_ballCutoffMeasure R j))
  simpa only [heq, zero_mul, sub_zero] using h

/-- Every full-class log-concave probability has a concrete family of compactly
supported log-concave probability cutoffs; all integrable moments converge by
`tendsto_integral_ballCutoffMeasure`. No smoothing or whitening is hidden here. -/
theorem measureLogConcave.exists_compact_probability_cutoffs
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) :
    ∃ R : ℝ, 0 < R ∧ μ (closedBall (0 : Space n) R) ≠ 0 ∧
      ∀ k : ℕ, IsProbabilityMeasure (ballCutoffMeasure μ R k) ∧
        measureLogConcave (ballCutoffMeasure μ R k) ∧
        IsCompact (ballCutoffMeasure μ R k).support := by
  obtain ⟨R, hR, hmass⟩ := exists_pos_radius_half_lt_ball μ
  have hnonzero : μ (closedBall (0 : Space n) R) ≠ 0 := by
    intro hz
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hmass
    linarith
  refine ⟨R, hR, hnonzero, fun k => ⟨isProbabilityMeasure_ballCutoffMeasure hnonzero k,
    hμ.ballCutoff_logConcave R k, isCompact_support_ballCutoffMeasure μ R k⟩⟩

/-- Variance convergence follows for every actual square-integrable test,
including unbounded quadratic tests. -/
theorem tendsto_variance_ballCutoffMeasure {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {f : Space n → ℝ} (hf : MemLp f 2 μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) :
    Tendsto (fun k => ProbabilityTheory.variance f (ballCutoffMeasure μ R k))
      atTop (𝓝 (ProbabilityTheory.variance f μ)) := by
  have heq (k : ℕ) : ProbabilityTheory.variance f (ballCutoffMeasure μ R k) =
      (∫ x, f x ^ 2 ∂ballCutoffMeasure μ R k) -
        (∫ x, f x ∂ballCutoffMeasure μ R k) ^ 2 := by
    let : IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
      isProbabilityMeasure_ballCutoffMeasure hR k
    exact ProbabilityTheory.variance_eq_sub (memLp_ballCutoffMeasure hf hR k)
  have h := (tendsto_integral_ballCutoffMeasure hf.integrable_sq R).sub
    ((tendsto_integral_ballCutoffMeasure (hf.integrable (by norm_num)) R).pow 2)
  simpa only [heq, ProbabilityTheory.variance_eq_sub hf, Pi.pow_apply] using h

/-- All actual matrix quadratic forms are square-integrable in the full
compact-set probability class. This gives integrability, not a variance bound. -/
theorem measureLogConcave.memLp_two_matrixQuadratic
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) (M : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (matrixQuadratic M) 2 μ := by
  unfold matrixQuadratic
  apply memLp_finsetSum Finset.univ
  intro i _
  apply memLp_finsetSum Finset.univ
  intro j _
  simpa only [mul_assoc] using (hμ.memLp_two_coordinate_mul i j).const_mul (M i j)

/-- The exact quadratic variances needed in the approximation step converge.
No uniform quadratic variance bound is inferred from this convergence. -/
theorem measureLogConcave.tendsto_quadraticVariance_ballCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) (M : Matrix (Fin n) (Fin n) ℝ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) :
    Tendsto (fun k => ProbabilityTheory.variance (matrixQuadratic M) (ballCutoffMeasure μ R k))
      atTop (𝓝 (ProbabilityTheory.variance (matrixQuadratic M) μ)) :=
  tendsto_variance_ballCutoffMeasure (hμ.memLp_two_matrixQuadratic M) hR

end KLS
end

#print axioms KLS.tendsto_integral_ballCutoffMeasure
#print axioms KLS.measureLogConcave.fourthMoment_tail_le
#print axioms KLS.admissibleMeasure.tendsto_secondMoment_ballCutoffMeasure

#print axioms KLS.admissibleMeasure.tendsto_covariance_ballCutoffMeasure
#print axioms KLS.measureLogConcave.exists_compact_probability_cutoffs

#print axioms KLS.tendsto_variance_ballCutoffMeasure
#print axioms KLS.measureLogConcave.memLp_two_matrixQuadratic
#print axioms KLS.measureLogConcave.tendsto_quadraticVariance_ballCutoffMeasure
