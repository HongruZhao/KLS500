import KLS.CovarianceMatrix
import KLS.QuadraticEnergy
import KLS.LogConcavityProjection

/-!
# Actual affine covariance whitening

The affine map and its pushforward measure are constructed from a matrix and
the actual vector mean. The covariance transformation is proved by coordinate
covariances. Positive definiteness gives exact isotropy through the actual
inverse positive square root.
-/

open MeasureTheory ProbabilityTheory Set Filter Matrix Metric
open scoped ENNReal Topology BigOperators

noncomputable section
namespace KLS

def affineMatrixMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) :
    Space n →ᴬ[ℝ] Space n :=
  (matrixAction A).toContinuousAffineMap + ContinuousAffineMap.const ℝ (Space n) b

@[simp] theorem affineMatrixMap_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b x : Space n) : affineMatrixMap A b x = matrixAction A x + b := rfl

def affineMatrixMeasure {n : ℕ} (μ : Measure (Space n))
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) : Measure (Space n) :=
  μ.map (affineMatrixMap A b)

instance isProbabilityMeasure_affineMatrixMeasure {n : ℕ} (μ : Measure (Space n))
    [IsProbabilityMeasure μ] (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) :
    IsProbabilityMeasure (affineMatrixMeasure μ A b) :=
  inferInstanceAs (IsProbabilityMeasure (μ.map (affineMatrixMap A b)))

theorem memLp_id_affineMatrixMeasure {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hμ : MemLp (fun x : Space n => x) 2 μ)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) :
    MemLp (fun x : Space n => x) 2 (affineMatrixMeasure μ A b) := by
  apply (memLp_map_measure_iff aestronglyMeasurable_id
    (affineMatrixMap A b).continuous.measurable.aemeasurable).mpr
  exact ((matrixAction A).comp_memLp' hμ).add (memLp_const b)

theorem integral_id_affineMatrixMeasure {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x : Space n => x) μ)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) :
    (∫ x, x ∂(affineMatrixMeasure μ A b)) = matrixAction A (∫ x, x ∂μ) + b := by
  rw [affineMatrixMeasure, integral_map (affineMatrixMap A b).continuous.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x : Space n => x) _ from aestronglyMeasurable_id)]
  simp only [affineMatrixMap_apply]
  rw [integral_add ((matrixAction A).integrable_comp hμ) (integrable_const b),
    (matrixAction A).integral_comp_comm hμ]
  simp

theorem covarianceMatrix_affineMatrixMeasure {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : MemLp (fun x : Space n => x) 2 μ)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) :
    covarianceMatrix (affineMatrixMeasure μ A b) = A * covarianceMatrix μ * A.transpose := by
  have hc (i : Fin n) : MemLp (fun x : Space n => x i) 2 μ :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hμ
  have hA (i : Fin n) : MemLp (fun x : Space n => ∑ k : Fin n, A i k * x k) 2 μ :=
    memLp_finsetSum _ fun k _ => (hc k).const_mul _
  ext i j
  rw [covarianceMatrix_apply (memLp_id_affineMatrixMeasure hμ A b)]
  rw [affineMatrixMeasure, covariance_map_fun (by fun_prop) (by fun_prop)
    (affineMatrixMap A b).continuous.measurable.aemeasurable]
  simp only [affineMatrixMap_apply, PiLp.add_apply, matrixAction_apply]
  rw [covariance_add_const_left ((hA i).integrable (by norm_num)),
    covariance_add_const_right ((hA j).integrable (by norm_num)),
    covariance_fun_sum_fun_sum (fun k => (hc k).const_mul (A i k))
      (fun l => (hc l).const_mul (A j l))]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    ← covarianceMatrix_apply hμ]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem isIsotropic_of_mean_zero_covariance_one {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : MemLp (fun x : Space n => x) 2 μ)
    (hmean : (∫ x, x ∂μ) = 0) (hcov : covarianceMatrix μ = 1) : IsIsotropic μ := by
  have hc (i : Fin n) : MemLp (fun x : Space n => x i) 2 μ :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hμ
  have hi := hμ.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hci (i : Fin n) : (∫ x, x i ∂μ) = 0 := by
    calc
      (∫ x : Space n, x i ∂μ) = (EuclideanSpace.proj i) (∫ x : Space n, x ∂μ) :=
        (EuclideanSpace.proj i).integral_comp_comm hi
      _ = 0 := by rw [hmean]; simp
  refine ⟨hi, hmean, fun i j => (hc i).integrable_mul (hc j), ?_⟩
  ext i j
  have h := congrFun (congrFun hcov i) j
  rw [covarianceMatrix_apply hμ, covariance_eq_sub (hc i) (hc j), hci i, hci j] at h
  simpa only [secondMomentMatrix, zero_mul, sub_zero, Pi.mul_apply] using h

def whitenedMeasure {n : ℕ} (μ : Measure (Space n)) : Measure (Space n) :=
  let Q := inverseSqrtMatrix (covarianceMatrix μ)
  affineMatrixMeasure μ Q (-matrixAction Q (∫ x, x ∂μ))

theorem whitenedMeasure_isIsotropic {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : MemLp (fun x : Space n => x) 2 μ)
    (hpos : (covarianceMatrix μ).PosDef) : IsIsotropic (whitenedMeasure μ) := by
  let Q := inverseSqrtMatrix (covarianceMatrix μ)
  let b := -matrixAction Q (∫ x, x ∂μ)
  change IsIsotropic (affineMatrixMeasure μ Q b)
  apply isIsotropic_of_mean_zero_covariance_one (memLp_id_affineMatrixMeasure hμ Q b)
  · rw [integral_id_affineMatrixMeasure (hμ.integrable (by norm_num))]
    exact add_neg_cancel _
  · rw [covarianceMatrix_affineMatrixMeasure hμ]
    exact inverseSqrtMatrix_mul_self_mul_transpose hpos


instance isProbabilityMeasure_whitenedMeasure {n : ℕ} (μ : Measure (Space n))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (whitenedMeasure μ) := by
  unfold whitenedMeasure
  infer_instance

theorem measureLogConcave.affineMatrixMeasure {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hμ : measureLogConcave μ)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) :
    measureLogConcave (affineMatrixMeasure μ A b) :=
  hμ.map_continuousAffineMap (affineMatrixMap A b)

theorem measureLogConcave.whitenedMeasure {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hμ : measureLogConcave μ) :
    measureLogConcave (whitenedMeasure μ) := hμ.affineMatrixMeasure _ _

theorem isCompact_support_affineMatrixMeasure {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) :
    IsCompact (affineMatrixMeasure μ A b).support := by
  have himg := hμ.image (affineMatrixMap A b).continuous
  apply himg.of_isClosed_subset (affineMatrixMeasure μ A b).isClosed_support
  apply Measure.support_subset_of_isClosed himg.isClosed
  apply (ae_map_iff (affineMatrixMap A b).continuous.measurable.aemeasurable
    himg.measurableSet).mpr
  filter_upwards [μ.support_mem_ae_of_innerRegular] with x hx
  exact mem_image_of_mem _ hx

theorem isCompact_support_whitenedMeasure {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hμ : IsCompact μ.support) :
    IsCompact (whitenedMeasure μ).support :=
  isCompact_support_affineMatrixMeasure hμ _ _

/-- The actual centered and whitened cutoff law. Its covariance matrix is
computed before applying the inverse positive square root. -/
def whitenedBallCutoffMeasure {n : ℕ} (μ : Measure (Space n)) (R : ℝ) (k : ℕ) :
    Measure (Space n) := whitenedMeasure (ballCutoffMeasure μ R k)

/-- All sufficiently large constructed cutoffs are compactly supported,
isotropic, log-concave probability measures in the original compact-set class.
No isotropy or whitening identity is assumed for the cutoff family. -/
theorem admissibleMeasure.eventually_admissible_whitenedBallCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) :
    ∀ᶠ k in atTop, admissibleMeasure (whitenedBallCutoffMeasure μ R k) ∧
      IsCompact (whitenedBallCutoffMeasure μ R k).support := by
  let : IsProbabilityMeasure μ := hμ.isProb
  filter_upwards [hμ.eventually_posDef_covarianceMatrix_ballCutoffMeasure hR] with k hk
  let : IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
    isProbabilityMeasure_ballCutoffMeasure hR k
  refine ⟨⟨inferInstanceAs (IsProbabilityMeasure (whitenedMeasure (ballCutoffMeasure μ R k))), ?_, ?_⟩, ?_⟩
  · exact (hμ.logConcave.ballCutoff_logConcave R k).whitenedMeasure
  · exact whitenedMeasure_isIsotropic (hμ.memLp_id_ballCutoffMeasure hR k) hk
  · exact isCompact_support_whitenedMeasure (isCompact_support_ballCutoffMeasure μ R k)

/-- A nonzero initial ball exists for every admissible measure, and the
resulting actual whitening construction eventually stays in the full class. -/
theorem admissibleMeasure.exists_whitened_compact_cutoffs
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    ∃ R : ℝ, 0 < R ∧ μ (closedBall (0 : Space n) R) ≠ 0 ∧
      ∀ᶠ k in atTop, admissibleMeasure (whitenedBallCutoffMeasure μ R k) ∧
        IsCompact (whitenedBallCutoffMeasure μ R k).support := by
  let : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨R, hR, hm⟩ := exists_pos_radius_half_lt_ball μ
  have hn : μ (closedBall (0 : Space n) R) ≠ 0 := by
    intro hz
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hm
    norm_num at hm
  exact ⟨R, hR, hn, hμ.eventually_admissible_whitenedBallCutoffMeasure hn⟩

end KLS
end

#print axioms KLS.covarianceMatrix_affineMatrixMeasure
#print axioms KLS.whitenedMeasure_isIsotropic

#print axioms KLS.admissibleMeasure.eventually_admissible_whitenedBallCutoffMeasure
#print axioms KLS.admissibleMeasure.exists_whitened_compact_cutoffs
