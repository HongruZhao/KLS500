import KLS.UniformGeometricMoments
import KLS.WhitenedFamilyMoments

/-! Actual covariance-normalized centered moments. The quantitative constants
depend only on the order and dimension; no spectral inequality is assumed. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The principal inverse square root of the actual covariance acts on the
actual centered vector. -/
def normalizedCenteredVector (μ : Measure (Space n)) (x : Space n) : Space n :=
  matrixAction (inverseSqrtMatrix (covarianceMatrix μ)) (x - ∫ y, y ∂μ)

lemma normalizedCenteredVector_eq_affine (μ : Measure (Space n)) (x : Space n) :
    normalizedCenteredVector μ x =
      affineMatrixMap (inverseSqrtMatrix (covarianceMatrix μ))
        (-matrixAction (inverseSqrtMatrix (covarianceMatrix μ)) (∫ y, y ∂μ)) x := by
  unfold normalizedCenteredVector
  rw [affineMatrixMap_apply, map_sub]
  rfl

lemma continuous_normalizedCenteredVector (μ : Measure (Space n)) :
    Continuous (normalizedCenteredVector μ) := by
  exact ((matrixAction _).continuous.comp (continuous_id.sub continuous_const))

lemma integral_normalizedCenteredVector_norm_pow (μ : Measure (Space n)) (p : ℕ) :
    (∫ x, ‖normalizedCenteredVector μ x‖ ^ p ∂μ) =
      ∫ x, ‖x‖ ^ p ∂whitenedMeasure μ := by
  rw [whitenedMeasure, affineMatrixMeasure, integral_map (f := fun x : Space n => ‖x‖ ^ p)
    (affineMatrixMap _ _).continuous.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x : Space n => ‖x‖ ^ p) _ from
      (continuous_norm.pow p).aestronglyMeasurable)]
  simp_rw [normalizedCenteredVector_eq_affine]

lemma measureLogConcave.integrable_normalizedCenteredVector_norm_pow
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) (p : ℕ) :
    Integrable (fun x => ‖normalizedCenteredVector μ x‖ ^ p) μ := by
  have h := (hμ.whitenedMeasure.integrable_norm_pow p).comp_aemeasurable
    ((affineMatrixMap (inverseSqrtMatrix (covarianceMatrix μ))
      (-matrixAction (inverseSqrtMatrix (covarianceMatrix μ)) (∫ y, y ∂μ))).continuous.measurable.aemeasurable)
  simpa only [Function.comp_def, normalizedCenteredVector_eq_affine] using h

/-- A uniform finite-order estimate for the genuine normalized centered vector,
derived by the computed affine whitening and its exact isotropy. -/
theorem measureLogConcave.integral_normalizedCenteredVector_norm_pow_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ)
    (hpos : (covarianceMatrix μ).PosDef) (p : ℕ) :
    (∫ x, ‖normalizedCenteredVector μ x‖ ^ p ∂μ) ≤
      isotropicTailRadius n ^ p * geometricNormMomentConstant p := by
  rw [integral_normalizedCenteredVector_norm_pow]
  exact hμ.whitenedMeasure.isotropic_integral_norm_pow_le
    (whitenedMeasure_isIsotropic hμ.memLp_id hpos) p

/-- Each normalized coordinate product is dominated by the actual norm power.
The estimate permits repetitions and applies at every finite order. -/
theorem measureLogConcave.abs_integral_normalized_coordinate_prod_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ)
    (hpos : (covarianceMatrix μ).PosDef) {p : ℕ} (r : Fin p → Fin n) :
    |∫ x, ∏ i : Fin p, normalizedCenteredVector μ x (r i) ∂μ| ≤
      isotropicTailRadius n ^ p * geometricNormMomentConstant p := by
  have hb (x : Space n) :
      ‖∏ i : Fin p, normalizedCenteredVector μ x (r i)‖ ≤
        ‖normalizedCenteredVector μ x‖ ^ p := by
    calc
      _ = ∏ i : Fin p, ‖normalizedCenteredVector μ x (r i)‖ := norm_prod _ _
      _ ≤ ∏ _i : Fin p, ‖normalizedCenteredVector μ x‖ :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => PiLp.norm_apply_le _ _)
      _ = _ := by simp
  calc
    _ ≤ ∫ x, ‖∏ i : Fin p, normalizedCenteredVector μ x (r i)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖normalizedCenteredVector μ x‖ ^ p ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        (hμ.integrable_normalizedCenteredVector_norm_pow p)
      exact ae_of_all _ hb
    _ ≤ _ := hμ.integral_normalizedCenteredVector_norm_pow_le hpos p

end KLS
end
#print axioms KLS.measureLogConcave.integral_normalizedCenteredVector_norm_pow_le
#print axioms KLS.measureLogConcave.abs_integral_normalized_coordinate_prod_le
