import KLS.QuadraticDamping
import KLS.WhitenedFamilyMoments

/-! Reduction of the full original class to smooth uniformly convex potentials
on bounded open convex targets, by an actual vanishing quadratic tilt followed
by covariance whitening. The quadratic variance convergence is proved. -/

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal Topology ContDiff

noncomputable section
namespace KLS

def HasSmoothBoundedStronglyConvexDensity {n : ℕ} (μ : Measure (Space n)) : Prop :=
  ∃ (K : Set (Space n)) (V : Space n → ℝ) (κ : ℝ),
    IsOpen K ∧ Convex ℝ K ∧ Bornology.IsBounded K ∧ K.Nonempty ∧
    ContDiff ℝ (⊤ : ℕ∞) V ∧ 0 < κ ∧ StrongConvexOn univ κ V ∧
    μ = (potentialMeasure V).restrict K

lemma convexOn_of_strongConvexOn_nonneg {n : ℕ} {V : Space n → ℝ} {κ : ℝ}
    (hκ : 0 ≤ κ) (hV : StrongConvexOn univ κ V) : ConvexOn ℝ univ V := by
  apply UniformConvexOn.convexOn hV
  intro r
  dsimp
  positivity

lemma HasSmoothBoundedStronglyConvexDensity.to_smoothBoundedConvexDensity
    {n : ℕ} {μ : Measure (Space n)} (hμ : HasSmoothBoundedStronglyConvexDensity μ) :
    HasSmoothBoundedConvexDensity μ := by
  obtain ⟨K, V, κ, ho, hc, hb, hn, hd, hκ, hs, he⟩ := hμ
  exact ⟨K, V, ho, hc, hb, hn, hd, convexOn_of_strongConvexOn_nonneg hκ.le hs, he⟩

lemma HasSmoothBoundedConvexDensity.quadraticDamping_logConcave
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : HasSmoothBoundedConvexDensity μ) {ε : ℝ} (hε : 0 ≤ ε) :
    measureLogConcave (quadraticDamping μ ε) := by
  have hs := hμ.isCompact_support
  obtain ⟨K, V, ho, hc, _, _, hd, hv, he⟩ := hμ
  rw [quadraticDamping_eq_restrict_potentialMeasure hs hd.continuous.measurable ho.measurableSet he]
  exact measureLogConcave_restrict_potentialMeasure (dampedPotential_contDiff hd ε).continuous.measurable
    (convexOn_of_strongConvexOn_nonneg (mul_nonneg (by norm_num) hε)
      (dampedPotential_strongConvex hv ε)) ho.measurableSet hc

lemma HasSmoothBoundedConvexDensity.affine_quadraticDamping_strongDensity
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : HasSmoothBoundedConvexDensity μ) {ε : ℝ} (hε : 0 < ε)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0) :
    HasSmoothBoundedStronglyConvexDensity (affineMatrixMeasure (quadraticDamping μ ε) A b) := by
  have hs := hμ.isCompact_support
  obtain ⟨K, V, ho, hc, hb, hn, hd, hv, he⟩ := hμ
  let e := affineMatrixEquiv A b hA
  let W := dampedPotential μ V ε
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := dampedPotential_contDiff hd ε
  refine ⟨e '' K, affineTransformedPotential W A b hA,
    (2 * ε) / (‖matrixAction A‖ + 1) ^ 2, e.toHomeomorph.isOpenMap _ ho,
    Convex.affine_image e.toAffineEquiv.toAffineMap hc, ?_, hn.image e,
    affineTransformedPotential_contDiff hW A b hA, by positivity,
    affineTransformedPotential_strongConvex (by positivity) (dampedPotential_strongConvex hv ε)
      A b hA, ?_⟩
  · exact (hb.isCompact_closure.image e.continuous).isBounded.subset (image_mono subset_closure)
  · change (quadraticDamping μ ε).map e = _
    rw [quadraticDamping_eq_restrict_potentialMeasure hs hd.continuous.measurable ho.measurableSet he,
      map_restrict_affineMatrixEquiv, map_potentialMeasure_affineMatrixEquiv hW.continuous.measurable]

lemma HasSmoothBoundedConvexDensity.whitened_quadraticDamping_strongDensity
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : HasSmoothBoundedConvexDensity μ) {ε : ℝ} (hε : 0 < ε)
    (hpos : (covarianceMatrix (quadraticDamping μ ε)).PosDef) :
    HasSmoothBoundedStronglyConvexDensity (whitenedMeasure (quadraticDamping μ ε)) :=
  hμ.affine_quadraticDamping_strongDensity hε _ _ (inverseSqrtMatrix_det_ne_zero hpos)

/-- Every sufficiently small damped and whitened law belongs to the original
isotropic class and has a smooth bounded strongly convex density. -/
theorem admissibleMeasure.eventually_strongDensity_whitened_quadraticDamping
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hreg : HasSmoothBoundedConvexDensity μ) :
    ∀ᶠ k in atTop,
      admissibleMeasure (whitenedMeasure (quadraticDamping μ (cutoffScale k))) ∧
      HasSmoothBoundedStronglyConvexDensity (whitenedMeasure (quadraticDamping μ (cutoffScale k))) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let ν := fun k => quadraticDamping μ (cutoffScale k)
  let : ∀ k, IsProbabilityMeasure (ν k) :=
    fun k => isProbabilityMeasure_quadraticDamping hreg.isCompact_support _
  have hν : ∀ k, measureLogConcave (ν k) :=
    fun k => hreg.quadraticDamping_logConcave (cutoffScale_pos k).le
  have hlim (f : Space n → ℝ) (hf : Continuous f) :
      Tendsto (fun k => ∫ x, f x ∂ν k) atTop (𝓝 (∫ x, f x ∂μ)) :=
    (tendsto_integral_quadraticDamping hreg.isCompact_support
      (integrable_of_continuous_compact_support_measure hreg.isCompact_support hf)).comp
        cutoffScale_tendsto_zero
  filter_upwards [eventually_admissible_whitenedMeasure_of_continuous_moments hμ hν hlim,
    eventually_posDef_covarianceMatrix_of_continuous_moments hμ hν hlim] with k hak hpk
  exact ⟨hak, hreg.whitened_quadraticDamping_strongDensity (cutoffScale_pos k) hpk⟩

theorem admissibleMeasure.tendsto_quadraticVariance_whitened_quadraticDamping
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hreg : HasSmoothBoundedConvexDensity μ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ProbabilityTheory.variance (matrixQuadratic M)
      (whitenedMeasure (quadraticDamping μ (cutoffScale k))))
      atTop (𝓝 (ProbabilityTheory.variance (matrixQuadratic M) μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let ν := fun k => quadraticDamping μ (cutoffScale k)
  let : ∀ k, IsProbabilityMeasure (ν k) :=
    fun k => isProbabilityMeasure_quadraticDamping hreg.isCompact_support _
  apply tendsto_quadraticVariance_whitenedMeasure_of_continuous_moments hμ
    (ν := ν) (fun k => hreg.quadraticDamping_logConcave (cutoffScale_pos k).le) _ M
  intro f hf
  exact (tendsto_integral_quadraticDamping hreg.isCompact_support
    (integrable_of_continuous_compact_support_measure hreg.isCompact_support hf)).comp
      cutoffScale_tendsto_zero

theorem admissibleMeasure.quadraticVarianceEight_of_strongDensity_of_regular
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hreg : HasSmoothBoundedConvexDensity μ)
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothBoundedStronglyConvexDensity ν → QuadraticVarianceEight ν) :
    QuadraticVarianceEight μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  intro M hM
  refine ⟨hμ.logConcave.memLp_two_matrixQuadratic M, ?_⟩
  apply le_of_tendsto (hμ.tendsto_quadraticVariance_whitened_quadraticDamping hreg M)
  filter_upwards [hμ.eventually_strongDensity_whitened_quadraticDamping hreg] with k hk
  exact (hstrong _ hk.1 hk.2 M hM).2

/-- Full-class reduction through actual laws and moment limits. The remaining
premise is exactly the inequality on regular strongly convex bounded targets;
no source moment-map existence or regularity is smuggled into the construction. -/
theorem admissibleMeasure.quadraticVarianceEight_of_strongDensity
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothBoundedStronglyConvexDensity ν → QuadraticVarianceEight ν) :
    QuadraticVarianceEight μ := by
  apply hμ.quadraticVarianceEight_of_smoothBoundedDensity
  intro ν hν hr
  exact hν.quadraticVarianceEight_of_strongDensity_of_regular hr hstrong

end KLS
end

#print axioms KLS.HasSmoothBoundedConvexDensity.affine_quadraticDamping_strongDensity
#print axioms KLS.admissibleMeasure.eventually_strongDensity_whitened_quadraticDamping
#print axioms KLS.admissibleMeasure.quadraticVarianceEight_of_strongDensity
