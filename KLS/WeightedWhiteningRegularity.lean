import KLS.DetOneQuadraticWhitening

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma strictConvexOn_comp_matrixAction {u : Space n → ℝ}
    (hu : StrictConvexOn ℝ univ u) {B : Matrix (Fin n) (Fin n) ℝ} (hne : B.det ≠ 0) :
    StrictConvexOn ℝ univ (u ∘ matrixAction B) := by
  apply (strictConvexOn_comp_continuousAffineEquiv hu (affineMatrixEquiv B 0 hne)).congr
  intro x _
  simp only [Function.comp_apply, affineMatrixEquiv_zero_apply]

lemma map_potentialMeasure_inverse_matrix_equiv
    {W : Space n → ℝ} (hW : Measurable W)
    (B : Matrix (Fin n) (Fin n) ℝ) (hdet : |B.det| = 1) :
    let e := affineMatrixEquiv B 0 (by intro hz; simp [hz] at hdet)
    (potentialMeasure W).map e.symm = potentialMeasure (W ∘ matrixAction B) := by
  let e := affineMatrixEquiv B 0 (by intro hz; simp [hz] at hdet)
  have hh := map_potentialMeasure_of_volumePreserving e.toHomeomorph.toMeasurableEquiv.symm
    (measurePreserving_symm_of_measurableEquiv e.toHomeomorph.toMeasurableEquiv
      (matrix_equiv_volumePreserving B hdet)) hW
  have hsource : W ∘ e.toHomeomorph.toMeasurableEquiv = W ∘ matrixAction B := by
    funext x
    change W (e x) = W (matrixAction B x)
    exact congrArg W (affineMatrixEquiv_zero_apply B (by intro hz; simp [hz] at hdet) x)
  change (potentialMeasure W).map e.symm = potentialMeasure (W ∘ matrixAction B)
  rw [MeasurableEquiv.symm_symm, hsource] at hh
  convert hh using 1
  congr 1

/-- The complete C1 strictly-convex weighted transport data are preserved by
symmetric volume-preserving matrix normalization. This applies in particular
to the actual inverse square root of the new determinant-one Hessian. -/
theorem weighted_moment_symmetric_whitening_data
    {u W V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    (hW : Continuous W) (hV : Continuous V) [IsFiniteMeasure (potentialMeasure W)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) (hdet : |B.det| = 1) :
    let e := affineMatrixEquiv B 0 (by intro hz; simp [hz] at hdet)
    (∃ D : ℝ≥0, LipschitzWith D (u ∘ matrixAction B)) ∧
      ContDiff ℝ 1 (u ∘ matrixAction B) ∧ StrictConvexOn ℝ univ (u ∘ matrixAction B) ∧
      Continuous (W ∘ matrixAction B) ∧ IsFiniteMeasure (potentialMeasure (W ∘ matrixAction B)) ∧
      Continuous (V ∘ e.symm) ∧ IsClosed (e '' K) ∧ Convex ℝ (e '' K) ∧
      (potentialMeasure (W ∘ matrixAction B)).map (gradient (u ∘ matrixAction B)) =
        (potentialMeasure (V ∘ e.symm)).restrict (e '' K) := by
  dsimp only
  have hne : B.det ≠ 0 := by intro hz; simp [hz] at hdet
  let e := affineMatrixEquiv B 0 hne
  have hfinite : IsFiniteMeasure (potentialMeasure (W ∘ matrixAction B)) := by
    rw [← map_potentialMeasure_inverse_matrix_equiv hW.measurable B hdet]
    infer_instance
  exact ⟨⟨_, hLip.comp (matrixAction B).lipschitzWith⟩, hu.comp (matrixAction B).contDiff,
    strictConvexOn_comp_matrixAction hc hne, hW.comp (matrixAction B).continuous, hfinite,
    hV.comp e.symm.continuous, e.toHomeomorph.isClosedMap _ hK,
    Convex.affine_image e.toAffineEquiv.toAffineMap hKc,
    weighted_moment_transport_symmetric_matrix (hu.differentiable (by norm_num)) hW.measurable hV.measurable
      hpush hB hdet⟩

end KLS
end
