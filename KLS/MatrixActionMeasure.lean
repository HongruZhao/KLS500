import KLS.AffineWhitening
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Basic measure properties of the actual finite matrix action. -/

open MeasureTheory Matrix Set

noncomputable section
namespace KLS

lemma det_matrixAction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (matrixAction A).det = A.det := by
  change LinearMap.det A.toEuclideanLin = A.det
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]

theorem absolutelyContinuous_map_matrixAction {n : ℕ} {μ : Measure (Space n)}
    (hμ : μ ≪ volume) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    μ.map (matrixAction A) ≪ volume := by
  have hq := Measure.ContinuousLinearMap.quasiMeasurePreserving volume (matrixAction A)
    (by rwa [det_matrixAction])
  exact (hq.mono_left hμ).absolutelyContinuous

theorem isCompact_support_map_matrixAction {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hμ : IsCompact μ.support) (A : Matrix (Fin n) (Fin n) ℝ) :
    IsCompact (μ.map (matrixAction A)).support := by
  have himg := hμ.image (matrixAction A).continuous
  apply himg.of_isClosed_subset (μ.map (matrixAction A)).isClosed_support
  apply Measure.support_subset_of_isClosed himg.isClosed
  apply (ae_map_iff (matrixAction A).continuous.measurable.aemeasurable himg.measurableSet).mpr
  filter_upwards [μ.support_mem_ae_of_innerRegular] with x hx
  exact mem_image_of_mem _ hx

end KLS
end

#print axioms KLS.absolutelyContinuous_map_matrixAction
#print axioms KLS.isCompact_support_map_matrixAction
