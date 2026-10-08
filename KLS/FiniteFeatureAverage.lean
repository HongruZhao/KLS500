import KLS.FiniteFeatureNumerator

/-! Genuine all-order Fréchet smoothness of normalized finite-feature moments. -/
open MeasureTheory Set
open scoped Topology
noncomputable section
namespace KLS.FiniteFeatureTilt

def featureAverage {n m : ℕ} (μ : Measure (Space n)) (Φ : Space n → Space m)
    (q f : Space n → ℝ) (z : Space m) : ℝ :=
  tiltAverage μ (fun x => q x + inner ℝ z (Φ x)) f

theorem contDiff_featureAverage {n m : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {Φ : Space n → Space m} (hΦ : Continuous Φ)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Integrable f μ) :
    ContDiff ℝ (⊤ : ℕ∞) (featureAverage μ Φ q f) := by
  have hN := contDiff_featureNumerator hμ hΦ hq hf
  have hZ : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => tiltPartition μ (fun x => q x + inner ℝ z (Φ x))) := by
    convert contDiff_featureNumerator hμ hΦ hq (integrable_const (1 : ℝ)) using 1
    funext z
    simp only [featureNumerator, tiltPartition, one_mul]
  have hp (z : Space m) : tiltPartition μ (fun x => q x + inner ℝ z (Φ x)) ≠ 0 :=
    (tiltPartition_pos hμ (by fun_prop)).ne'
  unfold featureAverage
  simp_rw [tiltAverage_eq_ratio]
  convert hN.div hZ hp using 1
  funext z
  rfl

end KLS.FiniteFeatureTilt
end
#print axioms KLS.FiniteFeatureTilt.contDiff_featureAverage
