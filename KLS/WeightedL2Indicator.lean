import KLS.WeightedEnergyGraph
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! A measurable indicator acts as a contraction on the actual weighted L² space. -/
open MeasureTheory InnerProductSpace Set Filter
open scoped RealInnerProductSpace
noncomputable section
namespace KLS
variable {n : ℕ}

private def weightedL2IndicatorFun (φ : Space n → ℝ) {s : Set (Space n)}
    (hs : MeasurableSet s) (f : Lp ℝ 2 (potentialMeasure φ)) : Lp ℝ 2 (potentialMeasure φ) :=
  ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f)

private theorem weightedL2IndicatorFun_coe (φ : Space n → ℝ) {s : Set (Space n)}
    (hs : MeasurableSet s) (f : Lp ℝ 2 (potentialMeasure φ)) :
    weightedL2IndicatorFun φ hs f =ᵐ[potentialMeasure φ] s.indicator f :=
  MemLp.coeFn_toLp _

/-- Multiplication by a measurable indicator is a bounded linear contraction. -/
def weightedL2Indicator (φ : Space n → ℝ) {s : Set (Space n)} (hs : MeasurableSet s) :
    Lp ℝ 2 (potentialMeasure φ) →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  LinearMap.mkContinuous
    { toFun := weightedL2IndicatorFun φ hs
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [weightedL2IndicatorFun_coe φ hs (f + g),
          weightedL2IndicatorFun_coe φ hs f, weightedL2IndicatorFun_coe φ hs g,
          Lp.coeFn_add f g, Lp.coeFn_add (weightedL2IndicatorFun φ hs f)
            (weightedL2IndicatorFun φ hs g)] with x ha hf hg hfg hsfg
        rw [ha, hsfg]
        simp only [Pi.add_apply]
        rw [hf, hg]
        by_cases hx : x ∈ s
        · simp only [Set.indicator_of_mem hx, hfg, Pi.add_apply]
        · simp [hx]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [weightedL2IndicatorFun_coe φ hs (c • f),
          weightedL2IndicatorFun_coe φ hs f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (weightedL2IndicatorFun φ hs f)] with x ha hf hcf hscf
        simp only [RingHom.id_apply]
        rw [ha, hscf]
        simp only [Pi.smul_apply]
        rw [hf]
        by_cases hx : x ∈ s
        · simp only [Set.indicator_of_mem hx, hcf, Pi.smul_apply]
        · simp [hx] }
    1 (by
      intro f
      simp only [one_mul]
      change ‖weightedL2IndicatorFun φ hs f‖ ≤ ‖f‖
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [weightedL2IndicatorFun_coe φ hs f] with x hx
      rw [hx]
      by_cases hx : x ∈ s <;> simp [hx])

theorem weightedL2Indicator_coe (φ : Space n → ℝ) {s : Set (Space n)}
    (hs : MeasurableSet s) (f : Lp ℝ 2 (potentialMeasure φ)) :
    weightedL2Indicator φ hs f =ᵐ[potentialMeasure φ] s.indicator f :=
  weightedL2IndicatorFun_coe φ hs f

/-- Its squared norm is exactly the actual exterior or local L² integral. -/
theorem weightedL2Indicator_norm_sq (φ : Space n → ℝ) {s : Set (Space n)}
    (hs : MeasurableSet s) (f : Lp ℝ 2 (potentialMeasure φ)) :
    ‖weightedL2Indicator φ hs f‖ ^ 2 = ∫ x in s, f x ^ 2 ∂potentialMeasure φ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [weightedL2Indicator_coe φ hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs, pow_two]

theorem weightedL2Indicator_norm_le (φ : Space n → ℝ) {s : Set (Space n)}
    (hs : MeasurableSet s) (f : Lp ℝ 2 (potentialMeasure φ)) :
    ‖weightedL2Indicator φ hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [weightedL2Indicator_coe φ hs f] with x hx
  rw [hx]
  by_cases hx : x ∈ s <;> simp [hx]

end KLS
end
#print axioms KLS.weightedL2Indicator
#print axioms KLS.weightedL2Indicator_norm_sq
