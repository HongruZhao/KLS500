import KLS.Definitions

/-!+# Open and closed enlargement comparison

The original Job 45 target uses closed metric neighborhoods. This module
records the inequality needed to transfer an open-neighborhood Cheeger lower
bound to that exact target without changing the constant. It does not assert
that the neighborhoods are equal for arbitrary nonclosed sets.
-/

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

noncomputable section
namespace KLS

def openBoundaryMeasure {n : ℕ} (μ : Measure (Space n))
    (A : Set (Space n)) : ℝ≥0∞ :=
  Filter.liminf
    (fun ε : ℝ => (μ (Metric.thickening ε A) - μ A) / ENNReal.ofReal ε)
    (𝓝[>] (0 : ℝ))

/-- Open outer boundary content is no larger than the closed-neighborhood
content used in the exact imported conjecture. No measure regularity needed. -/
theorem openBoundaryMeasure_le_boundaryMeasure {n : ℕ}
    (μ : Measure (Space n)) (A : Set (Space n)) :
    openBoundaryMeasure μ A ≤ boundaryMeasure μ A := by
  exact Filter.liminf_le_liminf (Eventually.of_forall fun ε =>
    ENNReal.div_le_div_right
      (tsub_le_tsub_right (measure_mono (thickening_subset_cthickening ε A)) _)
      (ENNReal.ofReal ε))

def openCheegerConstant {n : ℕ} (μ : Measure (Space n)) : ℝ≥0∞ :=
  ⨅ A : {A : Set (Space n) // MeasurableSet A ∧ 0 < μ A ∧ μ A < 1},
    openBoundaryMeasure μ A.1 / min (μ A.1) (1 - μ A.1)

theorem openCheegerConstant_le_cheegerConstant {n : ℕ}
    (μ : Measure (Space n)) : openCheegerConstant μ ≤ cheegerConstant μ := by
  apply iInf_mono
  intro A
  exact ENNReal.div_le_div_right (openBoundaryMeasure_le_boundaryMeasure μ A.1) _

theorem le_cheegerConstant_of_le_openCheegerConstant {n : ℕ}
    (μ : Measure (Space n)) {c : ℝ≥0∞}
    (h : c ≤ openCheegerConstant μ) : c ≤ cheegerConstant μ :=
  h.trans (openCheegerConstant_le_cheegerConstant μ)

end KLS
end

#print axioms KLS.openBoundaryMeasure_le_boundaryMeasure
#print axioms KLS.openCheegerConstant_le_cheegerConstant
