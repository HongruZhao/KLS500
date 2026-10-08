import KLS.FullVarianceGradientPoincare
import KLS.BoundedVarianceCheegerBoundary
import KLS.ConditionalEndpoints
import KLS.DensityToClass

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace KLS

/-- The full original admissible class inherits the exact closed Cheeger bound
from one faithful Poincare constant uniform on its smooth strongly convex
subclass. The uniform Poincare input remains an explicit hypothesis. -/
theorem admissibleMeasure.cheeger_lower_bound_of_uniform_strong_poincare
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {C : ℝ≥0} (hC0 : 0 < (C : ℝ))
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → C ∈ poincareConstants ν) :
    ENNReal.ofReal (((32 / 3 : ℝ) * Real.sqrt C)⁻¹) ≤ cheegerConstant μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hK0 : 0 < (16 / 3 : ℝ) * Real.sqrt C :=
    mul_pos (by norm_num) (Real.sqrt_pos.mpr hC0)
  have hbound := hμ.boundedVarianceBound_of_uniform_strong_poincare hC0 hstrong
  have heq : 2 * ((16 / 3 : ℝ) * Real.sqrt C) =
      (32 / 3 : ℝ) * Real.sqrt C := by ring
  simpa only [heq] using boundedVariance_inv_le_cheegerConstant hK0 hbound

/-- A faithful positive Poincare constant chosen before dimension and measure,
uniform on the smooth strongly convex subclass, proves both original Cheeger
targets. This theorem does not establish that uniform analytic input. -/
theorem fullCheegerVerification_of_uniform_strong_poincare
    {C : ℝ≥0} (hC0 : 0 < (C : ℝ))
    (hstrong : ∀ (n : ℕ), 1 ≤ n → ∀ ν : Measure (Space n),
      admissibleMeasure ν → HasSmoothStronglyConvexDensity ν →
        C ∈ poincareConstants ν) : FullCheegerVerification := by
  have hc : 0 < ((32 / 3 : ℝ) * Real.sqrt C)⁻¹ :=
    inv_pos.mpr (mul_pos (by norm_num) (Real.sqrt_pos.mpr hC0))
  refine ⟨_, hc, ?_, ?_⟩
  · intro n hn μ hμ
    exact hμ.cheeger_lower_bound_of_uniform_strong_poincare hC0 (hstrong n hn)
  · intro n hn μ hμ
    exact hμ.admissibleMeasure.cheeger_lower_bound_of_uniform_strong_poincare
      hC0 (hstrong n hn)

/-- The exact original density-based KLS target follows from the same explicitly
uniform smooth-subclass Poincare hypothesis. -/
theorem klsConjecture_of_uniform_strong_poincare
    {C : ℝ≥0} (hC0 : 0 < (C : ℝ))
    (hstrong : ∀ (n : ℕ), 1 ≤ n → ∀ ν : Measure (Space n),
      admissibleMeasure ν → HasSmoothStronglyConvexDensity ν →
        C ∈ poincareConstants ν) : KLSConjecture := by
  obtain ⟨c, hc, _, hfull⟩ :=
    fullCheegerVerification_of_uniform_strong_poincare hC0 hstrong
  exact ⟨c, hc, hfull⟩

/-- Finiteness of the imported universal optimal Poincare constant implies both
full Cheeger targets. The positive finite choice is its toNNReal value plus one;
this is a conditional conversion, not a proof of universal finiteness. -/
theorem fullCheegerVerification_of_universal_poincare_finite
    (hfinite : universalPoincareConstant < ⊤) : FullCheegerVerification := by
  let C : ℝ≥0 := universalPoincareConstant.toNNReal + 1
  have hC0 : 0 < (C : ℝ) := by dsimp [C]; positivity
  apply fullCheegerVerification_of_uniform_strong_poincare hC0
  intro n hn μ hμ _
  have hle := poincareConstant_le_universal hn hμ
  have hne := poincareConstants_nonempty_iff.mpr (hle.trans_lt hfinite)
  apply (poincareConstants_iff_optimal_le hne (hμ.poincareConstant_pos hn)).mpr
  apply hle.trans
  have hadd : universalPoincareConstant.toNNReal ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right zero_le_one
  have hcoe : (universalPoincareConstant.toNNReal : ℝ≥0∞) ≤ (C : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr hadd
  simpa only [ENNReal.coe_toNNReal (ne_of_lt hfinite)] using hcoe

/-- Full Poincare verification supplies the displayed finiteness hypothesis. -/
theorem fullCheegerVerification_of_fullPoincareVerification
    (hP : FullPoincareVerification) : FullCheegerVerification := by
  obtain ⟨_, _, _, hfinite, _⟩ := hP
  exact fullCheegerVerification_of_universal_poincare_finite hfinite

/-- Exact original KLS follows conditionally from full Poincare verification. -/
theorem klsConjecture_of_fullPoincareVerification
    (hP : FullPoincareVerification) : KLSConjecture := by
  obtain ⟨c, hc, _, hfull⟩ := fullCheegerVerification_of_fullPoincareVerification hP
  exact ⟨c, hc, hfull⟩

end KLS
end
