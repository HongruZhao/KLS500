import KLS.StrongDensityWeakMomentQuadratic

open MeasureTheory
noncomputable section
namespace KLS

/-- The accepted actual-law approximation transports the proved strong
 target estimate to every admissible measure in every finite dimension.
 Eight is a certified sufficient coefficient; optimality is not asserted. -/
theorem admissibleMeasure.quadraticVarianceEight_unconditional
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    QuadraticVarianceEight μ := by
  apply hμ.quadraticVarianceEight_of_strongDensity
  intro ν hν hreg
  exact hν.quadraticVarianceEight_of_actual_strongDensity hreg

end KLS
end
