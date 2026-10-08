import KLS.WeightedReciprocalEquation
import KLS.NormalizedEnergyBound

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Uniform local energy depends on the density error, with no bound on W itself. -/
theorem weighted_normalizedQuadraticError_caccioppoli (hn : 0 < n)
    {u W V χ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hu : ContDiff ℝ 1 u) (hc : ConvexOn ℝ univ u) (hW : Continuous W) (hV : Continuous V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (x₀ p : Space n) (c : ℝ) {ε r R S M : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hR : 0 < R) (hrR : r < R) (hRS : R < S)
    (hχs : tsupport χ ⊆ closedBall x₀ r)
    (hdensity : ∀ x ∈ closedBall x₀ S, |Real.exp (-W x + V (gradient u x)) - 1| ≤ ε ^ 2)
    (hM : 0 ≤ M) (hbound : ∀ x ∈ tsupport χ, |normalizedQuadraticError u x₀ p c ε x| ≤ M) :
    (∫ x, ∑ i, χ x ^ 2 * coordinateDerivative (normalizedQuadraticError u x₀ p c ε) i x ^ 2) ≤
      32 * (M + r ^ 2) ^ 2 * (∫ x, ∑ i, coordinateDerivative χ i x ^ 2) +
        2 * n * r ^ 2 * (∫ x, χ x ^ 2) :=
  normalizedQuadraticError_caccioppoli hn hu hc
    (Real.continuous_exp.comp (hW.neg.add (hV.comp (continuous_gradient_of_contDiff hu))))
    (fun _S hS => weighted_moment_alexandrov_equation hLip hc hW.measurable hV.measurable
      hK hKc hpush hS) hχ hχc x₀ p c hε hεhalf hR hrR hRS hχs hdensity hM hbound

end KLS
end
