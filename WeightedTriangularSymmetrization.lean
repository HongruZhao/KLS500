import FiniteAverageTriangularBound
import KLS.WeightedIterationSymmetrization

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]

/-- The actual weighted gradient average uses the exact triangular word
length, Hilbert orthogonality, and the original adjacent-defect estimate. -/
theorem weightedIteration_symmetrization_bound_triangular
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ) {lam : ℝ} (hlam : 0 < lam)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
    (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n ι k))
    (hF : ∀ k i, ContDiff ℝ 2 (F k i))
    (hW : ∀ k j l i, (weightedH1Derivative φ j (W k (l, i)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x => coordinateHessian (F k i) x j l)
    (r q : ℕ)
    (hscale : ∀ k, r+1 ≤ k → k < r+q →
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k))^2 ≤
        2*lam) :
    ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r+q))
        (weightedSuccessorIterate hφ hκ hlower U (r+q)) -
      weightedIterationSymmetrizedGradient hφ hκ hlower U r q‖^2 ≤
      ((q : ℝ)^2*(q+1 : ℝ)^2*(2 : ℝ)^(q+1)/8)/lam *
        ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r+i) := by
  have hav := norm_sub_permutationAverage_sq_le_triangular
    (weightedGradientPermutationAction (potentialMeasure φ) n ι r q)
    (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r+q))
      (weightedSuccessorIterate hφ hκ hlower U (r+q)))
  have hsum := weightedIteration_sum_adjacent_defects_le hφ hκ hlower hφsmooth hlam hb
    U F W hF hW r q hscale
  calc
    _ ≤ ((q : ℝ)^2*(q+1 : ℝ)^2/8)*
        ∑ i : Fin q, weightedIterationSwapDefect hφ hκ hlower U (r+q) i := by
      simpa only [weightedIterationSymmetrizedGradient, weightedIterationSwapDefect,
        weightedGradientPermutationAction_adjacent] using hav
    _ ≤ ((q : ℝ)^2*(q+1 : ℝ)^2/8)*((2 : ℝ)^(q+1)/lam *
        ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r+i)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end KLS.ConstantReduction
end
