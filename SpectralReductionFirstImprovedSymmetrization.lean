import SpectralReductionExactLemma38
import TwoPointWeightedSymmetrization

/-! The exact two-slot symmetrizer is combined with the existing polynomial
finite-group estimate. This is a proved actual-iteration bound. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal BigOperators
noncomputable section
namespace KLS.ConstantReduction

def firstImprovedSymmetrizationCoefficient (m : ℕ) : ℝ :=
  if m = 2 then 1 else 4 * (m : ℝ) ^ 4 * 2 ^ m

theorem firstImprovedSymmetrizationCoefficient_nonneg (m : ℕ) :
    0 ≤ firstImprovedSymmetrizationCoefficient m := by
  unfold firstImprovedSymmetrizationCoefficient
  split <;> positivity

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem weightedIteration_symmetrization_bound_polynomial
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
    (hscale : ∀ k, r + 1 ≤ k → k < r + q →
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)) ^ 2 ≤ 2 * lam) :
    ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
        (weightedSuccessorIterate hφ hκ hlower U (r + q)) -
      weightedIterationSymmetrizedGradient hφ hκ hlower U r q‖ ^ 2 ≤
        (4 * (q + 1 : ℝ) ^ 4 * (2 : ℝ) ^ (q + 1)) / lam *
          ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i) := by
  have hsum := weightedIteration_sum_adjacent_defects_le hφ hκ hlower hφsmooth hlam hb U F W hF hW r q hscale
  have hS : 0 ≤ ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i) :=
    Finset.sum_nonneg (fun i _ => weightedIterationDefect_nonneg hφsmooth hκ hlower U W (r + i))
  calc
    _ ≤ 4 * (q + 1 : ℝ) ^ 4 *
        ∑ i : Fin q, weightedIterationSwapDefect hφ hκ hlower U (r + q) i :=
      weightedIteration_symmetrization_le_adjacent_defects hφ hκ hlower U r q
    _ ≤ 4 * (q + 1 : ℝ) ^ 4 * ((2 : ℝ) ^ (q + 1) / lam *
        ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (4 * (q + 1 : ℝ) ^ 4 * (2 : ℝ) ^ (q + 1)) / lam *
        ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i) := by ring

theorem weightedIteration_symmetrization_bound_firstImproved
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
    (hscale : ∀ k, r + 1 ≤ k → k < r + q →
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)) ^ 2 ≤ 2 * lam) :
    ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
        (weightedSuccessorIterate hφ hκ hlower U (r + q)) -
      weightedIterationSymmetrizedGradient hφ hκ hlower U r q‖ ^ 2 ≤
        firstImprovedSymmetrizationCoefficient (q + 1) / lam *
          ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i) := by
  by_cases hq : q + 1 = 2
  · have hq1 : q = 1 := by omega
    subst q
    simpa [firstImprovedSymmetrizationCoefficient] using
      weightedIteration_symmetrization_bound_finTwo hφ hκ hlower hφsmooth hlam hb U F W hF hW r
  · simpa [firstImprovedSymmetrizationCoefficient, hq] using
      weightedIteration_symmetrization_bound_polynomial hφ hκ hlower hφsmooth hlam hb U F W hF hW r q hscale

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedIteration_symmetrization_bound_firstImproved
