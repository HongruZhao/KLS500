import SpectralReductionGeneralLemma38
import GeneralScaleSymmetrization
import TwoPointWeightedSymmetrization

/-! The improved coefficient sequence is proved on the actual weighted
iteration, combining exact two-slot and triangular-word Hilbert averaging. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal BigOperators
noncomputable section
namespace KLS.ConstantReduction

def generalSymmetrizationCoefficient (M : ℝ) (m : ℕ) : ℝ :=
  if m = 2 then 1 else ((m : ℝ) - 1) ^ 2 * (m : ℝ) ^ 2 * M ^ (m - 2) / 2

theorem generalSymmetrizationCoefficient_nonneg {M : ℝ} (hM : 0 ≤ M) (m : ℕ) :
    0 ≤ generalSymmetrizationCoefficient M m := by
  unfold generalSymmetrizationCoefficient
  split <;> positivity

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem weightedIteration_symmetrization_bound_generalScale
    (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ) {lam M : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
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
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)) ^ 2 ≤ M * lam) :
    ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
        (weightedSuccessorIterate hφ hκ hlower U (r + q)) -
      weightedIterationSymmetrizedGradient hφ hκ hlower U r q‖ ^ 2 ≤
        generalSymmetrizationCoefficient M (q + 1) / lam *
          ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i) := by
  by_cases hq : q + 1 = 2
  · have hq1 : q = 1 := by omega
    subst q
    simpa [generalSymmetrizationCoefficient] using
      weightedIteration_symmetrization_bound_finTwo hφ hκ hlower hφsmooth hlam hb U F W hF hW r
  · simpa [generalSymmetrizationCoefficient, hq, Nat.cast_add, Nat.cast_one, show q + 1 - 2 = q - 1 by omega] using
      weightedIteration_symmetrization_bound_triangular_generalScale hφ hκ hlower hφsmooth hlam hM hb U F W hF hW r q hscale


end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedIteration_symmetrization_bound_generalScale
