import WeightedScaleSymmetrization
import TwoPointWeightedSymmetrization

open MeasureTheory Matrix
open scoped ContDiff BigOperators
noncomputable section
namespace KLS.ConstantReduction

def weightedTriangularSymmetrizationCoefficient (q : ℕ) : ℝ :=
  if q = 1 then 1 else (q : ℝ)^2 * (q + 1 : ℝ)^2 / 2

theorem weightedTriangularSymmetrizationCoefficient_nonneg (q : ℕ) :
    0 ≤ weightedTriangularSymmetrizationCoefficient q := by
  unfold weightedTriangularSymmetrizationCoefficient
  split_ifs <;> positivity

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]

theorem weightedIteration_symmetrization_bound_rankWeightedScale
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
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
    (hscale : ∀ k, r+1 ≤ k → k < r+q →
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k))^2 ≤
        M*lam) :
    ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r+q))
        (weightedSuccessorIterate hφ hκ hlower U (r+q)) -
      weightedIterationSymmetrizedGradient hφ hκ hlower U r q‖^2 ≤
      weightedTriangularSymmetrizationCoefficient q / lam *
        ∑ i : Fin q, M^(i.rev : ℕ)*weightedIterationDefect hφsmooth hκ hlower U W (r+i) := by
  by_cases hq : q = 1
  · subst q
    simpa [weightedTriangularSymmetrizationCoefficient] using
      weightedIteration_symmetrization_bound_finTwo hφ hκ hlower hφsmooth hlam hb U F W hF hW r
  · simpa only [weightedTriangularSymmetrizationCoefficient, ite_eq_right hq] using
      weightedIteration_symmetrization_bound_triangular_weightedScale hφ hκ hlower
        hφsmooth hlam hM hb U F W hF hW r q hscale

end KLS.ConstantReduction
end
