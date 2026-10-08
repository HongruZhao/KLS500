import GeneralScaleAdjacentDefects
import FiniteAverageTriangularBound
import KLS.WeightedIterationSymmetrization

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem weightedIteration_sum_adjacent_defects_le_generalScale
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
    (∑ i : Fin q, weightedIterationSwapDefect hφ hκ hlower U (r + q) i) ≤
      (4 * M ^ (q - 1)) / lam * ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i) := by
  have hi (i : Fin q) : weightedIterationSwapDefect hφ hκ hlower U (r + q) i ≤
      ((4 * M ^ (q - 1)) / lam) *
        weightedIterationDefect hφsmooth hκ hlower U W (r + i.rev) := by
    have he : r + (i.rev : ℕ) + 1 + (i : ℕ) = r + q := by
      rw [Fin.val_rev]
      omega
    have h := weightedIteration_adjacentSwap_norm_sq_le_generalScale hφ hκ hlower hφsmooth hlam hM hb
      U F W hF hW (r + i.rev) i (fun k hk hk' => hscale k (by omega) (by omega))
    rw [he] at h
    have hp : (4 * M ^ (i : ℕ)) ≤ (4 * M ^ (q - 1)) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (by omega)) (by norm_num)
    have hd := weightedIterationDefect_nonneg hφsmooth hκ hlower U W (r + i.rev)
    calc
      _ ≤ (4 * M ^ (i : ℕ)) *
          weightedIterationDefect hφsmooth hκ hlower U W (r + i.rev) / lam := h
      _ ≤ (4 * M ^ (q - 1)) *
          weightedIterationDefect hφsmooth hκ hlower U W (r + i.rev) / lam :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hd) hlam.le
      _ = _ := by ring
  have hrev : (∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i.rev)) =
      ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i) :=
    Equiv.sum_comp Fin.revPerm (fun i : Fin q => weightedIterationDefect hφsmooth hκ hlower U W (r + i))
  calc
    _ ≤ ∑ i : Fin q, ((4 * M ^ (q - 1)) / lam) *
        weightedIterationDefect hφsmooth hκ hlower U W (r + i.rev) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by rw [← Finset.mul_sum, hrev]


theorem weightedIteration_symmetrization_bound_triangular_generalScale
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
      ((q : ℝ)^2*(q+1 : ℝ)^2*M^(q-1)/2)/lam *
        ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r+i) := by
  have hav := norm_sub_permutationAverage_sq_le_triangular
    (weightedGradientPermutationAction (potentialMeasure φ) n ι r q)
    (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r+q))
      (weightedSuccessorIterate hφ hκ hlower U (r+q)))
  have hsum := weightedIteration_sum_adjacent_defects_le_generalScale hφ hκ hlower hφsmooth hlam hM hb
    U F W hF hW r q hscale
  calc
    _ ≤ ((q : ℝ)^2*(q+1 : ℝ)^2/8)*
        ∑ i : Fin q, weightedIterationSwapDefect hφ hκ hlower U (r+q) i := by
      simpa only [weightedIterationSymmetrizedGradient, weightedIterationSwapDefect,
        weightedGradientPermutationAction_adjacent] using hav
    _ ≤ ((q : ℝ)^2*(q+1 : ℝ)^2/8)*((4*M^(q-1))/lam *
        ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r+i)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end KLS.ConstantReduction
end
