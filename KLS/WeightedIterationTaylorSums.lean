import KLS.WeightedIterationTaylorLemma38
import KLS.FiniteTaylorSumBounds

/-! BKL's finite Taylor sums, defined using the actual iteration tensor.
The finite defect bound follows from its already established infinite bound. -/
open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)

def weightedIterationTaylorSum (N d : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N - d), weightedIterationTaylorEnergy hφ hκ hlower U d k

theorem weightedIterationTaylorSum_nonneg (N d : ℕ) :
    0 ≤ weightedIterationTaylorSum hφ hκ hlower U N d :=
  Finset.sum_nonneg (fun k _ => weightedIterationTaylorEnergy_nonneg hφ hκ hlower U d k)

theorem weightedIterationTaylorSum_eq_zero (N d : ℕ) (h : N ≤ d) :
    weightedIterationTaylorSum hφ hκ hlower U N d = 0 := by
  simp [weightedIterationTaylorSum, Nat.sub_eq_zero_of_le h]

theorem weightedIterationTaylorSum_le_initial {lam R : ℝ}
    (hR : WeightedCoordinateTaylorBound φ R)
    (hE0 : weightedIterationEnergy hφ hκ hlower U 0 = lam)
    (N d : ℕ) (hd : 1 ≤ d) :
    weightedIterationTaylorSum hφ hκ hlower U N d ≤
      ((N - d : ℕ) : ℝ) * lam * R ^ (2 * d) := by
  calc
    _ ≤ ∑ _k ∈ Finset.range (N - d), lam * R ^ (2 * d) :=
      Finset.sum_le_sum (fun k _ => weightedIterationTaylorEnergy_le_initial hφ hκ hlower U hR hE0 hd k)
    _ = _ := by simp [mul_assoc]

theorem weightedIterationDefect_sum_range_le
    (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n ι k))
    {lam : ℝ}
    (hCs : Summable (weightedIterationDefect hφsmooth hκ hlower U W))
    (hCb : (∑' k, weightedIterationDefect hφsmooth hκ hlower U W k) ≤ lam ^ 2)
    (N : ℕ) :
    (∑ k ∈ Finset.range N, weightedIterationDefect hφsmooth hκ hlower U W k) ≤ lam ^ 2 := by
  exact (Summable.sum_le_tsum (Finset.range N)
    (fun k _ => weightedIterationDefect_nonneg hφsmooth hκ hlower U W k) hCs).trans hCb

end KLS
end

#print axioms KLS.weightedIterationTaylorSum
#print axioms KLS.weightedIterationTaylorSum_le_initial
#print axioms KLS.weightedIterationDefect_sum_range_le
