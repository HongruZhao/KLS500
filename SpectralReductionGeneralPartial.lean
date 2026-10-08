import KLS.WeightedIterationTaylorPartialBound

/-! Squared norm form of the actual repeated partial symmetrization. The
scale estimates in its premise are supplied by the actual stopping index. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
  (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
  (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))

include hF hV hL

/-- BKL (57), allowing any number k of steps and retaining all unused
coordinate positions. Every term is an actual coefficient or iterate. -/
theorem weightedIterationBlockTaylor_partial_norm_sq_le_of_scale (r d q k t m : ℕ)
    (hdk : d + k = t) (h : t + q = m) (hd : d ≠ 0) {B : ℝ}
    (hscale : ∀ j < k, (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + q + j))) ^ 2 ≤ B) :
    ‖finiteIsometryAverage
      (realTensorPrefixAction n (m + 1) (WeightedIterationIndex n ι r) (by omega : t ≤ m + 1))
      (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r d (q + k) m (by omega))‖ ^ 2 ≤
        (B) ^ k * ‖weightedL2TaylorTensor φ t
          (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + q)))‖ ^ 2 := by
  rw [weightedIterationBlockTaylor_partial hφ hκ hlower U F hF hV hL r d q k t m hdk h hd,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_weightedIterationBlockTaylor]
  exact mul_le_mul_of_nonneg_right (real_prod_sq_le_pow k hscale) (sq_nonneg _)

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedIterationBlockTaylor_partial_norm_sq_le_of_scale
