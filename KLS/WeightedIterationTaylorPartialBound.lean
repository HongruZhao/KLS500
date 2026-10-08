import KLS.WeightedIterationTaylorPartial

/-! Squared norm form of the actual repeated partial symmetrization. The
scale estimates in its premise are supplied by the actual stopping index. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS

theorem real_prod_sq_le_pow {a : ℕ → ℝ} {b : ℝ} (k : ℕ)
    (h : ∀ j < k, a j ^ 2 ≤ b) :
    (∏ j ∈ Finset.range k, a j) ^ 2 ≤ b ^ k := by
  rw [← Finset.prod_pow]
  calc
    _ ≤ ∏ _j ∈ Finset.range k, b := Finset.prod_le_prod₀ (fun j _ => sq_nonneg (a j))
      (fun j hj => h j (Finset.mem_range.mp hj))
    _ = _ := by rw [Finset.prod_const, Finset.card_range]

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
theorem weightedIterationBlockTaylor_partial_norm_sq_le (r d q k t m : ℕ)
    (hdk : d + k = t) (h : t + q = m) (hd : d ≠ 0) {lam : ℝ}
    (hscale : ∀ j < k, (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + q + j))) ^ 2 ≤ 2 * lam) :
    ‖finiteIsometryAverage
      (realTensorPrefixAction n (m + 1) (WeightedIterationIndex n ι r) (by omega : t ≤ m + 1))
      (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r d (q + k) m (by omega))‖ ^ 2 ≤
        (2 * lam) ^ k * ‖weightedL2TaylorTensor φ t
          (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + q)))‖ ^ 2 := by
  rw [weightedIterationBlockTaylor_partial hφ hκ hlower U F hF hV hL r d q k t m hdk h hd,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_weightedIterationBlockTaylor]
  exact mul_le_mul_of_nonneg_right (real_prod_sq_le_pow k hscale) (sq_nonneg _)

end KLS
end

#print axioms KLS.real_prod_sq_le_pow
#print axioms KLS.weightedIterationBlockTaylor_partial_norm_sq_le
