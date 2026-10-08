import SpectralReductionRetainedWindow
import KLS.WeightedIterationTaylorSums
import SpectralReductionMovingJumpLemma38
import SpectralReductionJumpWindow
import SpectralReductionCompleteWindow
import KLS.FiniteTaylorRecurrence

/-! The genuine finite Taylor jump recurrence with its actual defect prefix.
The early-index term stays q, and only the defect term uses the reduced budget. -/
open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
  (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
  (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n ι k))
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
  (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))
  (hW : ∀ k j l i, (weightedH1Derivative φ j (W k (l, i)) : Space n → ℝ)
    =ᵐ[potentialMeasure φ] fun x => coordinateHessian (F k i) x j l)

include hF hV hL hW

theorem weightedIteration_taylor_sum_recurrence_rankMovingJumpYoung_retained
    {lam M ε ρ : ℝ} (hε : 0 < ε) {β : ℕ → ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    (hβ : WeightedCoordinateTaylorCoefficientBound φ β) (hβ0 : ∀ d, 0 ≤ β d)
    (hE0 : weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U 0 = lam)
    (N : ℕ)
    (hCb : (∑ k ∈ Finset.range (N-1), weightedIterationDefect hφ hκ hlower U W k) ≤ ρ * lam ^ 2)
    (hscale : ∀ j, j + 1 < N → (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U j)) ^ 2 ≤ M * lam)
    (d k q : ℕ) (hd : 1 ≤ d) (hk : 1≤k) (hq : d+k≤q+1) :
    weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower U N d ≤
      jumpTaylorMainCoefficient M ε d k q * lam ^ k *
        weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower U N (d+k) +
      (((q : ℕ) : ℝ) + ρ * movingJumpTaylorErrorCoefficient ε d k q *
        completeGeometricWindow M q) * lam * β d := by
  unfold completeGeometricWindow
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hC : 0 ≤ movingJumpTaylorErrorCoefficient ε d k q := movingJumpTaylorErrorCoefficient_nonneg hε hd hk hq
  have hRp : 0 ≤ β d := hβ0 d
  have hsum := finite_taylor_jump_sum_weighted_retained
    (weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d)
    (weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (d+k))
    (weightedIterationDefect hφ hκ hlower U W)
    (weightedIterationTaylorEnergy_nonneg (hφ.of_le (by simp)) hκ hlower U (d+k))
    (weightedIterationDefect_nonneg hφ hκ hlower U W)
    (a := jumpTaylorMainCoefficient M ε d k q * lam ^ k)
    (b := movingJumpTaylorErrorCoefficient ε d k q * β d / lam)
    (e := lam * β d) (c := ρ * lam ^ 2)
    (by have hc := jumpRecoverySquared_gt_one hd hk hq; unfold jumpTaylorMainCoefficient; positivity)
    (div_nonneg (mul_nonneg hC hRp) hlam.le)
    (mul_nonneg hlam.le hRp) N d k q hd (by omega)
    (fun i : Fin (q) => completeIntervalWeight q i*M^(i.rev : ℕ)) (fun i => mul_nonneg (completeIntervalWeight_nonneg i) (pow_nonneg hM0 _))
    (weightedIterationTaylorEnergy_le_initial_coefficient (hφ.of_le (by simp)) hκ hlower U hβ hβ0 hE0 hd)
    hCb
    (fun j hj hjN => weightedIteration_taylor_rankMovingJumpYoung_before_stop hφ hκ hlower U F W hF hV hL hW
      hε hlam hM hb hβ hβ0 N hscale d k q j hd hk hq hj hjN)
  change weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower U N d ≤
    jumpTaylorMainCoefficient M ε d k q * lam ^ k *
      weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower U N (d+k) +
    ((q : ℕ) : ℝ) * (lam * β d) +
    movingJumpTaylorErrorCoefficient ε d k q * β d / lam *
      (∑ i : Fin (q), completeIntervalWeight q i*M^(i.rev : ℕ)) * (ρ * lam ^ 2) at hsum
  have he : ((q : ℕ) : ℝ) * (lam * β d) +
      movingJumpTaylorErrorCoefficient ε d k q * β d / lam *
        (∑ i : Fin (q), completeIntervalWeight q i*M^(i.rev : ℕ)) * (ρ * lam ^ 2) =
      (((q : ℕ) : ℝ) + ρ * movingJumpTaylorErrorCoefficient ε d k q *
        ∑ i : Fin (q), completeIntervalWeight q i*M^(i.rev : ℕ)) * lam * β d := by
    field_simp [ne_of_gt hlam]
  linarith

end KLS.ConstantReduction
end


#print axioms KLS.ConstantReduction.weightedIteration_taylor_sum_recurrence_rankMovingJumpYoung_retained
