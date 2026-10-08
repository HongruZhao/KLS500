import KLS.WeightedIterationTaylorSums
import SpectralReductionIndividualLemma38
import WeightedFiniteTaylorWindow
import KLS.FiniteTaylorRecurrence

/-! Actual BKL (63): the genuine Taylor sums obey the doubling recurrence.
All early indices and all defect-window multiplicities are discharged here. -/
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

theorem weightedIteration_taylor_sum_recurrence_rankIndividualYoung
    {lam M ε : ℝ} (hε : 0 < ε) {β : ℕ → ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    (hβ : WeightedCoordinateTaylorCoefficientBound φ β) (hβ0 : ∀ d, 0 ≤ β d)
    (hE0 : weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U 0 = lam)
    (hCs : Summable (weightedIterationDefect hφ hκ hlower U W))
    (hCb : (∑' k, weightedIterationDefect hφ hκ hlower U W k) ≤ lam ^ 2)
    (N : ℕ)
    (hscale : ∀ j, j + 1 < N → (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U j)) ^ 2 ≤ M * lam)
    (d : ℕ) (hd : 1 ≤ d) :
    weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower U N d ≤
      youngTaylorMainCoefficient M ε d * lam ^ d *
        weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower U N (2 * d) +
      (((2 * d - 1 : ℕ) : ℝ) + individualTaylorErrorCoefficient ε d *
        ∑ i : Fin (2*d-1), ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)) * lam * β d := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hC : 0 ≤ individualTaylorErrorCoefficient ε d := individualTaylorErrorCoefficient_nonneg hε d
  have hRp : 0 ≤ β d := hβ0 d
  have hsum := finite_taylor_doubling_sum_weighted
    (weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d)
    (weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (2 * d))
    (weightedIterationDefect hφ hκ hlower U W)
    (weightedIterationTaylorEnergy_nonneg (hφ.of_le (by simp)) hκ hlower U (2 * d))
    (weightedIterationDefect_nonneg hφ hκ hlower U W)
    (a := youngTaylorMainCoefficient M ε d * lam ^ d)
    (b := individualTaylorErrorCoefficient ε d * β d / lam)
    (e := lam * β d) (c := lam ^ 2)
    (by unfold youngTaylorMainCoefficient; positivity)
    (div_nonneg (mul_nonneg hC hRp) hlam.le)
    (mul_nonneg hlam.le hRp) N d hd
    (fun i : Fin (2*d-1) => ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)) (fun i => mul_nonneg (by positivity) (pow_nonneg hM0 _))
    (weightedIterationTaylorEnergy_le_initial_coefficient (hφ.of_le (by simp)) hκ hlower U hβ hβ0 hE0 hd)
    (weightedIterationDefect_sum_range_le hκ hlower U hφ W hCs hCb N)
    (fun k hk hkN => weightedIteration_taylor_rankIndividualYoung_before_stop hφ hκ hlower U F W hF hV hL hW
      hε hlam hM hb hβ hβ0 N hscale d k hd hk hkN)
  change weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower U N d ≤
    youngTaylorMainCoefficient M ε d * lam ^ d *
      weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower U N (2 * d) +
    ((2 * d - 1 : ℕ) : ℝ) * (lam * β d) +
    individualTaylorErrorCoefficient ε d * β d / lam *
      (∑ i : Fin (2*d-1), ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)) * lam ^ 2 at hsum
  have he : ((2 * d - 1 : ℕ) : ℝ) * (lam * β d) +
      individualTaylorErrorCoefficient ε d * β d / lam *
        (∑ i : Fin (2*d-1), ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)) * lam ^ 2 =
      (((2 * d - 1 : ℕ) : ℝ) + individualTaylorErrorCoefficient ε d *
        ∑ i : Fin (2*d-1), ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)) * lam * β d := by
    field_simp [ne_of_gt hlam]
  linarith

end KLS.ConstantReduction
end

