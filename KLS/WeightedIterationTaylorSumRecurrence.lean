import KLS.WeightedIterationTaylorSums
import KLS.FiniteTaylorRecurrence

/-! Actual BKL (63): the genuine Taylor sums obey the doubling recurrence.
All early indices and all defect-window multiplicities are discharged here. -/
open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
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

theorem weightedIteration_taylor_sum_recurrence
    {lam R : ℝ} (hlam : 0 < lam)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    (hR : WeightedCoordinateTaylorBound φ R)
    (hE0 : weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U 0 = lam)
    (hCs : Summable (weightedIterationDefect hφ hκ hlower U W))
    (hCb : (∑' k, weightedIterationDefect hφ hκ hlower U W k) ≤ lam ^ 2)
    (N : ℕ)
    (hscale : ∀ j, j + 1 < N → (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U j)) ^ 2 ≤ 2 * lam)
    (d : ℕ) (hd : 1 ≤ d) :
    weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower U N d ≤
      (bklTaylorDoublingConstant * lam) ^ d *
        weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower U N (2 * d) +
      4 * (d : ℝ) * bklTaylorDoublingConstant ^ d * lam * R ^ (2 * d) := by
  have hC : 0 ≤ bklTaylorDoublingConstant := le_trans (by norm_num) one_le_bklTaylorDoublingConstant
  have hCp : 1 ≤ bklTaylorDoublingConstant ^ d := one_le_pow₀ one_le_bklTaylorDoublingConstant
  have hRp : 0 ≤ R ^ (2 * d) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg R) d
  have hsum := finite_taylor_doubling_sum
    (weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d)
    (weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (2 * d))
    (weightedIterationDefect hφ hκ hlower U W)
    (weightedIterationTaylorEnergy_nonneg (hφ.of_le (by simp)) hκ hlower U (2 * d))
    (weightedIterationDefect_nonneg hφ hκ hlower U W)
    (a := (bklTaylorDoublingConstant * lam) ^ d)
    (b := bklTaylorDoublingConstant ^ d * R ^ (2 * d) / lam)
    (e := lam * R ^ (2 * d)) (c := lam ^ 2)
    (pow_nonneg (mul_nonneg hC hlam.le) d)
    (div_nonneg (mul_nonneg (pow_nonneg hC d) hRp) hlam.le)
    (mul_nonneg hlam.le hRp) N d hd
    (weightedIterationTaylorEnergy_le_initial (hφ.of_le (by simp)) hκ hlower U hR hE0 hd)
    (weightedIterationDefect_sum_range_le hκ hlower U hφ W hCs hCb N)
    (fun k hk hkN => weightedIteration_taylor_lemma38_before_stop hφ hκ hlower U F W hF hV hL hW
      hlam hb hR N hscale d k hd hk hkN)
  have hq : ((2 * d - 1 : ℕ) : ℝ) ≤ 2 * (d : ℝ) := by
    exact_mod_cast (Nat.sub_le (2 * d) 1)
  have hearly : ((2 * d - 1 : ℕ) : ℝ) * (lam * R ^ (2 * d)) ≤
      2 * (d : ℝ) * bklTaylorDoublingConstant ^ d * lam * R ^ (2 * d) := by
    calc
      _ ≤ (2 * (d : ℝ)) * (lam * R ^ (2 * d)) := mul_le_mul_of_nonneg_right hq (by positivity)
      _ ≤ (2 * (d : ℝ)) * bklTaylorDoublingConstant ^ d * (lam * R ^ (2 * d)) := by
        have hh := mul_le_mul_of_nonneg_left hCp (by positivity : 0 ≤ 2 * (d : ℝ))
        exact mul_le_mul_of_nonneg_right (by simpa using hh) (by positivity)
      _ = _ := by ring
  have herr : bklTaylorDoublingConstant ^ d * R ^ (2 * d) / lam *
      ((2 * d - 1 : ℕ) : ℝ) * lam ^ 2 ≤
      2 * (d : ℝ) * bklTaylorDoublingConstant ^ d * lam * R ^ (2 * d) := by
    calc
      _ = ((2 * d - 1 : ℕ) : ℝ) * (bklTaylorDoublingConstant ^ d * lam * R ^ (2 * d)) := by
        field_simp [ne_of_gt hlam]
      _ ≤ (2 * (d : ℝ)) * (bklTaylorDoublingConstant ^ d * lam * R ^ (2 * d)) :=
        mul_le_mul_of_nonneg_right hq (by positivity)
      _ = _ := by ring
  change weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower U N d ≤
    (bklTaylorDoublingConstant * lam) ^ d *
      weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower U N (2 * d) +
    ((2 * d - 1 : ℕ) : ℝ) * (lam * R ^ (2 * d)) +
    bklTaylorDoublingConstant ^ d * R ^ (2 * d) / lam *
      ((2 * d - 1 : ℕ) : ℝ) * lam ^ 2 at hsum
  linarith

end KLS
end

#print axioms KLS.weightedIteration_taylor_sum_recurrence
