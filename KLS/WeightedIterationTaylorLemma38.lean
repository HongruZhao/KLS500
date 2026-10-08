import KLS.WeightedIterationTaylorDoubling
import KLS.TaylorDoublingConstants
import KLS.WeightedIterationTaylorEnergy

/-! Full actual BKL Lemma 3.8, with one universal constant and the usual
iteration-level interval. The same actual U, F, W and lambda are retained. -/

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

/-- Universal-constant version in forward interval coordinates. -/
theorem weightedIteration_taylor_doubling_universal
    {lam R : ℝ} (hlam : 0 < lam)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    (hR : WeightedCoordinateTaylorBound φ R)
    (r d s : ℕ) (hd : 1 ≤ d) (hs : s + 1 = d)
    (hscale : ∀ k, r ≤ k → k < r + (s + d) →
      (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) ^ 2 ≤ 2 * lam) :
    weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d (r + (s + d)) ≤
      (bklTaylorDoublingConstant * lam) ^ d *
        weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (2 * d) (r + s) +
      bklTaylorDoublingConstant ^ d * R ^ (2 * d) / lam *
        ∑ i : Fin (s + d), weightedIterationDefect hφ hκ hlower U W (r + i) := by
  have he := weightedIteration_taylor_doubling_explicit hφ hκ hlower U F W hF hV hL hW
    hlam hb hR r d s hd hs hscale
  have hmain := taylorDoubling_main_coefficient hd hlam.le
  have herr := taylorDoubling_error_coefficient hd
  have hRpow : 0 ≤ R ^ (2 * d) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg R) d
  have hS : 0 ≤ ∑ i : Fin (s + d), weightedIterationDefect hφ hκ hlower U W (r + i) :=
    Finset.sum_nonneg (fun i _ => weightedIterationDefect_nonneg hφ hκ hlower U W (r + i))
  exact he.trans (add_le_add
    (mul_le_mul_of_nonneg_right hmain (weightedIterationTaylorEnergy_nonneg (hφ.of_le (by simp)) hκ hlower U (2 * d) (r + s)))
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right herr hRpow) hlam.le) hS))

/-- Actual BKL (55). Here k is paper index i−1, so the hypothesis is 2d≤i,
and the defect interval is precisely paper j=i−2d+1,...,i−1. -/
theorem weightedIteration_taylor_lemma38
    {lam R : ℝ} (hlam : 0 < lam)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    (hR : WeightedCoordinateTaylorBound φ R)
    (d k : ℕ) (hd : 1 ≤ d) (hk : 2 * d ≤ k + 1)
    (hscale : ∀ j < k, (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U j)) ^ 2 ≤ 2 * lam) :
    weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d k ≤
      (bklTaylorDoublingConstant * lam) ^ d *
        weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (2 * d) (k - d) +
      bklTaylorDoublingConstant ^ d * R ^ (2 * d) / lam *
        ∑ i : Fin (2 * d - 1), weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + i) := by
  have hq : d - 1 + d = 2 * d - 1 := by omega
  have hcur : k - (2 * d - 1) + (d - 1 + d) = k := by omega
  have hprev : k - (2 * d - 1) + (d - 1) = k - d := by omega
  have he := weightedIteration_taylor_doubling_universal hφ hκ hlower U F W hF hV hL hW
    hlam hb hR (k - (2 * d - 1)) d (d - 1) hd (by omega)
      (fun j _ hj => hscale j (by omega))
  rw [hcur, hprev] at he
  have hsum : (∑ i : Fin (d - 1 + d),
      weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + i)) =
      ∑ i : Fin (2 * d - 1), weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + i) := by
    let f : ℕ → ℝ := fun j => weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + j)
    change (∑ i : Fin (d - 1 + d), f i) = ∑ i : Fin (2 * d - 1), f i
    rw [Fin.sum_univ_eq_sum_range f (d - 1 + d), Fin.sum_univ_eq_sum_range f (2 * d - 1), hq]
  rw [hsum] at he
  exact he

/-- Direct stopping-index form: the per-step bounds already proved before N
supply the scale hypotheses, on the identical actual iteration. -/
theorem weightedIteration_taylor_lemma38_before_stop
    {lam R : ℝ} (hlam : 0 < lam)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    (hR : WeightedCoordinateTaylorBound φ R)
    (N : ℕ)
    (hscale : ∀ j, j + 1 < N → (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U j)) ^ 2 ≤ 2 * lam)
    (d k : ℕ) (hd : 1 ≤ d) (hk : 2 * d ≤ k + 1) (hkN : k < N) :
    weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d k ≤
      (bklTaylorDoublingConstant * lam) ^ d *
        weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (2 * d) (k - d) +
      bklTaylorDoublingConstant ^ d * R ^ (2 * d) / lam *
        ∑ i : Fin (2 * d - 1), weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + i) :=
  weightedIteration_taylor_lemma38 hφ hκ hlower U F W hF hV hL hW hlam hb hR d k hd hk
    (fun j hj => hscale j (by omega))

end KLS
end

#print axioms KLS.weightedIteration_taylor_doubling_universal
#print axioms KLS.weightedIteration_taylor_lemma38
#print axioms KLS.weightedIteration_taylor_lemma38_before_stop
