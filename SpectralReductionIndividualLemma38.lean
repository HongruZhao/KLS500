import SpectralReductionOrthogonalDoubling
import SpectralReductionIndividualSymmetrization
import SpectralReductionYoungLemma38
import SpectralReductionGeneralLemma38

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

def individualTaylorErrorCoefficient (ε : ℝ) (d : ℕ) : ℝ :=
  (1 + (1 + ε⁻¹) * ((2*d).choose d : ℝ)^2) * individualSymmetrizationCoefficient (2*d-1)

theorem individualTaylorErrorCoefficient_nonneg {ε : ℝ} (hε : 0 < ε) (d : ℕ) : 0 ≤ individualTaylorErrorCoefficient ε d := by
  exact mul_nonneg (by positivity) (individualSymmetrizationCoefficient_nonneg _)

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

theorem weightedIteration_taylor_doubling_rankIndividualYoung
    {lam M ε : ℝ} (hε : 0 < ε) {β : ℕ → ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    (hβ : WeightedCoordinateTaylorCoefficientBound φ β) (hβ0 : ∀ d, 0 ≤ β d)
    (r d s : ℕ) (hd : 1 ≤ d) (hs : s + 1 = d)
    (hscale : ∀ k, r ≤ k → k < r + (s + d) →
      (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) ^ 2 ≤ M * lam) :
    weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d (r + (s + d)) ≤
      youngTaylorMainCoefficient M ε d * lam ^ d *
        weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (2 * d) (r + s) +
      individualTaylorErrorCoefficient ε d * β d / lam *
        ∑ i : Fin (s + d), ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ) * weightedIterationDefect hφ hκ hlower U W (r + i) := by
  have hg := weightedIteration_symmetrization_bound_rankIndividualScale (hφ.of_le (by simp)) hκ hlower
    hφ hlam hM hb U F W (fun k i => (hF k i).of_le (by simp)) hW r (s+d)
      (fun k hk hk' => hscale k (by omega) hk')
  have he := weightedIteration_taylor_doubling_orthogonalYoung hφ hκ hlower U F W hF hV hL
    hε hβ hβ0 r d s hd hs (fun i : Fin (s+d) => ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)) hscale hg
  convert he using 1 <;>
    simp only [youngTaylorMainCoefficient, individualTaylorErrorCoefficient,
      weightedIterationTaylorEnergy, mul_pow, show 2*d-1 = s+d by omega]
  ring

theorem weightedIteration_taylor_rankIndividualYoung_before_stop
    {lam M ε : ℝ} (hε : 0 < ε) {β : ℕ → ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    (hβ : WeightedCoordinateTaylorCoefficientBound φ β) (hβ0 : ∀ d, 0 ≤ β d)
    (N : ℕ)
    (hscale : ∀ j, j + 1 < N → (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U j)) ^ 2 ≤ M * lam)
    (d k : ℕ) (hd : 1 ≤ d) (hk : 2 * d ≤ k + 1) (hkN : k < N) :
    weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d k ≤
      youngTaylorMainCoefficient M ε d * lam ^ d *
        weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (2 * d) (k - d) +
      individualTaylorErrorCoefficient ε d * β d / lam *
        ∑ i : Fin (2 * d - 1), ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ) *
          weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + i) := by
  have hq : d - 1 + d = 2 * d - 1 := by omega
  have hcur : k - (2 * d - 1) + (d - 1 + d) = k := by omega
  have hprev : k - (2 * d - 1) + (d - 1) = k - d := by omega
  have he := weightedIteration_taylor_doubling_rankIndividualYoung hφ hκ hlower U F W hF hV hL hW
    hε hlam hM hb hβ hβ0 (k - (2*d-1)) d (d-1) hd (by omega)
      (fun j _ hj => hscale j (by omega))
  rw [hcur, hprev] at he
  have hsum : (∑ i : Fin (d - 1 + d), ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ) *
      weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + i)) =
      ∑ i : Fin (2 * d - 1), ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ) *
        weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + i) := by
    simpa only [Fin.val_rev] using congrArg (fun q : ℕ =>
      ∑ i : Fin q, ((i : ℕ)+1 : ℝ)*M^(q-((i:ℕ)+1)) *
        weightedIterationDefect hφ hκ hlower U W (k-(2*d-1)+i)) hq
  rw [hsum] at he
  exact he

end KLS.ConstantReduction
end
