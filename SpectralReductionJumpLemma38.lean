import SpectralReductionJumpIteration
import SpectralReductionMeanSymmetrization
import SpectralReductionYoungLemma38
import SpectralReductionGeneralLemma38

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

def jumpTaylorMainCoefficient (M ε : ℝ) (d k q : ℕ) : ℝ :=
  (1+ε)*jumpRecoverySquared d k (q+1)*M^k

def jumpTaylorErrorCoefficient (ε : ℝ) (d k q : ℕ) : ℝ :=
  (jumpRecoverySquared d k (q+1)+(jumpRecoverySquared d k (q+1)-1)/ε) * meanSymmetrizationCoefficient q

theorem jumpTaylorErrorCoefficient_nonneg {ε : ℝ} (hε : 0 < ε)
    {d k q : ℕ} (hd : 1≤d) (hk : 1≤k) (hq : d+k≤q+1) :
    0 ≤ jumpTaylorErrorCoefficient ε d k q := by
  have hc := jumpRecoverySquared_gt_one hd hk hq
  have hcsub : 0≤jumpRecoverySquared d k (q+1)-1 := by linarith
  exact mul_nonneg (by positivity) (meanSymmetrizationCoefficient_nonneg _)

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

theorem weightedIteration_taylor_rankJumpYoung_before_stop
    {lam M ε : ℝ} (hε : 0 < ε) {β : ℕ → ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    (hβ : WeightedCoordinateTaylorCoefficientBound φ β) (hβ0 : ∀ d, 0 ≤ β d)
    (N : ℕ)
    (hscale : ∀ j, j + 1 < N → (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U j)) ^ 2 ≤ M * lam)
    (d k q j : ℕ) (hd : 1 ≤ d) (hk : 1≤k) (hq : d+k≤q+1) (hqj : q≤j) (hjN : j < N) :
    weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d j ≤
      jumpTaylorMainCoefficient M ε d k q * lam ^ k *
        weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (d+k) (j-k) +
      jumpTaylorErrorCoefficient ε d k q * β d / lam *
        ∑ i : Fin q, ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ) *
          weightedIterationDefect hφ hκ hlower U W (j-q+i) := by
  let r := j-q
  let s := q-k
  have hsk : s+k=q := by dsimp [s]; omega
  have hcur : r+(s+k)=j := by dsimp [r]; omega
  have hprev : r+s=j-k := by dsimp [r,s]; omega
  have hscale' : ∀ l, r≤l → l<r+(s+k) →
      (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U l))^2 ≤ M*lam := by
    intro l _ hl
    exact hscale l (by omega)
  have hg := weightedIteration_symmetrization_bound_rankMeanScale (hφ.of_le (by simp)) hκ hlower
    hφ hlam hM hb U F W (fun k i => (hF k i).of_le (by simp)) hW r (s+k)
      (fun l hl hl' => hscale' l (by omega) hl')
  have he := weightedIteration_taylor_jumpYoung hφ hκ hlower U F W hF hV hL
    hε hβ hβ0 r d k s hd hk (by omega)
      (fun i : Fin (s+k) => ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)) hscale' hg
  change weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d (r+(s+k)) ≤
    (1+ε)*jumpRecoverySquared d k (s+k+1)*(M*lam)^k*
      weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (d+k) (r+s) +
    (jumpRecoverySquared d k (s+k+1)+(jumpRecoverySquared d k (s+k+1)-1)/ε)*
      meanSymmetrizationCoefficient (s+k)*β d/lam*
        ∑ i : Fin (s+k), ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)*
          weightedIterationDefect hφ hκ hlower U W (r+i) at he
  rw [hcur,hprev,hsk] at he
  convert he using 1
  simp only [jumpTaylorMainCoefficient,jumpTaylorErrorCoefficient,mul_pow,r]
  ring

end KLS.ConstantReduction
end
