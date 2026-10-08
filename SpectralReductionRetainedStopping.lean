import SpectralReductionRetainedDefect
import SpectralReductionGeneralStopping

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

/-- The actual first crossing, scale control, energy loss, and reduced
finite defect budget all concern the identical attained eigenvalue orbit. -/
theorem weightedEigenIteration_exists_retained_energy_index
    (U : WeightedCenteredH1 φ)
    (F : (k : ℕ) → WeightedIterationIndex n (Fin 1) k → Space n → ℝ)
    (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n (Fin 1) k))
    (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
    (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower
        (weightedSingleFamily U) k i) : Space n → ℝ))
    (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))
    {lam M : ℝ} (hlam : 0 < lam) (hM : 1 < M)
    (hU : ‖weightedH1Value φ U‖ = 1)
    (heigen : ∀ x, weightedDiffusion φ (F 0 (0 : Fin 1)) x = -lam * F 0 (0 : Fin 1) x)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j
        (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖^2) ≤ lam⁻¹ * ‖g‖^2)
    (hE0 : weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) 0 = lam)
    (hB : ∀ m : ℕ, weightedIterationDiffusionEnergy φ F m +
      (∑ k ∈ Finset.range m, weightedIterationDefect hφ hκ hlower (weightedSingleFamily U) W k) +
      κ * (∑ k ∈ Finset.range m, weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower
        (weightedSingleFamily U) k) ≤ weightedIterationDiffusionEnergy φ F 0) :
    ∃ N : ℕ, 0 < N ∧
      (∀ k, k+1<N → (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k))^2 ≤ M*lam) ∧
      lam-lam/M < ∑ k ∈ Finset.range N,
        weightedIterationMeanLoss (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k ∧
      (∑ k ∈ Finset.range (N-1),
        weightedIterationDefect hφ hκ hlower (weightedSingleFamily U) W k) ≤ (1-1/M)*lam^2 := by
  obtain ⟨N,hN,_hEN,hbefore,hscale,hcross⟩ :=
    weightedEigenIteration_exists_fraction_energy_index hφ hκ hlower U F hF hV hL
      hlam hM hU heigen hE0
  refine ⟨N,hN,hscale,hcross,?_⟩
  exact weightedIterationDefect_sum_before_stop_le_retained hφ hκ hlower
    (weightedSingleFamily U) F W hF hV hlam (by linarith) hb hE0
    (weightedEigenIteration_initial_diffusion_energy U F (hV 0 (0 : Fin 1)) hU heigen)
    hB N (hbefore (N-1) (by omega))

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedEigenIteration_exists_retained_energy_index
