import KLS.WeightedIterationStoppingIndex

/-! A freely chosen retained-energy fraction gives the actual stopping index
and corresponding normalization bound on the identical attained-eigenvalue
iteration. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

section Scale
variable {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
  (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
  (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))

include hF hV hL

theorem weightedIterationScale_sq_le_of_fraction_energy {lam M : ℝ} (hlam : 0 < lam) (hM : 0 < M)
    (hD0 : weightedIterationDiffusionEnergy φ F 0 ≤ lam ^ 2) (k : ℕ)
    (hhalf : lam / M ≤ weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U (k + 1)) :
    (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) ^ 2 ≤ M * lam := by
  have hD := (weightedIterationDiffusionEnergy_antitone hφ hκ hlower U F hF hV hL
    (Nat.zero_le (k + 1))).trans hD0
  rw [weightedIterationDiffusionEnergy_eq_scale_sq_mul hφ hκ hlower U F hF hV] at hD
  have hscale := sq_nonneg (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k))
  have hmul := mul_le_mul_of_nonneg_left hhalf hscale
  have hden : (lam / M) * M = lam := div_mul_cancel₀ lam (ne_of_gt hM)
  have hh := mul_le_mul_of_nonneg_right hmul hM.le
  nlinarith

end Scale

theorem weightedIteration_exists_fraction_energy_index
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
    (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
    (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
    (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))
    {lam M : ℝ} (hlam : 0 < lam) (hM : 1 < M)
    (hE0 : weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U 0 = lam)
    (hD0 : weightedIterationDiffusionEnergy φ F 0 ≤ lam ^ 2) :
    ∃ N : ℕ, 0 < N ∧
      weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U N < lam / M ∧
      (∀ k < N, lam / M ≤ weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U k) ∧
      (∀ k, k + 1 < N →
        (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) ^ 2 ≤ M * lam) ∧
      lam - lam / M < ∑ k ∈ Finset.range N, weightedIterationMeanLoss (hφ.of_le (by simp)) hκ hlower U k := by
  have hM0 : 0 < M := by linarith
  have hden : (lam / M) * M = lam := div_mul_cancel₀ lam (ne_of_gt hM0)
  have hlt : lam / M < lam := by
    apply (div_lt_iff₀ hM0).2
    nlinarith
  let E := weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U
  have ht : Tendsto E atTop (𝓝 0) :=
    weightedIterationEnergy_tendsto_zero hφ hκ hlower U (F 0) (hF 0) (hV 0) (hL 0)
  have hex : ∃ k : ℕ, E k < lam / M :=
    (ht.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < lam / M))).exists
  let N := Nat.find hex
  have hN : E N < lam / M := Nat.find_spec hex
  have hbefore (k : ℕ) (hk : k < N) : lam / M ≤ E k :=
    le_of_not_gt (Nat.find_min hex hk)
  have hpos : 0 < N := by
    by_contra h
    have hz : N = 0 := by omega
    rw [hz] at hN
    change weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U 0 < _ at hN
    rw [hE0] at hN
    linarith
  refine ⟨N, hpos, hN, hbefore, ?_, ?_⟩
  · intro k hk
    exact weightedIterationScale_sq_le_of_fraction_energy hφ hκ hlower U F hF hV hL
      hlam hM0 hD0 k (hbefore (k + 1) hk)
  · have htel := weightedIterationEnergy_telescope (hφ.of_le (by simp)) hκ hlower U N
    have he : ‖weightedFamilyGradient φ ι U‖ ^ 2 = lam := hE0
    rw [he] at htel
    change weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U N < _ at hN
    linarith

theorem weightedEigenIteration_exists_fraction_energy_index
    (U : WeightedCenteredH1 φ)
    (F : (k : ℕ) → WeightedIterationIndex n (Fin 1) k → Space n → ℝ)
    (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
    (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k i) : Space n → ℝ))
    (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))
    {lam M : ℝ} (hlam : 0 < lam) (hM : 1 < M) (hU : ‖weightedH1Value φ U‖ = 1)
    (heigen : ∀ x, weightedDiffusion φ (F 0 (0 : Fin 1)) x = -lam * F 0 (0 : Fin 1) x)
    (hE0 : weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) 0 = lam) :
    ∃ N : ℕ, 0 < N ∧
      weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) N < lam / M ∧
      (∀ k < N, lam / M ≤ weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k) ∧
      (∀ k, k + 1 < N →
        (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k)) ^ 2 ≤ M * lam) ∧
      lam - lam / M < ∑ k ∈ Finset.range N,
        weightedIterationMeanLoss (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k := by
  have hD0 := weightedEigenIteration_initial_diffusion_energy U F (hV 0 (0 : Fin 1)) hU heigen
  exact weightedIteration_exists_fraction_energy_index hφ hκ hlower (weightedSingleFamily U) F
    hF hV hL hlam hM hE0 hD0.le

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedIterationScale_sq_le_of_fraction_energy
#print axioms KLS.ConstantReduction.weightedIteration_exists_fraction_energy_index
#print axioms KLS.ConstantReduction.weightedEigenIteration_exists_fraction_energy_index
