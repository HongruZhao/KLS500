import KLS.WeightedIterationDiffusionEnergy
import KLS.WeightedIterationEnergyConvergence
import KLS.WeightedEigenIterationConvergence

/-! The first actual energy below half of the initial eigenvalue exists by
proved energy convergence. Minimality and the genuine diffusion identity
derive the normalization upper bound throughout the preceding interval. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal Topology BigOperators

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

/-- The first half-energy crossing and all preceding scale bounds are
conclusions about the actual iteration. Our level zero is paper index one. -/
theorem weightedIteration_exists_half_energy_index
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
    (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
    (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
    (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))
    {lam : ℝ} (hlam : 0 < lam)
    (hE0 : weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U 0 = lam)
    (hD0 : weightedIterationDiffusionEnergy φ F 0 ≤ lam ^ 2) :
    ∃ N : ℕ, 0 < N ∧
      weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U N < lam / 2 ∧
      (∀ k < N, lam / 2 ≤ weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U k) ∧
      (∀ k, k + 1 < N →
        (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) ^ 2 ≤ 2 * lam) ∧
      lam / 2 < ∑ k ∈ Finset.range N, weightedIterationMeanLoss (hφ.of_le (by simp)) hκ hlower U k := by
  let E := weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U
  have ht : Tendsto E atTop (𝓝 0) :=
    weightedIterationEnergy_tendsto_zero hφ hκ hlower U (F 0) (hF 0) (hV 0) (hL 0)
  have hex : ∃ k : ℕ, E k < lam / 2 :=
    (ht.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < lam / 2))).exists
  let N := Nat.find hex
  have hN : E N < lam / 2 := Nat.find_spec hex
  have hbefore (k : ℕ) (hk : k < N) : lam / 2 ≤ E k :=
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
    exact weightedIterationScale_sq_le_of_half_energy hφ hκ hlower U F hF hV hL
      hlam hD0 k (hbefore (k + 1) hk)
  · have htel := weightedIterationEnergy_telescope (hφ.of_le (by simp)) hκ hlower U N
    have he : ‖weightedFamilyGradient φ ι U‖ ^ 2 = lam := hE0
    rw [he] at htel
    change weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U N < _ at hN
    linarith

omit [IsProbabilityMeasure (potentialMeasure φ)] in
/-- Any actual normalized eigenfunction representative has initial diffusion
energy lambda squared. This uses the same eigenvalue, without reselection. -/
theorem weightedEigenIteration_initial_diffusion_energy
    (U : WeightedCenteredH1 φ) (F : (k : ℕ) → WeightedIterationIndex n (Fin 1) k → Space n → ℝ)
    (hV : F 0 (0 : Fin 1) =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ))
    (hU : ‖weightedH1Value φ U‖ = 1) {lam : ℝ}
    (heigen : ∀ x, weightedDiffusion φ (F 0 (0 : Fin 1)) x = -lam * F 0 (0 : Fin 1) x) :
    weightedIterationDiffusionEnergy φ F 0 = lam ^ 2 := by
  have hvμ : (weightedH1Value φ U : Space n → ℝ) =ᵐ[potentialMeasure φ] F 0 (0 : Fin 1) :=
    (withDensity_absolutelyContinuous _ _).ae_eq hV.symm
  have hsq := realLp_norm_sq_eq_integral_sq_of_ae hvμ
  rw [hU, one_pow] at hsq
  change (∑ i : Fin 1, ∫ x, weightedDiffusion φ (F 0 i) x ^ 2 ∂potentialMeasure φ) = _
  rw [Fin.sum_univ_one]
  simp_rw [heigen, mul_pow, neg_sq]
  rw [integral_const_mul, ← hsq, mul_one]

/-- Direct specialization to any one normalized attained eigenpair already
chosen by the spectral theorem; no new eigenvalue or orbit is selected. -/
theorem weightedEigenIteration_exists_half_energy_index
    (U : WeightedCenteredH1 φ)
    (F : (k : ℕ) → WeightedIterationIndex n (Fin 1) k → Space n → ℝ)
    (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
    (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k i) : Space n → ℝ))
    (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))
    {lam : ℝ} (hlam : 0 < lam) (hU : ‖weightedH1Value φ U‖ = 1)
    (heigen : ∀ x, weightedDiffusion φ (F 0 (0 : Fin 1)) x = -lam * F 0 (0 : Fin 1) x)
    (hE0 : weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) 0 = lam) :
    ∃ N : ℕ, 0 < N ∧
      weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) N < lam / 2 ∧
      (∀ k < N, lam / 2 ≤ weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k) ∧
      (∀ k, k + 1 < N →
        (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k)) ^ 2 ≤ 2 * lam) ∧
      lam / 2 < ∑ k ∈ Finset.range N,
        weightedIterationMeanLoss (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k := by
  have hD0 := weightedEigenIteration_initial_diffusion_energy U F (hV 0 (0 : Fin 1)) hU heigen
  exact weightedIteration_exists_half_energy_index hφ hκ hlower (weightedSingleFamily U) F
    hF hV hL hlam hE0 hD0.le

end KLS
end

#print axioms KLS.weightedIteration_exists_half_energy_index
#print axioms KLS.weightedEigenIteration_initial_diffusion_energy
#print axioms KLS.weightedEigenIteration_exists_half_energy_index
