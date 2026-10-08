import KLS.WeightedEigenIterationConvergence
import KLS.WeightedIterationStoppingIndex

/-! Retain the diffusion energy in the genuine finite Bochner telescope.
At the last index before a first energy crossing, this bounds the defects
by the lost fraction of lambda squared, with no stopping overshoot. -/
open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem weightedIterationDiffusionEnergy_ge_spectral
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
    (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
    (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
    {lam : ℝ} (hlam : 0 < lam)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j
        (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
          lam⁻¹ * ‖g‖ ^ 2)
    (hzero : lam * weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U 0 ≤
      weightedIterationDiffusionEnergy φ F 0) (k : ℕ) :
    lam * weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U k ≤
      weightedIterationDiffusionEnergy φ F k := by
  cases k with
  | zero => exact hzero
  | succ k =>
    rw [weightedIterationDiffusionEnergy_eq_scale_sq_mul hφ hκ hlower U F hF hV]
    by_cases hz : weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι k)
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) = 0
    · have he : weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U (k+1) = 0 := by
        change ‖weightedFamilyGradient φ (Fin n × WeightedIterationIndex n ι k)
          (weightedNormalizedSuccessor (hφ.of_le (by simp)) hκ hlower
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k))‖^2 = 0
        rw [weightedNormalizedSuccessor_gradient_norm, hz]
        simp
      rw [he]
      simp
    · exact mul_le_mul_of_nonneg_right
        (weightedSuccessorScale_sq_ge_of_inverse_energy (hφ.of_le (by simp)) hκ hlower
          hlam hb _ hz) (weightedIterationEnergy_nonneg (hφ.of_le (by simp)) hκ hlower U _)

theorem weightedIterationDefect_sum_before_stop_le_retained
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
    (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n ι k))
    (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
    (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
    {lam M : ℝ} (hlam : 0 < lam) (_hM : 0 < M)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j
        (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
          lam⁻¹ * ‖g‖ ^ 2)
    (hE0 : weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U 0 = lam)
    (hD0 : weightedIterationDiffusionEnergy φ F 0 = lam^2)
    (hB : ∀ m : ℕ,
      weightedIterationDiffusionEnergy φ F m +
        (∑ k ∈ Finset.range m, weightedIterationDefect hφ hκ hlower U W k) +
        κ * (∑ k ∈ Finset.range m,
          weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U k) ≤
            weightedIterationDiffusionEnergy φ F 0)
    (N : ℕ)
    (hretained : lam/M ≤ weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U (N-1)) :
    (∑ k ∈ Finset.range (N-1), weightedIterationDefect hφ hκ hlower U W k) ≤
      (1-1/M)*lam^2 := by
  have hinit : lam * weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U 0 ≤
      weightedIterationDiffusionEnergy φ F 0 := by rw [hE0,hD0]; nlinarith
  have hD := weightedIterationDiffusionEnergy_ge_spectral hφ hκ hlower U F hF hV
    hlam hb hinit (N-1)
  have hbudget := hB (N-1)
  rw [hD0] at hbudget
  have hκE : 0 ≤ κ * (∑ k ∈ Finset.range (N-1),
      weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U k) :=
    mul_nonneg hκ.le (Finset.sum_nonneg fun k _ =>
      weightedIterationEnergy_nonneg (hφ.of_le (by simp)) hκ hlower U k)
  have hmul := mul_le_mul_of_nonneg_left hretained hlam.le
  have hid : lam^2-lam*(lam/M)=(1-1/M)*lam^2 := by ring
  rw [←hid]
  linarith

/-- Construct the same attained first eigenpair and its actual orbit while
preserving the finite Bochner inequality used by the retained budget. -/
theorem exists_attained_eigenvalue_retained_iteration (hn : 0 < n) :
    ∃ (lam : ℝ) (U : WeightedCenteredH1 φ)
      (F : (k : ℕ) → WeightedIterationIndex n (Fin 1) k → Space n → ℝ)
      (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n (Fin 1) k)),
      0 < lam ∧ ‖weightedH1Value φ U‖ = 1 ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      (∀ g : Lp ℝ 2 (potentialMeasure φ),
        (∑ j, ‖weightedH1Derivative φ j
          (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
            lam⁻¹ * ‖g‖ ^ 2) ∧
      (∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i)) ∧
      (∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower
          (weightedSingleFamily U) k i) : Space n → ℝ)) ∧
      (∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ)) ∧
      (∀ x, weightedDiffusion φ (F 0 (0 : Fin 1)) x = -lam * F 0 (0 : Fin 1) x) ∧
      (∀ k j l i, (weightedH1Derivative φ j (W k (l,i)) : Space n → ℝ)
        =ᵐ[potentialMeasure φ] fun x => coordinateHessian (F k i) x j l) ∧
      weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) 0 = lam ∧
      weightedIterationDiffusionEnergy φ F 0 = lam^2 ∧
      (∀ m : ℕ, weightedIterationDiffusionEnergy φ F m +
        (∑ k ∈ Finset.range m, weightedIterationDefect hφ hκ hlower (weightedSingleFamily U) W k) +
        κ * (∑ k ∈ Finset.range m, weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower
          (weightedSingleFamily U) k) ≤ weightedIterationDiffusionEnergy φ F 0) := by
  let hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  obtain ⟨lam,U,f,_hk,hlam,hU,_hweak,hCP,hf,hv,hL,hpoint,_hD,he,hRay⟩ :=
    exists_attained_smooth_eigenvalue_iteration_data hn hφ hκ hlower
  have hb (g : Lp ℝ 2 (potentialMeasure φ)) :
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ2 hκ hlower g)‖^2) ≤
        lam⁻¹ * ‖g‖^2 := weightedEnergyInverse_energy_le_of_rayleigh hφ2 hκ hlower hlam hRay g
  obtain ⟨F,W,hzero,hF,hV,hLF,hW,hB⟩ := exists_weightedIteration_bochner_sequence hφ hκ hlower
    (weightedSingleFamily U) (fun _ : Fin 1 => f) (fun _ => hf) (fun _ => hv) (fun _ => hL)
  have hpointF : ∀ x, weightedDiffusion φ (F 0 (0 : Fin 1)) x = -lam * F 0 (0 : Fin 1) x := by
    simpa only [hzero] using hpoint
  refine ⟨lam,U,F,W,hlam,hU,hCP,hb,hF,hV,hLF,hpointF,fun k => (hW k).2.1,?_,?_,hB⟩
  · change ‖weightedFamilyGradient φ (Fin 1) (weightedSingleFamily U)‖^2 = lam
    rw [weightedSingleFamily_gradient_norm_sq,he]
  · exact weightedEigenIteration_initial_diffusion_energy U F (hV 0 (0 : Fin 1)) hU hpointF

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedIterationDiffusionEnergy_ge_spectral
#print axioms KLS.ConstantReduction.weightedIterationDefect_sum_before_stop_le_retained
#print axioms KLS.ConstantReduction.exists_attained_eigenvalue_retained_iteration
