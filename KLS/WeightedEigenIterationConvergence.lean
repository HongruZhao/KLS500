import KLS.WeightedIterationEnergyConvergence
import KLS.WeightedEigenSuccessorIteration
import KLS.WeightedEigenRegularity

/-! The complete energy convergence specialization uses one actual attained
eigenpair throughout. Its smooth representative, initial diffusion energy,
inverse bound, and all later scale bounds are derived from that same pair. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal Topology

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hn : 0 < n) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hn hφ hκ hlower

/-- Actual smooth diffusion-domain data for the same attained first
eigenvector that supplies the global Rayleigh bound. -/
theorem exists_attained_smooth_eigenvalue_iteration_data :
    ∃ (lam : ℝ) (U : WeightedCenteredH1 φ) (f : Space n → ℝ),
      κ ≤ lam ∧ 0 < lam ∧ ‖weightedH1Value φ U‖ = 1 ∧
      (∀ V : WeightedCenteredH1 φ, weightedEnergyForm φ U V =
        lam * inner ℝ (weightedH1Value φ U) (weightedH1Value φ V)) ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ) ∧
      MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ) ∧
      (∀ x, weightedDiffusion φ f x = -lam * f x) ∧
      (∫ x, weightedDiffusion φ f x ^ 2 ∂potentialMeasure φ) = lam ^ 2 ∧
      weightedEnergyForm φ U U = lam ∧
      (∀ V : WeightedCenteredH1 φ,
        lam * ‖weightedH1Value φ V‖ ^ 2 ≤ weightedEnergyForm φ V V) := by
  obtain ⟨lam, U, hk, hlam, hU, hweak, hmin, hCP⟩ :=
    exists_positive_weighted_eigenpair_with_optimal_poincare hn (hφ.of_le (by simp)) hκ hlower
  obtain ⟨f, hf, hv, hvμ⟩ := weighted_eigenpair_exists_smooth_representative hφ hweak
  have hf2 : MemLp f 2 (potentialMeasure φ) := (memLp_congr_ae hvμ).mpr (Lp.memLp _)
  have hpoint : ∀ x, weightedDiffusion φ f x = -lam * f x :=
    weighted_eigenpair_pointwise_of_representative (hφ.of_le (by simp)) hweak
      (hf.of_le (by simp)) hv
  have hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ) := by
    have heq : weightedDiffusion φ f = fun x => -lam * f x := funext hpoint
    rw [heq]
    exact hf2.const_mul (-lam)
  have hsq : (∫ x, f x ^ 2 ∂potentialMeasure φ) = 1 := by
    calc
      _ = ∫ x, weightedH1Value φ U x ^ 2 ∂potentialMeasure φ := by
        apply integral_congr_ae
        filter_upwards [hvμ] with x hx
        rw [hx]
      _ = ‖weightedH1Value φ U‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, L2.real_inner_eq_integral]
        simp only [pow_two]
      _ = 1 := by rw [hU, one_pow]
  have hD : (∫ x, weightedDiffusion φ f x ^ 2 ∂potentialMeasure φ) = lam ^ 2 := by
    simp_rw [hpoint, mul_pow, neg_sq]
    rw [integral_const_mul, hsq, mul_one]
  have he : weightedEnergyForm φ U U = lam := by
    simpa only [real_inner_self_eq_norm_sq, hU, one_pow, mul_one] using hweak U
  have hm : ∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
      weightedEnergyForm φ U U ≤ weightedEnergyForm φ V V := by rwa [he]
  refine ⟨lam, U, f, hk, hlam, hU, hweak, hCP, hf, hv, hL, hpoint, hD, he, ?_⟩
  intro V
  simpa only [he] using weightedRayleigh_minimizer_lower_bound hm V

/-- Eigenfunction initialization, actual infinite energy convergence, exact
mean-loss sum, summable actual Hessian defects, and every inverse/scale lower
bound use the same attained eigenvalue. No regularity along the orbit is
assumed; the representatives and Hessian graph elements are constructed. -/
theorem exists_attained_eigenvalue_convergent_iteration :
    ∃ (lam : ℝ) (U : WeightedCenteredH1 φ) (f : Space n → ℝ)
      (F : (k : ℕ) → WeightedIterationIndex n (Fin 1) k → Space n → ℝ)
      (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n (Fin 1) k)),
      κ ≤ lam ∧ 0 < lam ∧ ‖weightedH1Value φ U‖ = 1 ∧
      (∀ V : WeightedCenteredH1 φ, weightedEnergyForm φ U V =
        lam * inner ℝ (weightedH1Value φ U) (weightedH1Value φ V)) ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      (∀ V : WeightedCenteredH1 φ,
        lam * ‖weightedH1Value φ V‖ ^ 2 ≤ weightedEnergyForm φ V V) ∧
      (∀ g : Lp ℝ 2 (potentialMeasure φ),
        (∑ j, ‖weightedH1Derivative φ j
          (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
            lam⁻¹ * ‖g‖ ^ 2) ∧
      (∀ k : ℕ,
        weightedFamilyCenteredGradient φ (WeightedIterationIndex n (Fin 1) k)
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k) ≠ 0 →
            lam ≤ (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
              (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower
                (weightedSingleFamily U) k)) ^ 2) ∧
      F 0 = (fun _ : Fin 1 => f) ∧
      (∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i)) ∧
      (∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower
          (weightedSingleFamily U) k i) : Space n → ℝ)) ∧
      (∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ)) ∧
      (∀ x, weightedDiffusion φ f x = -lam * f x) ∧
      (∀ k,
        weightedFamilyValue φ (Fin n × WeightedIterationIndex n (Fin 1) k) (W k) =
          weightedFamilyCenteredGradient φ (WeightedIterationIndex n (Fin 1) k)
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k) ∧
        ∀ j l i, (weightedH1Derivative φ j (W k (l, i)) : Space n → ℝ)
          =ᵐ[potentialMeasure φ] fun x => coordinateHessian (F k i) x j l) ∧
      weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) 0 = lam ∧
      Summable (weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U)) ∧
      (∑' k, weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k) ≤
        lam ^ 2 / κ ∧
      Tendsto (weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U))
        atTop (𝓝 0) ∧
      HasSum (weightedIterationMeanLoss (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U)) lam ∧
      Summable (weightedIterationDefect hφ hκ hlower (weightedSingleFamily U) W) ∧
      (∑' k, weightedIterationDefect hφ hκ hlower (weightedSingleFamily U) W k) ≤ lam ^ 2 := by
  let hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  obtain ⟨lam, U, f, hk, hlam, hU, hweak, hCP, hf, hv, hL, hpoint, hD, he, hRay⟩ :=
    exists_attained_smooth_eigenvalue_iteration_data hn hφ hκ hlower
  have hb (g : Lp ℝ 2 (potentialMeasure φ)) :
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ2 hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2 :=
    weightedEnergyInverse_energy_le_of_rayleigh hφ2 hκ hlower hlam hRay g
  let f0 : Fin 1 → Space n → ℝ := fun _ => f
  have hf0 : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f0 i) := fun _ => hf
  have hv0 : ∀ i, f0 i =ᵐ[volume]
      (weightedH1Value φ (weightedSingleFamily U i) : Space n → ℝ) := fun _ => hv
  have hL0 : ∀ i, MemLp (weightedDiffusion φ (f0 i)) 2 (potentialMeasure φ) := fun _ => hL
  have hD0 : (∑ i, ∫ x, weightedDiffusion φ (f0 i) x ^ 2 ∂potentialMeasure φ) = lam ^ 2 := by
    simpa only [Fin.sum_univ_one] using hD
  obtain ⟨F, W, hzero, hF, hV, hLF, hW, hCs, hCb⟩ :=
    exists_weightedIteration_summable_defects hφ hκ hlower (weightedSingleFamily U) f0 hf0 hv0 hL0
  obtain ⟨hEs, hEb⟩ := weightedIterationEnergy_summable_and_bound hφ hκ hlower
    (weightedSingleFamily U) f0 hf0 hv0 hL0
  have hP := weightedIterationMeanLoss_hasSum hφ hκ hlower (weightedSingleFamily U) f0 hf0 hv0 hL0
  rw [hD0] at hEb hCb
  rw [weightedSingleFamily_gradient_norm_sq, he] at hP
  refine ⟨lam, U, f, F, W, hk, hlam, hU, hweak, hCP, hRay, hb, ?_, hzero, hF, hV,
    hLF, hpoint, hW, ?_, hEs, hEb, hEs.tendsto_atTop_zero, hP, hCs, hCb⟩
  · intro k hne
    exact weightedSuccessorScale_sq_ge_of_inverse_energy hφ2 hκ hlower hlam hb _ hne
  · change ‖weightedFamilyGradient φ (Fin 1) (weightedSingleFamily U)‖ ^ 2 = lam
    rw [weightedSingleFamily_gradient_norm_sq, he]

end KLS
end

#print axioms KLS.exists_attained_smooth_eigenvalue_iteration_data
#print axioms KLS.exists_attained_eigenvalue_convergent_iteration
