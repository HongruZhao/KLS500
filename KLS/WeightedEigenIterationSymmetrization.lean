import KLS.WeightedIterationSymmetrization
import KLS.WeightedEigenIterationConvergence

/-! A single attained eigenpair supplies both the actual convergent BKL
iteration and its actual prefix-symmetrization bounds. No orbital regularity,
Hessian representation, or spectral bound is imposed as an extra hypothesis. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal Topology BigOperators

noncomputable section
namespace KLS
variable {n : ℕ}

theorem exists_attained_eigenvalue_symmetrized_iteration
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    ∃ (lam : ℝ) (U : WeightedCenteredH1 φ)
      (F : (k : ℕ) → WeightedIterationIndex n (Fin 1) k → Space n → ℝ)
      (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n (Fin 1) k)),
      κ ≤ lam ∧ 0 < lam ∧ ‖weightedH1Value φ U‖ = 1 ∧
      (∀ V : WeightedCenteredH1 φ, weightedEnergyForm φ U V =
        lam * inner ℝ (weightedH1Value φ U) (weightedH1Value φ V)) ∧
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
      (∀ k,
        weightedFamilyValue φ (Fin n × WeightedIterationIndex n (Fin 1) k) (W k) =
          weightedFamilyCenteredGradient φ (WeightedIterationIndex n (Fin 1) k)
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k) ∧
        ∀ j l i, (weightedH1Derivative φ j (W k (l, i)) : Space n → ℝ)
          =ᵐ[potentialMeasure φ] fun x => coordinateHessian (F k i) x j l) ∧
      weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) 0 = lam ∧
      Tendsto (weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U))
        atTop (𝓝 0) ∧
      HasSum (weightedIterationMeanLoss (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U)) lam ∧
      Summable (weightedIterationDefect hφ hκ hlower (weightedSingleFamily U) W) ∧
      (∑' k, weightedIterationDefect hφ hκ hlower (weightedSingleFamily U) W k) ≤ lam ^ 2 ∧
      (∀ r q : ℕ,
        (∀ k, r + 1 ≤ k → k < r + q →
          (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k)) ^ 2 ≤
              2 * lam) →
        ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n (Fin 1) (r + q))
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) (r + q)) -
          weightedIterationSymmetrizedGradient (hφ.of_le (by simp)) hκ hlower
            (weightedSingleFamily U) r q‖ ^ 2 ≤
          (128 : ℝ) ^ (q + 1) / lam *
            ∑ i : Fin q, weightedIterationDefect hφ hκ hlower (weightedSingleFamily U) W (r + i)) := by
  obtain ⟨lam, U, f, F, W, hk, hlam, hU, hweak, hCP, _, hb, _, hzero, hF, hV,
    hLF, hpoint, hW, hE0, _, _, hEt, hP, hCs, hCb⟩ :=
    exists_attained_eigenvalue_convergent_iteration hn hφ hκ hlower
  refine ⟨lam, U, F, W, hk, hlam, hU, hweak, hCP, hb, hF, hV, hLF, ?_, hW, hE0,
    hEt, hP, hCs, hCb, ?_⟩
  · simpa only [hzero] using hpoint
  · intro r q hscale
    exact weightedIteration_symmetrization_bound (hφ.of_le (by simp)) hκ hlower hφ hlam hb
      (weightedSingleFamily U) F W (fun k i => (hF k i).of_le (by simp))
      (fun k => (hW k).2) r q hscale

end KLS
end

#print axioms KLS.exists_attained_eigenvalue_symmetrized_iteration
