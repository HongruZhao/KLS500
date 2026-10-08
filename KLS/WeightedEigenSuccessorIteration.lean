import KLS.WeightedSuccessorIteration

/-! Initialize the actual tensor recursion at the actual attained first
eigenvector. The initial energy and every later nonzero normalization scale
use that same attained eigenvalue and the faithful Poincare constant. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

def weightedSingleFamily {φ : Space n → ℝ} (U : WeightedCenteredH1 φ) :
    WeightedH1Family φ (Fin 1) := WithLp.toLp 2 (fun _ => U)

theorem weightedSingleFamily_gradient_norm_sq {φ : Space n → ℝ} (U : WeightedCenteredH1 φ) :
    ‖weightedFamilyGradient φ (Fin 1) (weightedSingleFamily U)‖ ^ 2 = weightedEnergyForm φ U U := by
  rw [weightedFamilyGradient_norm_sq, Fin.sum_univ_one, weightedEnergyForm_self]
  rfl

/-- BKL's eigenfunction initialization and finite energy telescoping for the
literal normalized recursion, with no postulated sequence or spectral bound. -/
theorem exists_attained_eigenvalue_successor_iteration
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    ∃ (lam : ℝ) (U : WeightedCenteredH1 φ), κ ≤ lam ∧ 0 < lam ∧
      ‖weightedH1Value φ U‖ = 1 ∧
      (∀ V : WeightedCenteredH1 φ, weightedEnergyForm φ U V =
        lam * inner ℝ (weightedH1Value φ U) (weightedH1Value φ V)) ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      (∀ N : ℕ, lam = weightedIterationEnergy hφ hκ hlower (weightedSingleFamily U) N +
        ∑ k ∈ Finset.range N, weightedIterationMeanLoss hφ hκ hlower (weightedSingleFamily U) k) ∧
      (∀ k : ℕ,
        weightedFamilyCenteredGradient φ (WeightedIterationIndex n (Fin 1) k)
          (weightedSuccessorIterate hφ hκ hlower (weightedSingleFamily U) k) ≠ 0 →
            lam ≤ (weightedSuccessorScale hφ hκ hlower
              (weightedSuccessorIterate hφ hκ hlower (weightedSingleFamily U) k)) ^ 2) := by
  obtain ⟨lam, U, hk, hlam, hU, hweak, hmin, hCP⟩ :=
    exists_positive_weighted_eigenpair_with_optimal_poincare hn hφ hκ hlower
  have he : weightedEnergyForm φ U U = lam := by
    simpa only [real_inner_self_eq_norm_sq, hU, one_pow, mul_one] using hweak U
  have hm : ∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
      weightedEnergyForm φ U U ≤ weightedEnergyForm φ V V := by rwa [he]
  have hRay (V : WeightedCenteredH1 φ) :
      lam * ‖weightedH1Value φ V‖ ^ 2 ≤ weightedEnergyForm φ V V := by
    simpa only [he] using weightedRayleigh_minimizer_lower_bound hm V
  have hb (g : Lp ℝ 2 (potentialMeasure φ)) :
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2 :=
    weightedEnergyInverse_energy_le_of_rayleigh hφ hκ hlower hlam hRay g
  refine ⟨lam, U, hk, hlam, hU, hweak, hCP, ?_, ?_⟩
  · intro N
    have ht := weightedIterationEnergy_telescope hφ hκ hlower (weightedSingleFamily U) N
    simpa only [weightedSingleFamily_gradient_norm_sq, he] using ht
  · intro k hne
    exact weightedSuccessorScale_sq_ge_of_inverse_energy hφ hκ hlower hlam hb _ hne

end KLS
end

#print axioms KLS.weightedSingleFamily_gradient_norm_sq
#print axioms KLS.exists_attained_eigenvalue_successor_iteration
