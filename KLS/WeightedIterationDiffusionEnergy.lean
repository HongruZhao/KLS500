import KLS.WeightedIterationBochner

/-! Actual diffusion energy along any smooth representatives of the genuine
normalized iteration. Both the forcing identity and monotonicity are proved
from the existing normalized Poisson and Bochner theorems. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal Topology

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
  (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))

include hF hV

/-- The genuine diffusion energy equals the actual forcing norm at every
successor, including the zero branch. -/
theorem weightedIterationDiffusionEnergy_eq_forcing (k : ℕ) :
    weightedIterationDiffusionEnergy φ F (k + 1) =
      ‖weightedSuccessorForcing (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)‖ ^ 2 := by
  change (∑ ki : Fin n × WeightedIterationIndex n ι k,
    ∫ x, weightedDiffusion φ (F (k + 1) ki) x ^ 2 ∂potentialMeasure φ) = _
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro ki _
  rw [realLp_norm_sq_eq_integral_sq_of_ae
    (weightedSuccessorForcing_ae_of_representative (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) (F k)
      (fun i => (hF k i).of_le (by simp)) (hV k) ki)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x =>
    (congrArg (fun t : ℝ => t ^ 2)
      (weightedIteration_smooth_successor_equation hφ hκ hlower U F hF hV k ki x)).trans (by ring)

/-- BKL (46) for the literal iteration and its actual smooth representatives. -/
theorem weightedIterationDiffusionEnergy_eq_scale_sq_mul (k : ℕ) :
    weightedIterationDiffusionEnergy φ F (k + 1) =
      (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) ^ 2 *
          weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U (k + 1) := by
  rw [weightedIterationDiffusionEnergy_eq_forcing hφ hκ hlower U F hF hV,
    weightedSuccessorForcing_norm_sq]
  rfl

variable (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))

include hL

/-- Genuine Bochner dissipation implies diffusion energy decreases. -/
theorem weightedIterationDiffusionEnergy_succ_le (k : ℕ) :
    weightedIterationDiffusionEnergy φ F (k + 1) ≤ weightedIterationDiffusionEnergy φ F k := by
  obtain ⟨gnext, W, hg, _, _, _, _, hB⟩ := exists_weightedNormalizedSuccessor_bochner_step
    hφ hκ hlower (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)
      (F k) (hF k) (hV k) (hL k)
  have he : gnext = F (k + 1) := by
    funext i
    exact continuous_representative_unique (hg i).1.continuous (hF (k + 1) i).continuous
      ((hg i).2.2.2.1.trans (hV (k + 1) i).symm)
  rw [he] at hB
  have hchi : 0 ≤ weightedSuccessorHessianDefect (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) W := sq_nonneg _
  have hgrad := mul_nonneg hκ.le (sq_nonneg
    ‖weightedFamilyGradient φ (WeightedIterationIndex n ι k)
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)‖)
  change weightedIterationDiffusionEnergy φ F (k + 1) + _ + _ ≤
    weightedIterationDiffusionEnergy φ F k at hB
  linarith

theorem weightedIterationDiffusionEnergy_antitone : Antitone (weightedIterationDiffusionEnergy φ F) :=
  antitone_nat_of_succ_le (weightedIterationDiffusionEnergy_succ_le hφ hκ hlower U F hF hV hL)

/-- At a level whose next energy is at least half of lambda, the actual
normalization factor satisfies the paper's upper bound. -/
theorem weightedIterationScale_sq_le_of_half_energy {lam : ℝ} (hlam : 0 < lam)
    (hD0 : weightedIterationDiffusionEnergy φ F 0 ≤ lam ^ 2) (k : ℕ)
    (hhalf : lam / 2 ≤ weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U (k + 1)) :
    (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) ^ 2 ≤ 2 * lam := by
  have hD := (weightedIterationDiffusionEnergy_antitone hφ hκ hlower U F hF hV hL
    (Nat.zero_le (k + 1))).trans hD0
  rw [weightedIterationDiffusionEnergy_eq_scale_sq_mul hφ hκ hlower U F hF hV] at hD
  have hscale := sq_nonneg (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k))
  nlinarith

end KLS
end

#print axioms KLS.weightedIterationDiffusionEnergy_eq_forcing
#print axioms KLS.weightedIterationDiffusionEnergy_eq_scale_sq_mul
#print axioms KLS.weightedIterationDiffusionEnergy_antitone
#print axioms KLS.weightedIterationScale_sq_le_of_half_energy
