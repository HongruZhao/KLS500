import KLS.C1WeightedEquation
import KLS.WeightedAnnihilatorEnergy

/-!
# C¹ potential: C1WeightedEnergy

This extension uses the actual diffusion and weighted L² representatives.
Only first derivatives of the source potential are required.
-/

open MeasureTheory InnerProductSpace Set Filter ContinuousLinearMap
open scoped ContDiff ENNReal Convolution Topology

noncomputable section
namespace KLS
variable {n : ℕ}

theorem weighted_annihilator_exists_local_energy_C1 {φ χ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hχ : ContDiff ℝ 3 χ) (hc : HasCompactSupport χ) :
    ∃ (f : Space n → ℝ) (G : Fin n → Lp ℝ 2 (volume : Measure (Space n))),
      MemLp f 2 volume ∧ HasCompactSupport f ∧
      (∀ i, HasWeakCoordinateDerivative f i (G i)) ∧
      (∀ x ∈ tsupport χ, f x = u x) ∧
      (∑ i, ∫ x, Real.exp (-φ x) * χ x ^ 2 * (G i x) ^ 2) ≤
        4 * ∑ i, ∫ x, Real.exp (-φ x) * u x ^ 2 * (coordinateDerivative χ i x) ^ 2 := by
  obtain ⟨η, hη, hηc, hη1⟩ := exists_smooth_compact_one_on_compact hc
  let f : Space n → ℝ := fun x => η x ^ 2 * u x
  have hηsq : HasCompactSupport (fun x => η x ^ 2) := by
    convert! hηc.mul_right (f' := η) using 1
    funext x
    simp only [pow_two, Pi.mul_apply]
  have hf : MemLp f 2 volume := memLp_compact_mul_of_local (hη.continuous.pow 2) hηsq
    (fun _ hK => KLS.MemLp.restrict_volume_of_potentialMeasure (Lp.memLp u) hφ.continuous hK)
  have hfc : HasCompactSupport f := hηsq.mul_right
  have heq (x : Space n) (hx : x ∈ tsupport χ) : f x = u x := by
    simp [f, hη1 x hx]
  choose G hG using fun i => weighted_annihilator_compact_square_hasWeakDerivative_C1 hφ u hu
    (hη.of_le (by simp)) hηc i
  have hweak := weighted_annihilator_localized_weak_equation_C1 hφ u hu hf G hG hχ hc heq
  have he := weak_caccioppoli (Real.continuous_exp.comp hφ.continuous.neg) (fun x => (Real.exp_pos _).le)
    hf hfc G hG hχ hc hweak
  refine ⟨f, G, hf, hfc, hG, heq, ?_⟩
  change (∑ i, ∫ x, Real.exp (-φ x) * χ x ^ 2 * (G i x) ^ 2) ≤
    4 * ∑ i, ∫ x, Real.exp (-φ x) * f x ^ 2 * (coordinateDerivative χ i x) ^ 2 at he
  have hr : (∑ i, ∫ x, Real.exp (-φ x) * f x ^ 2 * (coordinateDerivative χ i x) ^ 2) =
      ∑ i, ∫ x, Real.exp (-φ x) * u x ^ 2 * (coordinateDerivative χ i x) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport χ
      · rw [heq x hx]
      · have hd : coordinateDerivative χ i x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hi => hx (tsupport_coordinateDerivative_subset χ i hi))
        simp [hd]
  rwa [hr] at he

end KLS
end
