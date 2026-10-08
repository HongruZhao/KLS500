import KLS.WeightedSuccessorDomain

/-! Actual Hessian symmetry and the BKL one-step symmetric approximation.
The final endpoint constructs the Hessian graph from the genuine smooth
diffusion domain and obtains lam from the attained Poincare eigenvalue. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

theorem weightedFamilyHessian_symmetric {φ : Space n → ℝ}
    {ι : Type*} [Fintype ι] (W : WeightedH1Family φ (Fin n × ι))
    (f : ι → Space n → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hd : ∀ j k i, (weightedH1Derivative φ j (W (k, i)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x => coordinateHessian (f i) x j k)
    (j k : Fin n) (i : ι) :
    weightedFamilyGradient φ (Fin n × ι) W (j, (k, i)) =
      weightedFamilyGradient φ (Fin n × ι) W (k, (j, i)) := by
  apply Lp.ext
  filter_upwards [hd j k i, hd k j i] with x hx hy
  change weightedH1Derivative φ j (W (k, i)) x = weightedH1Derivative φ k (W (j, i)) x
  rw [hx, hy]
  exact ((coordinateHessian_symmetric (hf i) x).apply j k).symm

theorem exists_weightedSuccessor_symmetric_approximation
    {φ : Space n → ℝ} {κ lam : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hlam : 0 < lam) {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (W : WeightedH1Family φ (Fin n × ι))
    (f : ι → Space n → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hd : ∀ j k i, (weightedH1Derivative φ j (W (k, i)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x => coordinateHessian (f i) x j k)
    (hscale : weightedFamilyCenteredGradient φ ι U ≠ 0 →
      lam ≤ (weightedSuccessorScale hφ hκ hlower U) ^ 2) :
    ∃ T : CenteredL2.Family (potentialMeasure φ) (Fin n × (Fin n × ι)),
      (∀ j k i, T (j, (k, i)) = T (k, (j, i))) ∧
      ‖weightedFamilyCenteredGradient φ (Fin n × ι)
        (weightedNormalizedSuccessor hφ hκ hlower U) - T‖ ^ 2 ≤
          weightedSuccessorHessianDefect hφ hκ hlower U W / lam := by
  by_cases hz : weightedFamilyCenteredGradient φ ι U = 0
  · refine ⟨0, fun _ _ _ => rfl, ?_⟩
    rw [weightedNormalizedSuccessor_eq_zero hφ hκ hlower U hz, map_zero, sub_zero, norm_zero,
      zero_pow (by norm_num)]
    exact div_nonneg (sq_nonneg _) hlam.le
  · let a := weightedSuccessorScale hφ hκ hlower U
    let T := a⁻¹ • weightedFamilyCenteredGradient φ (Fin n × ι) W
    refine ⟨T, ?_, ?_⟩
    · intro j k i
      have he := weightedFamilyHessian_symmetric W f hf hd j k i
      simp only [T, PiLp.smul_apply, weightedFamilyCenteredGradient_apply]
      rw [show weightedH1Derivative φ j (W (k, i)) = weightedH1Derivative φ k (W (j, i)) from he]
    · exact weightedSuccessor_centered_hessian_approximation hφ hκ hlower U W hlam
        (weightedSuccessorScale_pos hφ hκ hlower U hz) (hscale hz)

/-- BKL (38)--(40) for the actual successor, with a single attained eigenvalue
for all finite ranks. Both Hessian regularity and the scale bound are derived. -/
theorem exists_optimal_weightedSuccessor_symmetric_bounds
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    ∃ lam : ℝ, 0 < lam ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      ∀ (ι : Type*) [Fintype ι] (U : WeightedH1Family φ ι) (f : ι → Space n → ℝ),
        (∀ i, ContDiff ℝ 3 (f i)) →
        (∀ i, f i =ᵐ[volume] (weightedH1Value φ (U i) : Space n → ℝ)) →
        (∀ i, MemLp (weightedDiffusion φ (f i)) 2 (potentialMeasure φ)) →
        ∃ W : WeightedH1Family φ (Fin n × ι),
          weightedFamilyValue φ (Fin n × ι) W = weightedFamilyCenteredGradient φ ι U ∧
          (∀ j k i, (weightedH1Derivative φ j (W (k, i)) : Space n → ℝ)
            =ᵐ[potentialMeasure φ] fun x => coordinateHessian (f i) x j k) ∧
          ∃ T : CenteredL2.Family (potentialMeasure φ) (Fin n × (Fin n × ι)),
            (∀ j k i, T (j, (k, i)) = T (k, (j, i))) ∧
            ‖weightedFamilyCenteredGradient φ (Fin n × ι)
              (weightedNormalizedSuccessor hφ hκ hlower U) - T‖ ^ 2 ≤
                weightedSuccessorHessianDefect hφ hκ hlower U W / lam := by
  obtain ⟨lam, hlam, hCP, hscale⟩ := exists_optimal_weightedSuccessorScale_lower_bound hφ hκ hlower hn
  refine ⟨lam, hlam, hCP, ?_⟩
  intro ι _ U f hf hv hL
  obtain ⟨W, hW, hD, _, _, _⟩ :=
    exists_weightedFamily_hessian_of_diffusion_domain hφ hκ hlower U f hf hv hL
  exact ⟨W, hW, hD, exists_weightedSuccessor_symmetric_approximation hφ hκ hlower hlam U W f
    (fun i => (hf i).of_le (by norm_num)) hD (hscale ι U)⟩

end KLS
end

#print axioms KLS.weightedFamilyHessian_symmetric
#print axioms KLS.exists_optimal_weightedSuccessor_symmetric_bounds
