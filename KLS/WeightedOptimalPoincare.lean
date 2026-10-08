import KLS.WeightedFaithfulGraph
import KLS.WeightedRayleighEquation
import KLS.OptimalConstants

/-! The actual attained Rayleigh value equals the reciprocal of the faithful optimal Poincaré constant. -/

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped Topology ContDiff ENNReal NNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

lemma energy_lt_top_of_memLp_coordinateDerivative {μ : Measure (Space n)} {f : Space n → ℝ}
    (hd : ∀ i : Fin n, MemLp (coordinateDerivative f i) 2 μ) : energy μ f < ⊤ := by
  have hgrad : (fun x => ‖gradient f x‖ ^ 2) =
      fun x => ∑ i : Fin n, coordinateDerivative f i x ^ 2 := by
    funext x
    simp_rw [EuclideanSpace.real_norm_sq_eq, coordinateDerivative_eq_gradient]
  have hi : Integrable (fun x => ‖gradient f x‖ ^ 2) μ := by
    rw [hgrad]
    exact integrable_finsetSum Finset.univ (fun i _ => (hd i).integrable_sq)
  exact lt_top_iff_ne_top.mpr <| (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    hi.aestronglyMeasurable (Eventually.of_forall fun x => sq_nonneg ‖gradient f x‖)).mpr hi

/-- Every faithful Poincaré constant already bounds the genuine compact smooth core. -/
theorem smoothCenteredGradientGraphSet_bound_of_poincareConstant
    {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : Continuous φ) {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ))
    {W : WeightedEnergyAmbient φ} (hW : W ∈ smoothCenteredGradientGraphSet φ) :
    ‖W 0‖ ^ 2 ≤ (C : ℝ) * ∑ i : Fin n, ‖W i.succ‖ ^ 2 := by
  obtain ⟨f, hf, hc, hv, hd⟩ := hW
  have hft : LocallyLipschitzTests (potentialMeasure φ) f :=
    ⟨(hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)).locallyLipschitz,
      memLp_of_continuous_hasCompactSupport hφ hf.continuous hc⟩
  have hd2 (i : Fin n) : MemLp (coordinateDerivative f i) 2 (potentialMeasure φ) :=
    (memLp_congr_ae (hd i)).mp (Lp.memLp (W i.succ))
  have he := energy_lt_top_of_memLp_coordinateDerivative hd2
  let U : WeightedCenteredH1 φ := ⟨W, Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨f, hf, hc, hv, hd⟩)⟩
  have hnorm := weightedH1_faithful_test_norms hft he (U := U) hv hd
  have hb := hC f hft
  rw [hnorm.2.2.1, hnorm.2.2.2] at hb
  have hB : 0 ≤ weightedEnergyForm φ U U := by
    rw [weightedEnergyForm_self]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ht := ENNReal.toReal_mono (by finiteness) hb
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal hB] at ht
  simpa only [weightedEnergyForm_self, weightedH1Value_apply, weightedH1Derivative_apply] using ht

/-- Faithful constants pass to the closed graph, so testing a minimizer needs no classical representative. -/
theorem weightedH1_bound_of_poincareConstant {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ)) (U : WeightedCenteredH1 φ) :
    ‖weightedH1Value φ U‖ ^ 2 ≤ (C : ℝ) * weightedEnergyForm φ U U := by
  have hclosed : IsClosed {W : WeightedEnergyAmbient φ |
      ‖W 0‖ ^ 2 ≤ (C : ℝ) * ∑ i : Fin n, ‖W i.succ‖ ^ 2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hcore : smoothCenteredGradientGraphSet φ ⊆ {W : WeightedEnergyAmbient φ |
      ‖W 0‖ ^ 2 ≤ (C : ℝ) * ∑ i : Fin n, ‖W i.succ‖ ^ 2} :=
    fun _ hW => smoothCenteredGradientGraphSet_bound_of_poincareConstant hφ hC hW
  have hU : (U : WeightedEnergyAmbient φ) ∈ closure (smoothCenteredGradientGraphSet φ) := by
    rw [← weightedCenteredGradientGraph_coe_eq_closure hφ]
    exact U.property
  simpa only [Set.mem_ofPred_eq, weightedEnergyForm_self, weightedH1Value_apply, weightedH1Derivative_apply] using (closure_minimal hcore hclosed) hU

/-- The positive Rayleigh reciprocal is an admissible constant for every original locally
Lipschitz L² test. Infinite energy is handled in the extended nonnegative reals. -/
theorem weightedRayleigh_inv_mem_poincareConstants {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    {U : WeightedCenteredH1 φ} (hpos : 0 < weightedEnergyForm φ U U)
    (hmin : ∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
      weightedEnergyForm φ U U ≤ weightedEnergyForm φ V V) :
    Real.toNNReal (weightedEnergyForm φ U U)⁻¹ ∈ poincareConstants (potentialMeasure φ) := by
  intro f hf
  by_cases he : energy (potentialMeasure φ) f < ⊤
  · obtain ⟨V, _, _, hv, hd⟩ := exists_weightedH1_of_faithful_test_with_norms hφ hf he
    have hr := weightedRayleigh_minimizer_lower_bound hmin V
    have hreal : ‖weightedH1Value φ V‖ ^ 2 ≤
        (weightedEnergyForm φ U U)⁻¹ * weightedEnergyForm φ V V := by
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hpos).mpr (by nlinarith [hr])
    rw [hv, hd]
    change ENNReal.ofReal (‖weightedH1Value φ V‖ ^ 2) ≤
      ENNReal.ofReal (weightedEnergyForm φ U U)⁻¹ * ENNReal.ofReal (weightedEnergyForm φ V V)
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
    exact ENNReal.ofReal_le_ofReal hreal
  · have htop : energy (potentialMeasure φ) f = ⊤ := top_le_iff.mp (not_lt.mp he)
    have hinv : ENNReal.ofReal (weightedEnergyForm φ U U)⁻¹ ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr hpos)).ne'
    change variance (potentialMeasure φ) f ≤ ENNReal.ofReal (weightedEnergyForm φ U U)⁻¹ * _
    rw [htop, ENNReal.mul_top hinv]
    exact le_top

/-- Exact agreement with the faithful infimum over all original locally Lipschitz L² tests. -/
theorem poincareConstant_eq_inv_weightedRayleigh {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    {U : WeightedCenteredH1 φ} (hU : ‖weightedH1Value φ U‖ = 1)
    (hpos : 0 < weightedEnergyForm φ U U)
    (hmin : ∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
      weightedEnergyForm φ U U ≤ weightedEnergyForm φ V V) :
    poincareConstant (potentialMeasure φ) = ENNReal.ofReal (weightedEnergyForm φ U U)⁻¹ := by
  apply le_antisymm
  · exact poincareConstant_le_of_mem (weightedRayleigh_inv_mem_poincareConstants hφ hpos hmin)
  · apply le_poincareConstant_of_forall
    intro C hC
    have hb := weightedH1_bound_of_poincareConstant hφ hC U
    rw [hU, one_pow] at hb
    have hr : (weightedEnergyForm φ U U)⁻¹ ≤ (C : ℝ) := by
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hpos).mpr (by nlinarith [hb])
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr

/-- Each genuinely confined normalized potential has an attained positive first weak eigenvalue
whose reciprocal is its faithful optimal Poincaré constant. This is a per-measure result. -/
theorem exists_positive_weighted_eigenpair_with_optimal_poincare {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    ∃ (lam : ℝ) (U : WeightedCenteredH1 φ), κ ≤ lam ∧ 0 < lam ∧
      ‖weightedH1Value φ U‖ = 1 ∧
      (∀ V : WeightedCenteredH1 φ,
        weightedEnergyForm φ U V = lam * inner ℝ (weightedH1Value φ U) (weightedH1Value φ V)) ∧
      (∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
        lam ≤ weightedEnergyForm φ V V) ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ := by
  obtain ⟨lam, U, hk, hp, hu, hw, hm⟩ := exists_positive_weighted_weak_eigenpair hn hφ hκ hlower
  have he : weightedEnergyForm φ U U = lam := by
    simpa only [real_inner_self_eq_norm_sq, hu, one_pow, mul_one] using hw U
  have hm' : ∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
      weightedEnergyForm φ U U ≤ weightedEnergyForm φ V V := by rwa [he]
  refine ⟨lam, U, hk, hp, hu, hw, hm, ?_⟩
  simpa only [he] using poincareConstant_eq_inv_weightedRayleigh hφ.continuous hu (he ▸ hp) hm'

end KLS
end

#print axioms KLS.weightedH1_bound_of_poincareConstant
#print axioms KLS.poincareConstant_eq_inv_weightedRayleigh
#print axioms KLS.exists_positive_weighted_eigenpair_with_optimal_poincare
