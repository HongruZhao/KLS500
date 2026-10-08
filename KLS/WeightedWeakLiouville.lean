import KLS.WeakLocalPairing
import KLS.WeakDistributionConstant

/-!
# Full-space weak weighted L² Liouville and actual diffusion-range density

Every compact cutoff has an actual local weak gradient. Its Caccioppoli
bound controls each fixed distributional derivative pairing. Expanding
cutoffs make those pairings zero; actual mollification then gives an
almost-everywhere constant. No elliptic regularity hypothesis is assumed.

The potential is finite and C² on all of Euclidean space. This theorem does
not by itself pass to a potential infinite off a convex support.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff ENNReal Topology

noncomputable section
namespace KLS
variable {n : ℕ}

lemma smoothCutoff_contDiff_top (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (smoothCutoff n k) :=
  (unitCutoff n).contDiff.comp (contDiff_id.const_smul (cutoffScale k))

lemma smoothCutoff_eventually_one_on_compact {K : Set (Space n)} (hK : IsCompact K) :
    ∀ᶠ k in atTop, ∀ x ∈ K, smoothCutoff n k x = 1 := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image continuous_norm.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt M
  filter_upwards [eventually_ge_atTop N] with k hk
  intro x hx
  apply (unitCutoff n).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (cutoffScale_pos k)]
  change cutoffScale k * ‖x‖ ≤ 1
  have hn : ‖x‖ ≤ (k : ℝ) + 1 :=
    (hM (mem_image_of_mem _ hx)).trans
      (hN.le.trans ((Nat.cast_le.mpr hk).trans (by linarith)))
  calc
    cutoffScale k * ‖x‖ ≤ cutoffScale k * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hn (cutoffScale_pos k).le
    _ = 1 := inv_mul_cancel₀ (by positivity)

/-- A fixed distributional derivative pairing is controlled by an arbitrarily large cutoff. -/
theorem weighted_annihilator_test_pairing_sq_le {φ χ ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hχ1 : ∀ x ∈ tsupport ψ, χ x = 1) {a : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ x, ‖gradient χ x‖ ≤ a) (i : Fin n) :
    (∫ x, u x * coordinateDerivative ψ i x) ^ 2 ≤
      (4 * ((n : ℝ) * (a ^ 2 * ∫ x, u x ^ 2 ∂potentialMeasure φ))) *
        (∫ x, Real.exp (φ x) * ψ x ^ 2) := by
  obtain ⟨f, G, hf, hfc, hG, heq, henergy⟩ :=
    weighted_annihilator_exists_local_energy hφ u hu hχ hχc
  have hpair := weak_cutoff_test_pairing_sq_le hφ.continuous (G i) (hG i)
    hχ.continuous hχc hψ hψc hχ1
  have hfu : (∫ x, u x * coordinateDerivative ψ i x) =
      ∫ x, f x * coordinateDerivative ψ i x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport ψ
      · have hxχ : x ∈ tsupport χ := subset_tsupport χ (by simp [Function.mem_support, hχ1 x hx])
        rw [heq x hxχ]
      · have hd : coordinateDerivative ψ i x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hi => hx (tsupport_coordinateDerivative_subset ψ i hi))
        simp [hd]
  rw [hfu]
  have hsingle : (∫ x, Real.exp (-φ x) * χ x ^ 2 * (G i x) ^ 2) ≤
      ∑ j, ∫ x, Real.exp (-φ x) * χ x ^ 2 * (G j x) ^ 2 := by
    apply Finset.single_le_sum (f := fun j => ∫ x, Real.exp (-φ x) * χ x ^ 2 * (G j x) ^ 2)
    · intro j _
      apply integral_nonneg
      intro x
      positivity
    · exact Finset.mem_univ i
  have hsum : (∑ j, ∫ x, Real.exp (-φ x) * u x ^ 2 * (coordinateDerivative χ j x) ^ 2) ≤
      (n : ℝ) * (a ^ 2 * ∫ x, u x ^ 2 ∂potentialMeasure φ) := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      integral_weighted_coordinate_sq_le_L2 hφ.continuous u (hχ.of_le (by norm_num)) ha hbound j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs
  have hb := hsingle.trans (henergy.trans (mul_le_mul_of_nonneg_left hsum (by norm_num)))
  exact hpair.trans (mul_le_mul_of_nonneg_right hb (integral_nonneg (fun x => by positivity)))

/-- Expanding actual cutoffs make every distributional derivative pairing zero. -/
theorem weighted_annihilator_zero_distributional_gradient {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0) :
    ∀ i (ψ : Space n → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, u x * coordinateDerivative ψ i x) = 0 := by
  intro i ψ hψ hψc
  obtain ⟨K, hK, hbound⟩ := smoothCutoff_gradient_bound (n := n)
  have hsmall : Tendsto
      (fun k => (4 * ((n : ℝ) * ((cutoffScale k * K) ^ 2 *
        ∫ x, u x ^ 2 ∂potentialMeasure φ))) * (∫ x, Real.exp (φ x) * ψ x ^ 2))
      atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (((((cutoffScale_tendsto_zero.mul_const K).pow 2).mul_const
        (∫ x, u x ^ 2 ∂potentialMeasure φ)).const_mul (n : ℝ)).const_mul 4).mul_const
          (∫ x, Real.exp (φ x) * ψ x ^ 2)
  have he : ∀ᶠ k in atTop,
      (∫ x, u x * coordinateDerivative ψ i x) ^ 2 ≤
        (4 * ((n : ℝ) * ((cutoffScale k * K) ^ 2 *
          ∫ x, u x ^ 2 ∂potentialMeasure φ))) * (∫ x, Real.exp (φ x) * ψ x ^ 2) := by
    filter_upwards [smoothCutoff_eventually_one_on_compact hψc] with k hk
    exact weighted_annihilator_test_pairing_sq_le hφ u hu
      ((smoothCutoff_contDiff_top k).of_le (by simp)) (smoothCutoff_hasCompactSupport k)
      hψ hψc hk (mul_nonneg (cutoffScale_pos k).le hK) (hbound k) i
  have hz : (∫ x, u x * coordinateDerivative ψ i x) ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hsmall he
  nlinarith [sq_nonneg (∫ x, u x * coordinateDerivative ψ i x)]

/-- Full-space weak weighted L² Liouville, with no regularity assumption on the solution. -/
theorem weakDiffusionLiouville_of_contDiff {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) : WeakDiffusionLiouville φ := by
  intro u hu
  have hloc := KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure (Lp.memLp u) hφ.continuous
  obtain ⟨c, hc⟩ := ae_eq_const_of_zero_distributional_gradient hloc
    (weighted_annihilator_zero_distributional_gradient hφ u hu)
  exact ⟨c, (withDensity_absolutelyContinuous volume
    (fun x => ENNReal.ofReal (Real.exp (-φ x)))).ae_eq hc⟩

/-- Genuine L² norm density of the actual compact diffusion range is now unconditional for C² potentials. -/
theorem diffusionRangeDense_of_contDiff {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) : DiffusionRangeDense φ :=
  diffusionRangeDense_of_weakDiffusionLiouville hφ (weakDiffusionLiouville_of_contDiff hφ)

end KLS
end

#print axioms KLS.weighted_annihilator_test_pairing_sq_le
#print axioms KLS.weighted_annihilator_zero_distributional_gradient
#print axioms KLS.weakDiffusionLiouville_of_contDiff
#print axioms KLS.diffusionRangeDense_of_contDiff
