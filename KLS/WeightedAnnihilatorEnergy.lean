import KLS.WeightedWeakEnergy

/-!
# Actual local energy bounds for weighted L² annihilators

A larger compact cutoff is constructed explicitly to equal one on the
desired compact region. The proved Sobolev localization and weak energy
identity then give an actual local gradient bound without regularity or
global weak-gradient assumptions.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff ENNReal Topology

noncomputable section
namespace KLS
variable {n : ℕ}

theorem exists_smooth_compact_one_on_compact {K : Set (Space n)} (hK : IsCompact K) :
    ∃ η : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ ∀ x ∈ K, η x = 1 := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let b : ContDiffBump (0 : Space n) :=
    ⟨|M| + 1, |M| + 2, by positivity, by linarith⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_⟩
  intro x hx
  apply b.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (hM (mem_image_of_mem _ hx)).trans ((le_abs_self M).trans (by dsimp [b]; linarith))

/-- The cutoff and its actual weak derivatives are constructed from the original annihilator. -/
theorem weighted_annihilator_exists_local_energy {φ χ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ))
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
  choose G hG using fun i => weighted_annihilator_compact_square_hasWeakDerivative hφ u hu
    (hη.of_le (by simp)) hηc i
  have hweak := weighted_annihilator_localized_weak_equation hφ u hu hf G hG hχ hc heq
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

lemma integral_weighted_coordinate_sq_le_L2 {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hχ : ContDiff ℝ 1 χ) {a : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ x, ‖gradient χ x‖ ≤ a) (i : Fin n) :
    (∫ x, Real.exp (-φ x) * u x ^ 2 * (coordinateDerivative χ i x) ^ 2) ≤
      a ^ 2 * ∫ x, u x ^ 2 ∂potentialMeasure φ := by
  have hd (x : Space n) : ‖coordinateDerivative χ i x‖ ≤ a := by
    rw [coordinateDerivative_eq_gradient]
    exact (PiLp.norm_apply_le (gradient χ x) i).trans (hbound x)
  have hD : MemLp (coordinateDerivative χ i) ⊤ (potentialMeasure φ) :=
    memLp_top_of_bound (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous.aestronglyMeasurable a
      (Eventually.of_forall hd)
  have hmul : MemLp (fun x => u x * coordinateDerivative χ i x) 2 (potentialMeasure φ) :=
    (Lp.memLp u).mul hD
  have hi : Integrable (fun x => u x ^ 2 * (coordinateDerivative χ i x) ^ 2)
      (potentialMeasure φ) := by
    convert hmul.integrable_sq using 1
    funext x
    ring
  have he : (∫ x, Real.exp (-φ x) * u x ^ 2 * (coordinateDerivative χ i x) ^ 2) =
      ∫ x, u x ^ 2 * (coordinateDerivative χ i x) ^ 2 ∂potentialMeasure φ := by
    rw [integral_potentialMeasure hφ.measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; ring
  rw [he, ← integral_const_mul]
  apply integral_mono hi ((Lp.memLp u).integrable_sq.const_mul (a ^ 2))
  intro x
  have hd2 : (coordinateDerivative χ i x) ^ 2 ≤ a ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) (hd x) 2
    simpa only [Real.norm_eq_abs, sq_abs] using this
  nlinarith [mul_le_mul_of_nonneg_left hd2 (sq_nonneg (u x))]

end KLS
end

#print axioms KLS.exists_smooth_compact_one_on_compact
#print axioms KLS.weighted_annihilator_exists_local_energy
#print axioms KLS.integral_weighted_coordinate_sq_le_L2
