import KLS.WeightedIntegrationByParts

/-!
# Coercivity of finite convex potentials with finite exponential mass

A fixed ball of uniformly positive density fits around the midpoint of
every point in a fixed sublevel. Finite-measure tightness prevents those
midpoints from escaping to infinity. Thus actual sublevels are compact,
and the potential attains its minimum.
-/

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

private lemma volume_ball_eq_center_zero (x : Space n) (r : ℝ) :
    volume (ball x r) = volume (ball (0 : Space n) r) := by
  have heq : (fun y : Space n => x + y) ⁻¹' ball x r = ball (0 : Space n) r := by
    ext y
    simp [Metric.mem_ball, dist_eq_norm]
  rw [← heq, measure_preimage_add]

/-- Every sublevel of the genuine potential is compact; coercivity is not an assumption. -/
theorem isCompact_sublevel_of_finite_potentialMeasure {φ : Space n → ℝ}
    (hφ : Continuous φ) (hconv : ConvexOn ℝ univ φ)
    [IsFiniteMeasure (potentialMeasure φ)] (c : ℝ) : IsCompact {x | φ x ≤ c} := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space n) 1).bddAbove_image hφ.continuousOn
  have hM' (z : Space n) (hz : ‖z‖ ≤ 1) : φ z ≤ M := by
    exact hM ⟨z, by simpa using hz, rfl⟩
  let C : ℝ := (c + M) / 2
  let δ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-C)) * volume (ball (0 : Space n) (1 / 2))
  have hδ : δ ≠ 0 := by
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      (measure_ball_pos volume (0 : Space n) (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  obtain ⟨K, _, hK, hKmass⟩ := (MeasurableSet.univ : MeasurableSet (univ : Set (Space n))).exists_isCompact_sdiff_lt
    (μ := potentialMeasure φ) (measure_ne_top _ _) hδ
  have hKmass' : potentialMeasure φ Kᶜ < δ := by
    convert hKmass using 2
    ext x
    exact (and_iff_right (mem_univ x)).symm
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hbound (y : Space n) (hy : φ y ≤ c) : ‖y‖ ≤ 2 * R + 1 := by
    by_contra hybound
    have hyfar : 2 * R + 1 < ‖y‖ := lt_of_not_ge hybound
    have hball : ball ((1 / 2 : ℝ) • y) (1 / 2) ⊆ Kᶜ := by
      intro z hz hzK
      have hdist : ‖z - (1 / 2 : ℝ) • y‖ < 1 / 2 := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hz
      have htri : ‖(1 / 2 : ℝ) • y‖ ≤ ‖z - (1 / 2 : ℝ) • y‖ + ‖z‖ := by
        calc
          _ = ‖z - (z - (1 / 2 : ℝ) • y)‖ := by congr 1; abel
          _ ≤ ‖z‖ + ‖z - (1 / 2 : ℝ) • y‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at htri
      have hzbound := hR z hzK
      linarith
    have hφball (z : Space n) (hz : z ∈ ball ((1 / 2 : ℝ) • y) (1 / 2)) : φ z ≤ C := by
      let v : Space n := (2 : ℝ) • z - y
      have hv : ‖v‖ ≤ 1 := by
        have heq : v = (2 : ℝ) • (z - (1 / 2 : ℝ) • y) := by dsimp [v]; module
        rw [heq, norm_smul]
        have hd : ‖z - (1 / 2 : ℝ) • y‖ < 1 / 2 := by
          simpa only [Metric.mem_ball, dist_eq_norm] using hz
        norm_num
        linarith
      have hmid : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • v = z := by dsimp [v]; module
      have hm := hconv.2 (mem_univ y) (mem_univ v)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      rw [hmid] at hm
      have hvM := hM' v hv
      dsimp [C]
      simp only [smul_eq_mul] at hm
      linarith
    have hmass : δ ≤ potentialMeasure φ (ball ((1 / 2 : ℝ) • y) (1 / 2)) := by
      rw [potentialMeasure, withDensity_apply _ isOpen_ball.measurableSet]
      calc
        δ = ∫⁻ z in ball ((1 / 2 : ℝ) • y) (1 / 2), ENNReal.ofReal (Real.exp (-C)) := by
          rw [lintegral_const, Measure.restrict_apply_univ, volume_ball_eq_center_zero]
        _ ≤ ∫⁻ z in ball ((1 / 2 : ℝ) • y) (1 / 2), ENNReal.ofReal (Real.exp (-φ z)) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hφball z hz)))
    exact (not_lt_of_ge (hmass.trans (measure_mono hball))) hKmass'
  exact isCompact_iff_isClosed_bounded.mpr ⟨isClosed_le hφ continuous_const,
    isBounded_iff_forall_norm_le.mpr ⟨2 * R + 1, fun y hy => hbound y hy⟩⟩

/-- The potential tends to infinity outside compact sets. -/
theorem tendsto_potential_cocompact_atTop {φ : Space n → ℝ}
    (hφ : Continuous φ) (hconv : ConvexOn ℝ univ φ)
    [IsFiniteMeasure (potentialMeasure φ)] : Tendsto φ (cocompact (Space n)) atTop := by
  apply Filter.tendsto_atTop.2
  intro c
  filter_upwards [(isCompact_sublevel_of_finite_potentialMeasure hφ hconv c).compl_mem_cocompact] with x hx
  exact (lt_of_not_ge (show ¬φ x ≤ c from hx)).le

/-- A genuine global minimizer exists from finite exponential mass and convexity. -/
theorem exists_minimizer_of_finite_potentialMeasure {φ : Space n → ℝ}
    (hφ : Continuous φ) (hconv : ConvexOn ℝ univ φ)
    [IsFiniteMeasure (potentialMeasure φ)] : ∃ x₀, ∀ x, φ x₀ ≤ φ x :=
  hφ.exists_forall_le (tendsto_potential_cocompact_atTop hφ hconv)

end KLS
end

#print axioms KLS.isCompact_sublevel_of_finite_potentialMeasure
#print axioms KLS.tendsto_potential_cocompact_atTop
#print axioms KLS.exists_minimizer_of_finite_potentialMeasure
