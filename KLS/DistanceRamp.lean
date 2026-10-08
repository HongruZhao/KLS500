import KLS.Definitions
import KLS.LocalRademacher

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal

noncomputable section
namespace KLS

/-- A genuine distance ramp, equal to one on the closure and zero outside the
open enlargement. Its estimates below do not assume that the set is closed. -/
def distanceRamp {n : ℕ} (A : Set (Space n)) (ε : ℝ) (x : Space n) : ℝ :=
  1 - min (Metric.infDist x A / ε) 1

theorem distanceRamp_nonneg {n : ℕ} (A : Set (Space n)) (ε : ℝ) (x : Space n) :
    0 ≤ distanceRamp A ε x := by
  unfold distanceRamp
  exact sub_nonneg.mpr (min_le_right _ _)

theorem distanceRamp_le_one {n : ℕ} (A : Set (Space n)) {ε : ℝ} (hε : 0 < ε)
    (x : Space n) : distanceRamp A ε x ≤ 1 := by
  unfold distanceRamp
  have := infDist_nonneg (x := x) (s := A)
  have : 0 ≤ min (infDist x A / ε) 1 := le_min (div_nonneg this hε.le) zero_le_one
  linarith

theorem distanceRamp_eq_one {n : ℕ} {A : Set (Space n)} {ε : ℝ} {x : Space n}
    (hx : x ∈ A) : distanceRamp A ε x = 1 := by
  simp [distanceRamp, infDist_zero_of_mem hx]

theorem distanceRamp_eq_zero {n : ℕ} {A : Set (Space n)} (hA : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε) {x : Space n} (hx : x ∉ thickening ε A) :
    distanceRamp A ε x = 0 := by
  have hdist : ε ≤ infDist x A :=
    not_lt.mp (fun h => hx ((mem_thickening_iff_infDist_lt hA).mpr h))
  have hdiv : 1 ≤ infDist x A / ε := (le_div_iff₀ hε).mpr (by simpa using hdist)
  simp [distanceRamp, min_eq_right hdiv]

theorem distanceRamp_lipschitz {n : ℕ} (A : Set (Space n)) {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal ε⁻¹) (distanceRamp A ε) := by
  have hd : LipschitzWith (Real.toNNReal ε⁻¹) (fun x : Space n => infDist x A / ε) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hε,
      Real.coe_toNNReal _ (inv_nonneg.mpr hε.le), mul_comm ε⁻¹, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using
      (lipschitz_infDist_pt A).dist_le_mul x y) hε.le
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [distanceRamp, dist_sub_left] using (hd.min_const 1).dist_le_mul x y

/-- Local extrema force the total derivative to vanish, including its default
zero at nondifferentiable points; absolute continuity is unnecessary. -/
theorem distanceRamp_gradient_eq_zero_of_mem {n : ℕ} {A : Set (Space n)}
    {ε : ℝ} (hε : 0 < ε) {x : Space n} (hx : x ∈ A) :
    gradient (distanceRamp A ε) x = 0 := by
  have he : IsLocalMax (distanceRamp A ε) x := Eventually.of_forall fun y => by
    rw [distanceRamp_eq_one hx]
    exact distanceRamp_le_one A hε y
  simp only [gradient, he.fderiv_eq_zero, map_zero]

theorem distanceRamp_gradient_eq_zero_of_notMem {n : ℕ} {A : Set (Space n)}
    (hA : A.Nonempty) {ε : ℝ} (hε : 0 < ε) {x : Space n}
    (hx : x ∉ thickening ε A) : gradient (distanceRamp A ε) x = 0 := by
  have he : IsLocalMin (distanceRamp A ε) x := Eventually.of_forall fun y => by
    rw [distanceRamp_eq_zero hA hε hx]
    exact distanceRamp_nonneg A ε y
  simp only [gradient, he.fderiv_eq_zero, map_zero]

theorem distanceRamp_gradient_bound {n : ℕ} {A : Set (Space n)} (hA : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε) (x : Space n) :
    ‖gradient (distanceRamp A ε) x‖ ≤
      (thickening ε A \ A).indicator (fun _ => ε⁻¹) x := by
  classical
  by_cases hx : x ∈ thickening ε A \ A
  · rw [Set.indicator_of_mem hx, norm_gradient_eq_norm_fderiv]
    simpa only [Real.coe_toNNReal _ (inv_nonneg.mpr hε.le)] using
      norm_fderiv_le_of_lipschitz ℝ (distanceRamp_lipschitz A hε) (x₀ := x)
  · rw [Set.indicator_of_notMem hx]
    by_cases hxA : x ∈ A
    · simp [distanceRamp_gradient_eq_zero_of_mem hε hxA]
    · have hxT : x ∉ thickening ε A := fun hxT => hx ⟨hxT, hxA⟩
      simp [distanceRamp_gradient_eq_zero_of_notMem hA hε hxT]

theorem distanceRamp_indicator_error {n : ℕ} {A : Set (Space n)} (hA : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε) (x : Space n) :
    |A.indicator (fun _ => (1 : ℝ)) x - distanceRamp A ε x| ≤
      (thickening ε A \ A).indicator (fun _ => (1 : ℝ)) x := by
  classical
  by_cases hxA : x ∈ A
  · simp [hxA, distanceRamp_eq_one hxA]
  · by_cases hxT : x ∈ thickening ε A
    · simp only [Set.indicator_of_notMem hxA, zero_sub, abs_neg,
        Set.indicator_of_mem (show x ∈ thickening ε A \ A from ⟨hxT, hxA⟩)]
      rw [abs_of_nonneg (distanceRamp_nonneg A ε x)]
      exact distanceRamp_le_one A hε x
    · simp [hxA, hxT, distanceRamp_eq_zero hA hε hxT]

theorem distanceRamp_integrable {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (A : Set (Space n)) {ε : ℝ} (hε : 0 < ε) : Integrable (distanceRamp A ε) μ := by
  apply (integrable_const (1 : ℝ)).mono' (distanceRamp_lipschitz A hε).continuous.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (distanceRamp_nonneg A ε x)]
    exact distanceRamp_le_one A hε x

end KLS
end
