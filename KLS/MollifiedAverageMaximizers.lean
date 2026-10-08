import KLS.MollifiedTranslatedAverage
import KLS.MollificationLocalization

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

lemma abs_mollified_translatedAverage_sub_le {u : Space n → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L u) (k : ℕ) (h x : Space n) :
    |translatedAverage (mollify k u) h x - translatedAverage u h x| ≤
      L * (2 * cutoffScale k) := by
  have hp := dist_mollify_le_of_lipschitz hLip k (x+h)
  have hm := dist_mollify_le_of_lipschitz hLip k (x-h)
  rw [Real.dist_eq] at hp hm
  have hp' := abs_le.mp hp
  have hm' := abs_le.mp hm
  unfold translatedAverage
  apply abs_le.mpr
  constructor <;> linarith

lemma translatedAverage_mollify_tendsto_at_moving_points
    {u : Space n → ℝ} (hu : Continuous u) (h : Space n)
    {x : ℕ → Space n} {x₀ : Space n} (hx : Tendsto x atTop (𝓝 x₀))
    {s : ℕ → ℕ} (hs : Tendsto s atTop atTop) :
    Tendsto (fun k => translatedAverage (mollify (s k) u) h (x k))
      atTop (𝓝 (translatedAverage u h x₀)) := by
  exact ((mollify_tendsto_at_moving_points hu (hx.add_const h) hs).add
    (mollify_tendsto_at_moving_points hu (hx.sub_const h) hs)).div_const 2

/-- Actual maximizers of the smoothed translated averages exist and all lie
in one compact sublevel of the original finite-mass potential. -/
theorem exists_mollified_average_maximizers_bounded
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) [IsFiniteMeasure (potentialMeasure u)]
    (h : Space n) {α : ℝ} (hα : 1 < α) :
    ∃ x : ℕ → Space n, ∃ C : ℝ,
      (∀ k y, translatedAverage (mollify k u) h y - α * u y ≤
        translatedAverage (mollify k u) h (x k) - α * u (x k)) ∧
      (∀ k, u (x k) ≤ C) := by
  have herr (k : ℕ) (y : Space n) :
      |translatedAverage (mollify k u) h y - translatedAverage u h y| ≤ 2 * L := by
    apply (abs_mollified_translatedAverage_sub_le hLip k h y).trans
    have hh := mul_le_mul_of_nonneg_left (cutoffScale_le_one k) L.coe_nonneg
    nlinarith
  have hupp (k : ℕ) (y : Space n) :
      translatedAverage (mollify k u) h y ≤ u y + L * ‖h‖ + 2 * L := by
    have he := (abs_le.mp (herr k y)).2
    have hd := symmetricSecondDifference_le_of_lipschitz hLip h y
    dsimp [translatedAverage,symmetricSecondDifference] at *
    linarith
  have hex (k : ℕ) : ∃ x₀ : Space n, ∀ y,
      translatedAverage (mollify k u) h y - α * u y ≤
        translatedAverage (mollify k u) h x₀ - α * u x₀ := by
    have hg : Continuous (translatedAverage (mollify k u) h) :=
      (translatedAverage_contDiff (mollify_contDiff hLip.continuous.locallyIntegrable k) h).continuous
    apply (hg.sub (continuous_const.mul hLip.continuous)).exists_forall_ge
    apply tendsto_atBot.2
    intro b
    filter_upwards [(tendsto_potential_cocompact_atTop hLip.continuous hc).eventually
      (eventually_ge_atTop ((L * ‖h‖ + 2 * L - b) / (α-1)))] with y hy
    have hm := (div_le_iff₀ (sub_pos.mpr hα)).mp hy
    have hb := hupp k y
    change translatedAverage (mollify k u) h y - α * u y ≤ b
    nlinarith
  choose x hx using hex
  refine ⟨x,(L * ‖h‖ + 4 * L - translatedAverage u h 0 + α * u 0) / (α-1),hx,?_⟩
  intro k
  have hzero := hx k 0
  have hlo := (abs_le.mp (herr k 0)).1
  have hhi := hupp k (x k)
  apply (le_div_iff₀ (sub_pos.mpr hα)).mpr
  nlinarith

/-- A subsequence of the actual smooth maxima converges to an actual maximum
of the original translated average. -/
theorem exists_mollified_average_maximum_subsequence
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) [IsFiniteMeasure (potentialMeasure u)]
    (h : Space n) {α : ℝ} (hα : 1 < α) :
    ∃ x : ℕ → Space n, ∃ s : ℕ → ℕ, ∃ x₀ : Space n,
      StrictMono s ∧ Tendsto (fun k => x (s k)) atTop (𝓝 x₀) ∧
      (∀ k y, translatedAverage (mollify k u) h y - α * u y ≤
        translatedAverage (mollify k u) h (x k) - α * u (x k)) ∧
      (∀ y, translatedAverage u h y - α * u y ≤
        translatedAverage u h x₀ - α * u x₀) := by
  obtain ⟨x,C,hmax,hbound⟩ := exists_mollified_average_maximizers_bounded hLip hc h hα
  obtain ⟨x₀,_,s,hs,hlim⟩ :=
    (isCompact_sublevel_of_finite_potentialMeasure hLip.continuous hc C).tendsto_subseq hbound
  refine ⟨x,s,x₀,hs,hlim,hmax,?_⟩
  intro y
  have hl := translatedAverage_mollify_tendsto_at_moving_points hLip.continuous h
    (tendsto_const_nhds (x := y)) hs.tendsto_atTop
  have hr := translatedAverage_mollify_tendsto_at_moving_points hLip.continuous h hlim hs.tendsto_atTop
  exact le_of_tendsto_of_tendsto
    (hl.sub_const (α * u y)) (hr.sub ((hLip.continuous.tendsto x₀ |>.comp hlim).const_mul α))
    (Eventually.of_forall fun k => hmax (s k) y)

end KLS
end
