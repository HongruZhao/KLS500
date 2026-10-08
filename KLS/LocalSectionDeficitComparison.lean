import KLS.SectionDeficitContraction

/-! Actual two-center engulfing supplies opposite-deficit comparison whenever
the relevant small sections remain in one compact controlled region. The
quantitative localization inequality is stated explicitly. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem supportDeficit_le_of_lipschitz
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    {x p : Space n} (hp : p ∈ convexSubgradient u x) (y : Space n) :
    supportDeficit u x p y ≤ 2 * (L : ℝ) * ‖y - x‖ := by
  have hnorm := norm_le_of_mem_convexSubgradient hLip hp
  have hdiff : u y - u x ≤ (L : ℝ) * ‖y - x‖ := by
    have hh := hLip.dist_le_mul y x
    rw [Real.dist_eq, dist_eq_norm] at hh
    exact (le_abs_self _).trans hh
  have hinner : -inner ℝ p (y - x) ≤ (L : ℝ) * ‖y - x‖ :=
    (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)))
  dsimp [supportDeficit]
  linarith

theorem exists_uniform_moment_deficit_comparison_of_small_sections
    (hn : 0 < n) {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {T : Set (Space n)} (hT : MeasurableSet T) (hTc : Convex ℝ T)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict T)
    {Q : Set (Space n)} (hQ : IsCompact Q)
    {c : Space n} {r t : ℝ} (hscale : 8 * (L : ℝ) * r ≤ t)
    (hsmall : ∀ x ∈ closedBall c r, ∀ p ∈ convexSubgradient u x,
      ∀ h : ℝ, 0 < h → h ≤ t → closedCenteredSection u x p h ⊆ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      ∀ p ∈ convexSubgradient u x, ∀ q ∈ convexSubgradient u y,
        supportDeficit u x p y ≤ C * supportDeficit u y q x := by
  obtain ⟨C, hC, hengulf⟩ := exists_uniform_moment_section_engulfing_on_compact
    hn hLip hc hV hT hTc hpush hQ
  have hstrict := moment_strictConvexOn hLip hc hV hT hTc hpush
  refine ⟨C, hC, ?_⟩
  intro x hx y hy p hp q hq
  by_cases hxy : x = y
  · subst y
    simp only [supportDeficit_self, mul_zero, le_refl]
  let h := supportDeficit u y q x
  have hh : 0 < h := by
    have hs := strict_support_inequality_of_strictConvexOn hstrict hq (fun heq => hxy heq.symm)
    dsimp [h, supportDeficit]
    linarith
  have hdist : ‖x - y‖ ≤ 2 * r := by
    have hxn : ‖x - c‖ ≤ r := hx
    have hyn : ‖y - c‖ ≤ r := hy
    have hh := norm_sub_le_norm_sub_add_norm_sub x c y
    rw [norm_sub_rev c y] at hh
    linarith
  have hhsize : 2 * h ≤ t := by
    have hs := supportDeficit_le_of_lipschitz hLip hq x
    have hmul := mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ 2 * (L : ℝ))
    dsimp [h]
    nlinarith
  have hSQ := hsmall y hy q hq (2 * h) (mul_pos zero_lt_two hh) hhsize
  have hxS : x ∈ closedCenteredSection u y q h := by
    change u x ≤ u y + inner ℝ q (x - y) + h
    dsimp [h, supportDeficit]
    linarith
  have hyS : y ∈ closedCenteredSection u y q h := by
    change u y ≤ u y + inner ℝ q (y - y) + h
    simp only [sub_self, inner_zero_right, add_zero]
    linarith
  have hybig := hengulf y q h hq hh hSQ x hxS p hp hyS
  change u y ≤ u x + inner ℝ p (y - x) + C * h at hybig
  dsimp [supportDeficit]
  change u y - u x - inner ℝ p (y - x) ≤ C * h
  linarith

end KLS
end

#print axioms KLS.supportDeficit_le_of_lipschitz
#print axioms KLS.exists_uniform_moment_deficit_comparison_of_small_sections
