import KLS.CenteredSectionEngulfing
import KLS.MomentConjugateInterior

/-! Uniform local engulfing for the actual weak moment potential. The same
constant works for all doubled sections contained in a fixed compact source
region; the density bounds are derived from the actual transport equation. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem closedCenteredSection_mono_height
    (u : Space n → ℝ) (x p : Space n) {h H : ℝ} (hh : h ≤ H) :
    closedCenteredSection u x p h ⊆ closedCenteredSection u x p H := by
  intro y hy
  change u y ≤ u x + inner ℝ p (y - x) + h at hy
  change u y ≤ u x + inner ℝ p (y - x) + H
  linarith

/-- Two-center containment at comparable heights. Any point in the original
height-h section may be the new center, including its minimum. The sole
localization condition is that the actual doubled section lies in Q. -/
theorem exists_uniform_moment_section_engulfing_on_compact
    (hn : 0 < n) {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {T : Set (Space n)} (hT : MeasurableSet T) (hTc : Convex ℝ T)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict T)
    {Q : Set (Space n)} (hQ : IsCompact Q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x₀ p₀ : Space n) (h : ℝ), p₀ ∈ convexSubgradient u x₀ → 0 < h →
        closedCenteredSection u x₀ p₀ (2 * h) ⊆ Q →
        ∀ x ∈ closedCenteredSection u x₀ p₀ h, ∀ p ∈ convexSubgradient u x,
          closedCenteredSection u x₀ p₀ h ⊆ closedCenteredSection u x p (C * h) := by
  obtain ⟨a, b, ha, hatop, hb, hbtop, hbounds⟩ :=
    exists_local_subgradient_volume_bounds_sigmaCompact hLip hc hV hT hTc hpush hQ
  let C : ℝ := 2 * sectionEngulfingConstant n a b (1 / 2)
  have hC : 0 < C := mul_pos zero_lt_two
    (sectionEngulfingConstant_pos hn ha hatop hb hbtop (by norm_num))
  refine ⟨C, hC, ?_⟩
  intro x₀ p₀ h hp₀ hh hSQ x hx p hp
  have hpD := moment_convexSubgradient_subset_interior_domain hLip hc hV hT hTc hpush x₀ hp₀
  have hlower : ∀ S : Set (Space n), IsCompact S → S ⊆ closedCenteredSection u x₀ p₀ (2 * h) →
      a * volume S ≤ volume (convexSubgradientImage u S) :=
    fun S hS hSS => (hbounds S hS.isSigmaCompact (hSS.trans hSQ)).1
  have hupper : ∀ S : Set (Space n), IsOpen S → S ⊆ closedCenteredSection u x₀ p₀ (2 * h) →
      volume (convexSubgradientImage u S) ≤ b * volume S :=
    fun S hS hSS => (hbounds S (isSigmaCompact_of_isOpen_space hS) (hSS.trans hSQ)).2
  have hx' : x ∈ closedCenteredSection u x₀ p₀ ((1 - (1 / 2 : ℝ)) * (2 * h)) := by
    have heq : (1 - (1 / 2 : ℝ)) * (2 * h) = h := by ring
    rw [heq]
    exact hx
  have hh' := closedCenteredSection_subset_recentered hn ha hatop hb hbtop (by norm_num : 0 < (1 / 2 : ℝ))
    hLip.continuous hc hp₀ hpD (mul_pos zero_lt_two hh) hlower hupper hx' hp
  have hheight : sectionEngulfingConstant n a b (1 / 2) * (2 * h) = C * h := by dsimp [C]; ring
  rw [hheight] at hh'
  exact (closedCenteredSection_mono_height u x₀ p₀ (by linarith : h ≤ 2 * h)).trans hh'

end KLS
end

#print axioms KLS.exists_uniform_moment_section_engulfing_on_compact
