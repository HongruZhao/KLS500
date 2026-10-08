import KLS.MomentVariationalCompactness

/-!
# Attainment of the normalized moment-measure variational functional

For an actual isotropic probability law with bounded support, this file
constructs a finite-energy maximizer among normalized convex potentials with
a specified common Lipschitz bound. A radial norm potential is an actual
finite-energy competitor. Coercivity puts all competitive values in one
compact energy sublevel; upper semicontinuity then attains the maximum.

This is variational attainment, not yet the Euler--Lagrange transport identity
or a smooth Monge--Ampere solution.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

theorem IsIsotropic.exists_maximizer_on_momentEnergy_sublevel
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (L : ℝ≥0) {M : ℝ} (hM : 0 ≤ M)
    (hne : (normalizedMomentEnergySublevel n L μ (ENNReal.ofReal M)).Nonempty) :
    ∃ φ ∈ normalizedMomentEnergySublevel n L μ (ENNReal.ofReal M),
      ∀ ψ ∈ normalizedMomentEnergySublevel n L μ (ENNReal.ofReal M),
        momentVariationalFunctional μ ψ ≤ momentVariationalFunctional μ φ := by
  let S := normalizedMomentEnergySublevel n L μ (ENNReal.ofReal M)
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    (isCompact_normalizedMomentEnergySublevel n L μ (ENNReal.ofReal M))
  have hne' : (Set.univ : Set S).Nonempty := by
    obtain ⟨φ, hφ⟩ := hne
    exact ⟨⟨φ, hφ⟩, mem_univ _⟩
  obtain ⟨φ, _, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn hne' isCompact_univ
    ((hμ.upperSemicontinuous_functional_on_energy_sublevel L hM).upperSemicontinuousOn univ)
  refine ⟨φ.1, φ.2, fun ψ hψ => ?_⟩
  exact hmax (mem_univ (⟨ψ, hψ⟩ : S))

/-- Attainment on the whole finite-energy normalized family, from an actual
competitor. The compact energy threshold is produced inside the proof using
the proved coercivity estimate. -/
theorem IsIsotropic.exists_momentVariational_maximizer_of_competitor
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (L : ℝ≥0) (φ₀ : C(Space n, ℝ))
    (hφ₀ : φ₀ ∈ normalizedConvexLipschitzPotentials n L)
    (hφ₀nonneg : ∀ x, 0 ≤ φ₀ x) (hφ₀finite : momentDualEnergy μ φ₀ ≠ ∞) :
    ∃ φ : C(Space n, ℝ),
      φ ∈ normalizedConvexLipschitzPotentials n L ∧ (∀ x, 0 ≤ φ x) ∧
      momentDualEnergy μ φ ≠ ∞ ∧
      ∀ ψ : C(Space n, ℝ), ψ ∈ normalizedConvexLipschitzPotentials n L →
        (∀ x, 0 ≤ ψ x) → momentDualEnergy μ ψ ≠ ∞ →
        momentVariationalFunctional μ ψ ≤ momentVariationalFunctional μ φ := by
  obtain ⟨C, hcoercive⟩ := hμ.exists_momentVariational_coercivity
  let M : ℝ := 2 * (C - momentVariationalFunctional μ φ₀) + 1
  have h₀ := hcoercive φ₀ φ₀.continuous.aestronglyMeasurable hφ₀nonneg hφ₀finite
  have hM : 0 ≤ M := by
    dsimp [M]
    nlinarith [ENNReal.toReal_nonneg (a := momentDualEnergy μ φ₀)]
  have h₀energy : momentDualEnergy μ φ₀ ≤ ENNReal.ofReal M := by
    apply (ENNReal.le_ofReal_iff_toReal_le hφ₀finite hM).mpr
    dsimp [M]
    linarith
  obtain ⟨φ, hφ, hmax⟩ := hμ.exists_maximizer_on_momentEnergy_sublevel L hM
    ⟨φ₀, hφ₀, hφ₀nonneg, h₀energy⟩
  have hφfinite : momentDualEnergy μ φ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hφ.2.2
  refine ⟨φ, hφ.1, hφ.2.1, hφfinite, fun ψ hψ hψnonneg hψfinite => ?_⟩
  by_cases hψenergy : momentDualEnergy μ ψ ≤ ENNReal.ofReal M
  · exact hmax ψ ⟨hψ, hψnonneg, hψenergy⟩
  · have hψlarge : M < (momentDualEnergy μ ψ).toReal := by
      by_contra h
      exact hψenergy ((ENNReal.le_ofReal_iff_toReal_le hψfinite hM).mpr (le_of_not_gt h))
    have hψbound := hcoercive ψ ψ.continuous.aestronglyMeasurable hψnonneg hψfinite
    have hcompare := hmax φ₀ ⟨hφ₀, hφ₀nonneg, h₀energy⟩
    dsimp [M] at hψlarge
    linarith

/-- Radial norm competitor with an explicitly specified Lipschitz bound. -/
def momentNormCompetitor (n : ℕ) (L : ℝ≥0) : C(Space n, ℝ) :=
  ⟨fun x => (L : ℝ) * ‖x‖, by fun_prop⟩

theorem momentNormCompetitor_lipschitz (n : ℕ) (L : ℝ≥0) :
    LipschitzWith L (momentNormCompetitor n L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist ((L : ℝ) * ‖x‖) ((L : ℝ) * ‖y‖) ≤ (L : ℝ) * dist x y
  rw [Real.dist_eq, ← mul_sub, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ (L : ℝ) from L.property), dist_eq_norm]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) L.property

theorem momentNormCompetitor_normalized (n : ℕ) (L : ℝ≥0) :
    momentNormCompetitor n L ∈ normalizedConvexLipschitzPotentials n L := by
  refine ⟨momentNormCompetitor_lipschitz n L, by simp [momentNormCompetitor], ?_⟩
  exact (convexOn_norm convex_univ).smul L.property

theorem momentNormCompetitor_nonneg (n : ℕ) (L : ℝ≥0) (x : Space n) :
    0 ≤ momentNormCompetitor n L x :=
  mul_nonneg L.property (norm_nonneg x)

theorem normalizedLegendreTransform_normCompetitor_eq_zero
    {n : ℕ} (L : ℝ≥0) {y : Space n} (hy : ‖y‖ ≤ L) :
    normalizedLegendreTransform (momentNormCompetitor n L) y = 0 := by
  apply le_antisymm _ bot_le
  change normalizedLegendreTransform (momentNormCompetitor n L) y ≤ (0 : ℝ≥0∞)
  rw [← ENNReal.ofReal_zero]
  apply (normalizedLegendreTransform_le_ofReal_iff _ _ (le_refl 0)).mpr
  intro x
  have h : inner ℝ y x ≤ (L : ℝ) * ‖x‖ :=
    (real_inner_le_norm y x).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
  change inner ℝ y x - (L : ℝ) * ‖x‖ ≤ 0
  linarith

theorem momentDualEnergy_normCompetitor_eq_zero
    {n : ℕ} {μ : Measure (Space n)} (L : ℝ≥0) (hbound : ∀ᵐ y ∂μ, ‖y‖ ≤ L) :
    momentDualEnergy μ (momentNormCompetitor n L) = 0 := by
  calc
    _ = ∫⁻ _y : Space n, (0 : ℝ≥0∞) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hbound] with y hy
      exact normalizedLegendreTransform_normCompetitor_eq_zero L hy
    _ = 0 := lintegral_zero

/-- Actual variational attainment for every isotropic probability law supported
in the prescribed ball. Both a competitor and the optimizer are constructed;
there is no optimizer certificate among the assumptions. -/
theorem IsIsotropic.exists_momentVariational_maximizer_of_bounded
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (L : ℝ≥0) (hbound : ∀ᵐ y ∂μ, ‖y‖ ≤ L) :
    ∃ φ : C(Space n, ℝ),
      φ ∈ normalizedConvexLipschitzPotentials n L ∧ (∀ x, 0 ≤ φ x) ∧
      momentDualEnergy μ φ ≠ ∞ ∧
      ∀ ψ : C(Space n, ℝ), ψ ∈ normalizedConvexLipschitzPotentials n L →
        (∀ x, 0 ≤ ψ x) → momentDualEnergy μ ψ ≠ ∞ →
        momentVariationalFunctional μ ψ ≤ momentVariationalFunctional μ φ := by
  apply hμ.exists_momentVariational_maximizer_of_competitor L (momentNormCompetitor n L)
    (momentNormCompetitor_normalized n L) (momentNormCompetitor_nonneg n L)
  rw [momentDualEnergy_normCompetitor_eq_zero L hbound]
  exact ENNReal.zero_ne_top

end KLS
end

#print axioms KLS.IsIsotropic.exists_momentVariational_maximizer_of_competitor
#print axioms KLS.momentDualEnergy_normCompetitor_eq_zero
#print axioms KLS.IsIsotropic.exists_momentVariational_maximizer_of_bounded
