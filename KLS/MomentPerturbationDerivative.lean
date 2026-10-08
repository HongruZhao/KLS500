import KLS.MomentVariationalInequality

/-!
# First variation of the actual conjugate perturbation

The proof identifies the gradient as the unique contact slope. Approximate
contact slopes converge to it by the definition of differentiability. This
supplies the envelope derivative without assuming existence of an optimizer
for each perturbed conjugate supremum.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

theorem HasGradientAt.convex_supporting_inner {n : ℕ} {φ : Space n → ℝ}
    {g x : Space n} (hg : HasGradientAt φ g x)
    (hconvex : ConvexOn ℝ Set.univ φ) (z : Space n) :
    inner ℝ g (z - x) ≤ φ z - φ x := by
  have hc : ConvexOn ℝ Set.univ (φ ∘ AffineMap.lineMap (k := ℝ) x z) := by
    simpa using hconvex.comp_affineMap (AffineMap.lineMap (k := ℝ) x z)
  have hd : HasDerivAt (φ ∘ AffineMap.lineMap (k := ℝ) x z) (inner ℝ g (z - x)) 0 := by
    simpa using hg.hasFDerivAt.comp_hasDerivAt_of_eq 0
      (AffineMap.hasDerivAt_lineMap (a := x) (b := z) (x := (0 : ℝ))) (by simp)
  have hs := hc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hd
  simpa [slope_def_field] using hs

theorem HasGradientAt.normalizedLegendre_contact {n : ℕ} {φ : Space n → ℝ}
    {g x : Space n} (hg : HasGradientAt φ g x)
    (hconvex : ConvexOn ℝ Set.univ φ) (hzero : φ 0 = 0) :
    g ∈ momentLegendreDomain φ ∧
      (normalizedLegendreTransform φ g).toReal = inner ℝ g x - φ x := by
  have ha : 0 ≤ inner ℝ g x - φ x := by
    have h := HasGradientAt.convex_supporting_inner hg hconvex 0
    simp only [zero_sub, inner_neg_right, hzero] at h
    linarith
  have hle : normalizedLegendreTransform φ g ≤ ENNReal.ofReal (inner ℝ g x - φ x) := by
    apply (normalizedLegendreTransform_le_ofReal_iff φ g ha).mpr
    intro z
    have h := HasGradientAt.convex_supporting_inner hg hconvex z
    rw [inner_sub_right] at h
    linarith
  have heq : normalizedLegendreTransform φ g = ENNReal.ofReal (inner ℝ g x - φ x) :=
    le_antisymm hle (ofReal_affine_le_normalizedLegendreTransform φ x g)
  refine ⟨?_, ?_⟩
  · change normalizedLegendreTransform φ g ≠ ∞
    rw [heq]
    exact ENNReal.ofReal_ne_top
  · rw [heq, ENNReal.toReal_ofReal ha]

/-- Near-contact affine slopes are close to the derivative. This quantitative
form needs only differentiability and the actual Fenchel inequality. -/
theorem HasGradientAt.exists_legendre_gap_control {n : ℕ} {φ : Space n → ℝ}
    {g x : Space n} (hg : HasGradientAt φ g x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ momentLegendreDomain φ,
      φ x - (inner ℝ y x - (normalizedLegendreTransform φ y).toReal) ≤ δ →
      ‖y - g‖ < ε := by
  have herr := (hasGradientAt_iff_isLittleO_nhds_zero.mp hg).bound (show 0 < ε / 4 by positivity)
  obtain ⟨r, hr, hrbound⟩ := Metric.eventually_nhds_iff.mp herr
  refine ⟨ε * r / 8, by positivity, ?_⟩
  intro y hy hgap
  by_cases hw : y - g = 0
  · simpa [hw] using hε
  have hnorm : 0 < ‖y - g‖ := norm_pos_iff.mpr hw
  let u : Space n := (r / (2 * ‖y - g‖)) • (y - g)
  have hu : ‖u‖ = r / 2 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr (by positivity))]
    field_simp
  have herror := hrbound (y := u) (by simpa [dist_eq_norm, hu] using (show r / 2 < r by linarith))
  have hupper : φ (x + u) - φ x - inner ℝ g u ≤ ε / 4 * (r / 2) := by
    exact (le_abs_self _).trans (by simpa [hu, Real.norm_eq_abs] using herror)
  have hyoung := normalizedLegendreTransform_young φ hy (x + u)
  rw [inner_add_right] at hyoung
  have hinner : inner ℝ y u - inner ℝ g u = r / 2 * ‖y - g‖ := by
    rw [← inner_sub_left]
    dsimp [u]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hmain : r / 2 * ‖y - g‖ ≤ ε * r / 4 := by
    nlinarith only [hgap, hupper, hyoung, hinner]
  nlinarith

/-- The bounded conjugate perturbation has the expected first-order expansion
at every point at which the original convex potential is differentiable. -/
theorem hasDerivAt_momentLegendrePerturbation {n : ℕ} {φ : Space n → ℝ}
    (hcont : Continuous φ) (hconvex : ConvexOn ℝ Set.univ φ) (hzero : φ 0 = 0)
    (hnonneg : ∀ x, 0 ≤ φ x) {v : Space n → ℝ} {B : ℝ}
    (hv : ∀ y, |v y| ≤ B) {g x : Space n} (hg : HasGradientAt φ g x)
    (hvc : ContinuousAt v g) :
    HasDerivAt (fun t : ℝ => momentLegendrePerturbation φ v t x) (-v g) 0 := by
  obtain ⟨hgdom, hgcontact⟩ := HasGradientAt.normalizedLegendre_contact hg hconvex hzero
  have hB : 0 ≤ B := (abs_nonneg (v 0)).trans (hv 0)
  have hzeroPert := momentLegendrePerturbation_zero hcont hconvex hzero hnonneg v x
  apply hasDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨ρ, hρ, hρbound⟩ := Metric.continuousAt_iff.mp hvc ε hε
  obtain ⟨δ, hδ, hδbound⟩ := HasGradientAt.exists_legendre_gap_control hg hρ
  have hden : 0 < 2 * B + 1 := by linarith
  refine (Metric.eventually_nhds_iff.mpr ⟨δ / (2 * B + 1), div_pos hδ hden, ?_⟩)
  intro t ht
  have ht' : |t| * (2 * B + 1) < δ := by
    apply (lt_div_iff₀ hden).mp
    simpa [Real.dist_eq] using ht
  have hlower : φ x - t * v g ≤ momentLegendrePerturbation φ v t x := by
    have h := affine_le_momentLegendrePerturbation φ hv t x ⟨g, hgdom⟩
    change inner ℝ g x - (normalizedLegendreTransform φ g).toReal - t * v g ≤ _ at h
    rw [hgcontact] at h
    linarith
  have hupper : momentLegendrePerturbation φ v t x ≤ φ x - t * v g + ε * |t| := by
    apply csSup_le (momentLegendrePerturbation_range_nonempty hnonneg v t x)
    rintro a ⟨y, rfl⟩
    have hgapnonneg : 0 ≤ φ x - (inner ℝ y.1 x - (normalizedLegendreTransform φ y.1).toReal) := by
      have h := normalizedLegendreTransform_young φ y.2 x
      linarith
    by_cases hgap : φ x - (inner ℝ y.1 x - (normalizedLegendreTransform φ y.1).toReal) ≤ δ
    · have hyclose := hδbound y.1 y.2 hgap
      have hvclose : |v g - v y.1| ≤ ε := by
        have h := hρbound (by simpa [dist_eq_norm] using hyclose)
        simpa [Real.dist_eq, abs_sub_comm] using h.le
      have hmul : t * (v g - v y.1) ≤ ε * |t| := by
        calc
          _ ≤ |t * (v g - v y.1)| := le_abs_self _
          _ = |t| * |v g - v y.1| := abs_mul _ _
          _ ≤ |t| * ε := mul_le_mul_of_nonneg_left hvclose (abs_nonneg _)
          _ = ε * |t| := mul_comm _ _
      nlinarith only [hgapnonneg, hmul]
    · have hvdiff : |v g - v y.1| ≤ 2 * B := by
        exact (abs_sub _ _).trans (by linarith [hv g, hv y.1])
      have hmul : t * (v g - v y.1) ≤ |t| * (2 * B) := by
        exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hvdiff (abs_nonneg _))
      have hsmall : |t| * (2 * B) ≤ δ := by nlinarith [abs_nonneg t]
      have hεt : 0 ≤ ε * |t| := mul_nonneg hε.le (abs_nonneg _)
      nlinarith only [lt_of_not_ge hgap, hmul, hsmall, hεt]
  simp only [zero_add, hzeroPert, smul_eq_mul, mul_neg, sub_neg_eq_add, Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith : 0 ≤ momentLegendrePerturbation φ v t x - φ x + t * v g)]
  linarith

end KLS
end

#print axioms KLS.HasGradientAt.normalizedLegendre_contact
#print axioms KLS.HasGradientAt.exists_legendre_gap_control

#print axioms KLS.hasDerivAt_momentLegendrePerturbation
