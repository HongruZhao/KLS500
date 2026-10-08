import KLS.MomentProjectionCoercivity
import KLS.MomentPotentialCompactness

/-!
# Actual normalized Legendre energy and its lower semicontinuity

For a potential with `φ 0 = 0`, its Legendre transform is nonnegative. We
therefore represent that extended transform in `ENNReal`, as the supremum of
the nonnegative parts of its defining affine expressions. The `IsLUB` theorem
below verifies that, when finite, its real value is exactly the usual Legendre
transform. Infinite values remain infinite in the dual energy.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

noncomputable section
namespace KLS

/-- Nonnegative extended Legendre transform. On the normalized class `φ 0 = 0`
this is the genuine Legendre transform, since its supremum is nonnegative. -/
def normalizedLegendreTransform {n : ℕ} (φ : Space n → ℝ) (y : Space n) : ℝ≥0∞ :=
  ⨆ x : Space n, ENNReal.ofReal (inner ℝ y x - φ x)

/-- Actual integral of the extended normalized Legendre transform. -/
def momentDualEnergy {n : ℕ} (μ : Measure (Space n)) (φ : Space n → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, normalizedLegendreTransform φ y ∂μ

theorem ofReal_affine_le_normalizedLegendreTransform {n : ℕ} (φ : Space n → ℝ)
    (x y : Space n) :
    ENNReal.ofReal (inner ℝ y x - φ x) ≤ normalizedLegendreTransform φ y :=
  le_iSup (fun z => ENNReal.ofReal (inner ℝ y z - φ z)) x

theorem normalizedLegendreTransform_le_ofReal_iff {n : ℕ} (φ : Space n → ℝ)
    (y : Space n) {a : ℝ} (ha : 0 ≤ a) :
    normalizedLegendreTransform φ y ≤ ENNReal.ofReal a ↔
      ∀ x : Space n, inner ℝ y x - φ x ≤ a := by
  simp only [normalizedLegendreTransform, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff ha]

theorem normalizedLegendreTransform_young {n : ℕ} (φ : Space n → ℝ)
    {y : Space n} (hy : normalizedLegendreTransform φ y ≠ ∞) (x : Space n) :
    inner ℝ y x ≤ φ x + (normalizedLegendreTransform φ y).toReal := by
  have h := (ENNReal.ofReal_le_iff_le_toReal hy).mp
    (ofReal_affine_le_normalizedLegendreTransform φ x y)
  linarith

/-- This equality of least upper bounds checks the conventional normalization:
the finite real value is the supremum of `y·x - φ(x)`, without changing it by
clipping, whenever `φ(0)=0`. -/
theorem normalizedLegendreTransform_isLUB {n : ℕ} {φ : Space n → ℝ}
    (hzero : φ 0 = 0) {y : Space n} (hy : normalizedLegendreTransform φ y ≠ ∞) :
    IsLUB (Set.range (fun x : Space n => inner ℝ y x - φ x))
      (normalizedLegendreTransform φ y).toReal := by
  constructor
  · rintro z ⟨x, rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hy).mp
      (ofReal_affine_le_normalizedLegendreTransform φ x y)
  · intro a ha
    have ha0 : 0 ≤ a := by
      have h := ha (Set.mem_range_self (0 : Space n))
      simpa only [inner_zero_right, hzero, sub_zero] using h
    have hle : normalizedLegendreTransform φ y ≤ ENNReal.ofReal a := by
      apply (normalizedLegendreTransform_le_ofReal_iff φ y ha0).mpr
      intro x
      exact ha (Set.mem_range_self x)
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    simpa only [ENNReal.toReal_ofReal ha0] using h

theorem lowerSemicontinuous_normalizedLegendreTransform {n : ℕ} (φ : Space n → ℝ) :
    LowerSemicontinuous (normalizedLegendreTransform φ) := by
  apply lowerSemicontinuous_iSup
  intro x
  exact (ENNReal.continuous_ofReal.comp (by fun_prop)).lowerSemicontinuous

theorem measurable_normalizedLegendreTransform {n : ℕ} (φ : Space n → ℝ) :
    Measurable (normalizedLegendreTransform φ) :=
  (lowerSemicontinuous_normalizedLegendreTransform φ).measurable

theorem normalizedLegendreTransform_antitone {n : ℕ} {φ ψ : Space n → ℝ}
    (h : φ ≤ ψ) : normalizedLegendreTransform ψ ≤ normalizedLegendreTransform φ := by
  intro y
  apply iSup_mono
  intro x
  exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (h x) _)

theorem normalizedLegendreTransform_le_liminf {n : ℕ} {φ : ℕ → Space n → ℝ}
    {ψ : Space n → ℝ} (hlim : ∀ x, Tendsto (fun k => φ k x) atTop (𝓝 (ψ x)))
    (y : Space n) :
    normalizedLegendreTransform ψ y ≤ liminf (fun k => normalizedLegendreTransform (φ k) y) atTop := by
  apply iSup_le
  intro x
  have hconv : Tendsto (fun k => ENNReal.ofReal (inner ℝ y x - φ k x)) atTop
      (𝓝 (ENNReal.ofReal (inner ℝ y x - ψ x))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.sub (hlim x))
  rw [← hconv.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun k =>
    ofReal_affine_le_normalizedLegendreTransform (φ k) x y)

/-- The actual dual energy is lower semicontinuous under pointwise convergence
of potentials. Fatou retains possible infinite dual values. -/
theorem momentDualEnergy_le_liminf {n : ℕ} (μ : Measure (Space n))
    {φ : ℕ → Space n → ℝ} {ψ : Space n → ℝ}
    (hlim : ∀ x, Tendsto (fun k => φ k x) atTop (𝓝 (ψ x))) :
    momentDualEnergy μ ψ ≤ liminf (fun k => momentDualEnergy μ (φ k)) atTop := by
  calc
    _ ≤ ∫⁻ y, liminf (fun k => normalizedLegendreTransform (φ k) y) atTop ∂μ :=
      lintegral_mono (normalizedLegendreTransform_le_liminf hlim)
    _ ≤ _ := lintegral_liminf_le (fun k => measurable_normalizedLegendreTransform (φ k))

theorem ae_normalizedLegendreTransform_lt_top {n : ℕ} {μ : Measure (Space n)}
    {φ : Space n → ℝ} (hfinite : momentDualEnergy μ φ ≠ ∞) :
    ∀ᵐ y ∂μ, normalizedLegendreTransform φ y < ∞ :=
  ae_lt_top (measurable_normalizedLegendreTransform φ) hfinite

theorem integrable_normalizedLegendreTransform_toReal {n : ℕ} {μ : Measure (Space n)}
    {φ : Space n → ℝ} (hfinite : momentDualEnergy μ φ ≠ ∞) :
    Integrable (fun y => (normalizedLegendreTransform φ y).toReal) μ :=
  integrable_toReal_of_lintegral_ne_top
    (measurable_normalizedLegendreTransform φ).aemeasurable hfinite

theorem integral_normalizedLegendreTransform_toReal {n : ℕ} {μ : Measure (Space n)}
    {φ : Space n → ℝ} (hfinite : momentDualEnergy μ φ ≠ ∞) :
    (∫ y, (normalizedLegendreTransform φ y).toReal ∂μ) = (momentDualEnergy μ φ).toReal :=
  integral_toReal (measurable_normalizedLegendreTransform φ).aemeasurable
    (ae_normalizedLegendreTransform_lt_top hfinite)

theorem IsIsotropic.integrable_positive_projection {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (x : Space n) :
    Integrable (fun y : Space n => max (inner ℝ y x) 0) μ := by
  have h := ((hμ.integrable_inner x).abs.add (hμ.integrable_inner x)).div_const 2
  convert h using 1
  funext y
  change max (inner ℝ y x) 0 = (|inner ℝ y x| + inner ℝ y x) / 2
  rcases le_total 0 (inner ℝ y x) with hy | hy
  · rw [max_eq_left hy, abs_of_nonneg hy]
    ring
  · rw [max_eq_right hy, abs_of_nonpos hy]
    ring

theorem IsIsotropic.integral_positive_projection {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (x : Space n) :
    (∫ y : Space n, max (inner ℝ y x) 0 ∂μ) = projectionAbsoluteMoment μ x / 2 := by
  have heq (y : Space n) : max (inner ℝ y x) 0 = (|inner ℝ y x| + inner ℝ y x) / 2 := by
    rcases le_total 0 (inner ℝ y x) with hy | hy
    · rw [max_eq_left hy, abs_of_nonneg hy]
      ring
    · rw [max_eq_right hy, abs_of_nonpos hy]
      ring
  simp_rw [heq]
  rw [integral_div, integral_add (hμ.integrable_inner x).abs (hμ.integrable_inner x),
    hμ.integral_inner, add_zero]
  rfl

/-- Positive-part Fenchel integrated against a centered isotropic law. All real
integral manipulations follow from finite actual dual energy. -/
theorem IsIsotropic.half_projectionAbsoluteMoment_le_dualEnergy_add
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    {φ : Space n → ℝ} (hnonneg : ∀ x, 0 ≤ φ x) (hfinite : momentDualEnergy μ φ ≠ ∞)
    (x : Space n) :
    projectionAbsoluteMoment μ x / 2 ≤ (momentDualEnergy μ φ).toReal + φ x := by
  rw [← hμ.integral_positive_projection]
  calc
    _ ≤ ∫ y, ((normalizedLegendreTransform φ y).toReal + φ x) ∂μ := by
      apply integral_mono_ae (hμ.integrable_positive_projection x)
        ((integrable_normalizedLegendreTransform_toReal hfinite).add (integrable_const _))
      filter_upwards [ae_normalizedLegendreTransform_lt_top hfinite] with y hy
      apply max_le
      · change inner ℝ y x ≤ (normalizedLegendreTransform φ y).toReal + φ x
        have h := normalizedLegendreTransform_young φ hy.ne x
        linarith
      · exact add_nonneg ENNReal.toReal_nonneg (hnonneg x)
    _ = _ := by
      rw [integral_add (integrable_normalizedLegendreTransform_toReal hfinite) (integrable_const _),
        integral_normalizedLegendreTransform_toReal hfinite]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- An actual finite dual energy controls the potential below by a linear cone.
The positive slope is constructed from isotropy and is independent of the
potential; no convexity or variational-optimizer premise is required. -/
theorem IsIsotropic.exists_dualEnergy_linear_coercivity
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) :
    ∃ a : ℝ, 0 < a ∧ ∀ φ : Space n → ℝ, (∀ x, 0 ≤ φ x) → momentDualEnergy μ φ ≠ ∞ →
      ∀ x, a * ‖x‖ - (momentDualEnergy μ φ).toReal ≤ φ x := by
  obtain ⟨m, hm, hproj⟩ := hμ.exists_projectionAbsoluteMoment_coercivity
  refine ⟨m / 2, half_pos hm, fun φ hφ hfinite x => ?_⟩
  have hp := hproj x
  have hd := hμ.half_projectionAbsoluteMoment_le_dualEnergy_add hφ hfinite x
  nlinarith

end KLS
end

#print axioms KLS.normalizedLegendreTransform_isLUB
#print axioms KLS.momentDualEnergy_le_liminf
#print axioms KLS.IsIsotropic.exists_dualEnergy_linear_coercivity
