import KLS.MomentLegendrePerturbation

/-!
# Normalize actual conjugate perturbations and control their energy

The minimum is attained by coercivity. Translation to that actual minimizer
and subtraction of its value produces an admissible normalized competitor.
The energy comparison is proved by integrating the pointwise conjugate bound.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

def normalizeMomentPotentialAt {n : ℕ} (ψ : Space n → ℝ) (x₀ : Space n) (x : Space n) : ℝ :=
  ψ (x + x₀) - ψ x₀

theorem normalizeMomentPotentialAt_zero {n : ℕ} (ψ : Space n → ℝ) (x₀ : Space n) :
    normalizeMomentPotentialAt ψ x₀ 0 = 0 := by
  simp [normalizeMomentPotentialAt]

theorem normalizeMomentPotentialAt_nonneg {n : ℕ} {ψ : Space n → ℝ} {x₀ : Space n}
    (hmin : ∀ x, ψ x₀ ≤ ψ x) (x : Space n) : 0 ≤ normalizeMomentPotentialAt ψ x₀ x :=
  sub_nonneg.mpr (hmin (x + x₀))

theorem lipschitzWith_normalizeMomentPotentialAt {n : ℕ} {ψ : Space n → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L ψ) (x₀ : Space n) :
    LipschitzWith L (normalizeMomentPotentialAt ψ x₀) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simpa only [normalizeMomentPotentialAt, dist_sub_right, dist_add_right] using
    hLip.dist_le_mul (x + x₀) (z + x₀)

theorem convexOn_normalizeMomentPotentialAt {n : ℕ} {ψ : Space n → ℝ}
    (hconvex : ConvexOn ℝ Set.univ ψ) (x₀ : Space n) :
    ConvexOn ℝ Set.univ (normalizeMomentPotentialAt ψ x₀) := by
  convert! (hconvex.translate_left x₀).add_const (-ψ x₀) using 1

theorem momentPartitionFunction_normalizeAt {n : ℕ} (ψ : Space n → ℝ) (x₀ : Space n) :
    momentPartitionFunction (normalizeMomentPotentialAt ψ x₀) =
      Real.exp (ψ x₀) * momentPartitionFunction ψ := by
  unfold momentPartitionFunction normalizeMomentPotentialAt
  simp_rw [neg_sub, sub_eq_add_neg, Real.exp_add]
  rw [integral_const_mul, integral_add_right_eq_self (fun x : Space n => Real.exp (-ψ x)) x₀]

theorem exists_minimizer_of_linear_coercivity {n : ℕ} {ψ : Space n → ℝ}
    (hcont : Continuous ψ) {a A : ℝ} (ha : 0 < a) (hcone : ∀ x, a * ‖x‖ - A ≤ ψ x) :
    ∃ x₀ : Space n, ∀ x : Space n, ψ x₀ ≤ ψ x := by
  apply hcont.exists_forall_le' 0
  have hnorm : ∀ᶠ x : Space n in cocompact (Space n), (ψ 0 + A) / a ≤ ‖x‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hnorm] with x hx
  have hm := (div_le_iff₀ ha).mp hx
  have hc := hcone x
  nlinarith

theorem IsIsotropic.exists_minimizer_momentLegendrePerturbation
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hconvex : ConvexOn ℝ Set.univ φ) (hzero : φ 0 = 0) (hnonneg : ∀ x, 0 ≤ φ x)
    (hfinite : momentDualEnergy μ φ ≠ ∞) {v : Space n → ℝ} {B : ℝ}
    (hv : ∀ y, |v y| ≤ B) (t : ℝ) :
    ∃ x₀ : Space n, ∀ x : Space n,
      momentLegendrePerturbation φ v t x₀ ≤ momentLegendrePerturbation φ v t x := by
  obtain ⟨a, ha, hcone⟩ := hμ.exists_dualEnergy_linear_coercivity
  apply exists_minimizer_of_linear_coercivity
    (lipschitzWith_momentLegendrePerturbation hLip hzero hnonneg hv t).continuous ha
    (A := (momentDualEnergy μ φ).toReal + |t| * B)
  intro x
  have hc := hcone φ hnonneg hfinite x
  have hd := (abs_le.mp (abs_momentLegendrePerturbation_sub_le
    hLip.continuous hconvex hzero hnonneg hv t x)).1
  linarith

theorem normalizedLegendreTransform_normalizedPerturbation_le
    {n : ℕ} (φ : Space n → ℝ) {v : Space n → ℝ} {B : ℝ}
    (hv : ∀ y, |v y| ≤ B) (t : ℝ) (x₀ : Space n) (y : momentLegendreDomain φ) :
    normalizedLegendreTransform
        (normalizeMomentPotentialAt (momentLegendrePerturbation φ v t) x₀) y.1 ≤
      ENNReal.ofReal ((normalizedLegendreTransform φ y.1).toReal + t * v y.1 -
        inner ℝ y.1 x₀ + momentLegendrePerturbation φ v t x₀) := by
  have h₀ := affine_le_momentLegendrePerturbation φ hv t x₀ y
  have hnonneg : 0 ≤ (normalizedLegendreTransform φ y.1).toReal + t * v y.1 -
      inner ℝ y.1 x₀ + momentLegendrePerturbation φ v t x₀ := by linarith
  apply (normalizedLegendreTransform_le_ofReal_iff _ _ hnonneg).mpr
  intro x
  have h := affine_le_momentLegendrePerturbation φ hv t (x + x₀) y
  rw [inner_add_right] at h
  unfold normalizeMomentPotentialAt
  linarith

/-- Finite original dual energy yields finite energy for every normalized
bounded conjugate perturbation. Centering cancels the translation term. -/
theorem IsIsotropic.momentDualEnergy_normalizedPerturbation_bound
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    {φ : Space n → ℝ} (hfinite : momentDualEnergy μ φ ≠ ∞)
    {v : Space n → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B) (hvi : Integrable v μ)
    (t : ℝ) (x₀ : Space n) :
    0 ≤ (momentDualEnergy μ φ).toReal + t * (∫ y, v y ∂μ) +
        momentLegendrePerturbation φ v t x₀ ∧
    momentDualEnergy μ (normalizeMomentPotentialAt (momentLegendrePerturbation φ v t) x₀) ≤
      ENNReal.ofReal ((momentDualEnergy μ φ).toReal + t * (∫ y, v y ∂μ) +
        momentLegendrePerturbation φ v t x₀) := by
  let g : Space n → ℝ := fun y => (normalizedLegendreTransform φ y).toReal + t * v y -
    inner ℝ y x₀ + momentLegendrePerturbation φ v t x₀
  have hgi : Integrable g μ :=
    (((integrable_normalizedLegendreTransform_toReal hfinite).add (hvi.const_mul t)).sub
      (hμ.integrable_inner x₀)).add (integrable_const _)
  have hgnonneg : 0 ≤ᵐ[μ] g := by
    filter_upwards [ae_normalizedLegendreTransform_lt_top hfinite] with y hy
    have h := affine_le_momentLegendrePerturbation φ hv t x₀
      (⟨y, hy.ne⟩ : momentLegendreDomain φ)
    change 0 ≤ (normalizedLegendreTransform φ y).toReal + t * v y -
      inner ℝ y x₀ + momentLegendrePerturbation φ v t x₀
    linarith
  have hgint : (∫ y, g y ∂μ) = (momentDualEnergy μ φ).toReal + t * (∫ y, v y ∂μ) +
      momentLegendrePerturbation φ v t x₀ := by
    unfold g
    have h₁ := integral_add (((integrable_normalizedLegendreTransform_toReal hfinite).add
      (hvi.const_mul t)).sub (hμ.integrable_inner x₀))
      (integrable_const (momentLegendrePerturbation φ v t x₀) (μ := μ))
    have h₂ := integral_sub ((integrable_normalizedLegendreTransform_toReal hfinite).add
      (hvi.const_mul t)) (hμ.integrable_inner x₀)
    have h₃ := integral_add (integrable_normalizedLegendreTransform_toReal hfinite) (hvi.const_mul t)
    simp only [Pi.add_apply, Pi.sub_apply] at h₁ h₂ h₃
    rw [h₁, h₂, h₃, integral_normalizedLegendreTransform_toReal hfinite,
      integral_const_mul, hμ.integral_inner]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_zero]
  constructor
  · rw [← hgint]
    exact integral_nonneg_of_ae hgnonneg
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (g y) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_normalizedLegendreTransform_lt_top hfinite] with y hy
      exact normalizedLegendreTransform_normalizedPerturbation_le φ hv t x₀ ⟨y, hy.ne⟩
    _ = ENNReal.ofReal (∫ y, g y ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hgi hgnonneg).symm
    _ = _ := by rw [hgint]

theorem IsIsotropic.momentDualEnergy_normalizedPerturbation_toReal_le
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    {φ : Space n → ℝ} (hfinite : momentDualEnergy μ φ ≠ ∞)
    {v : Space n → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B) (hvi : Integrable v μ)
    (t : ℝ) (x₀ : Space n) :
    momentDualEnergy μ (normalizeMomentPotentialAt (momentLegendrePerturbation φ v t) x₀) ≠ ∞ ∧
      (momentDualEnergy μ (normalizeMomentPotentialAt (momentLegendrePerturbation φ v t) x₀)).toReal ≤
        (momentDualEnergy μ φ).toReal + t * (∫ y, v y ∂μ) + momentLegendrePerturbation φ v t x₀ := by
  obtain ⟨hnonneg, hle⟩ := hμ.momentDualEnergy_normalizedPerturbation_bound hfinite hv hvi t x₀
  exact ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle,
    ENNReal.toReal_le_of_le_ofReal hnonneg hle⟩

end KLS
end

#print axioms KLS.IsIsotropic.exists_minimizer_momentLegendrePerturbation
#print axioms KLS.IsIsotropic.momentDualEnergy_normalizedPerturbation_toReal_le
