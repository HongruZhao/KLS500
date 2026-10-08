import KLS.MultiplicativeBrunnMinkowski
import KLS.ExponentialMoments
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Compact-set log-concavity of the actual exponential law

The change of variables `x ↦ exp(-x)` identifies exponentially weighted
Lebesgue measure with ordinary length of the image. Multiplicative
Brunn--Minkowski gives compact-set log-concavity of this weight. Restriction
to the closed positive half-line gives exactly `expMeasure 1`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section
namespace KLS

def realAffineSetCombination (t : ℝ) (E F : Set ℝ) : Set ℝ :=
  (fun p : ℝ × ℝ => t * p.1 + (1 - t) * p.2) '' (E ×ˢ F)

theorem isCompact_realAffineSetCombination (t : ℝ) {E F : Set ℝ}
    (hE : IsCompact E) (hF : IsCompact F) : IsCompact (realAffineSetCombination t E F) :=
  (hE.prod hF).image (by fun_prop)

def exponentialWeightMeasure : Measure ℝ :=
  volume.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp (-x)))

/-- This is an actual Jacobian identity for arbitrary measurable sets. -/
theorem exponentialWeightMeasure_eq_volume_image {E : Set ℝ} (hE : MeasurableSet E) :
    exponentialWeightMeasure E = volume ((fun x : ℝ => Real.exp (-x)) '' E) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa using (hasDerivAt_id x).neg.exp
  have hi : Function.Injective (fun x : ℝ => Real.exp (-x)) := by
    intro x y h
    exact neg_injective (Real.exp_injective h)
  have h := lintegral_image_eq_lintegral_abs_deriv_mul hE
    (fun x _ => (hd x).hasDerivWithinAt) hi.injOn (fun _ => 1)
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one, abs_neg,
    abs_of_pos (Real.exp_pos _)] at h
  rw [exponentialWeightMeasure, withDensity_apply _ hE]
  exact h.symm

theorem exp_neg_affineCombination (x y t : ℝ) :
    Real.exp (-(t * x + (1 - t) * y)) =
      Real.exp (-x) ^ t * Real.exp (-y) ^ (1 - t) := by
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

theorem exp_neg_image_realAffineSetCombination (E F : Set ℝ) (t : ℝ) :
    (fun x : ℝ => Real.exp (-x)) '' realAffineSetCombination t E F =
      geometricSetCombination t ((fun x : ℝ => Real.exp (-x)) '' E)
        ((fun x : ℝ => Real.exp (-x)) '' F) := by
  ext z
  constructor
  · rintro ⟨w, ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩, rfl⟩
    exact ⟨(Real.exp (-x), Real.exp (-y)), ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩,
      (exp_neg_affineCombination x y t).symm⟩
  · rintro ⟨⟨a, b⟩, ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, rfl⟩
    exact ⟨t * x + (1 - t) * y, ⟨(x, y), ⟨hx, hy⟩, rfl⟩,
      exp_neg_affineCombination x y t⟩

/-- Exponentially weighted Lebesgue measure is log-concave on arbitrary
compact real sets, without an assumed density-to-measure theorem. -/
theorem exponentialWeightMeasure_logConcave {E F : Set ℝ}
    (hE : IsCompact E) (hF : IsCompact F) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (exponentialWeightMeasure E) ^ t * (exponentialWeightMeasure F) ^ (1 - t) ≤
      exponentialWeightMeasure (realAffineSetCombination t E F) := by
  rw [exponentialWeightMeasure_eq_volume_image hE.measurableSet,
    exponentialWeightMeasure_eq_volume_image hF.measurableSet,
    exponentialWeightMeasure_eq_volume_image (isCompact_realAffineSetCombination t hE hF).measurableSet,
    exp_neg_image_realAffineSetCombination]
  apply real_volume_geometricCombination_ge (hE.image (by fun_prop)) (hF.image (by fun_prop))
  · rintro _ ⟨x, _, rfl⟩
    exact Real.exp_pos _
  · rintro _ ⟨y, _, rfl⟩
    exact Real.exp_pos _
  · exact ht0
  · exact ht1

theorem expMeasure_one_eq_restrict_exponentialWeight :
    expMeasure 1 = exponentialWeightMeasure.restrict (Ici 0) := by
  have hdensity : exponentialPDF 1 = (Ici (0 : ℝ)).indicator
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-x))) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp [exponentialPDF_of_nonneg hx, hx]
    · simp [exponentialPDF_of_neg (lt_of_not_ge hx), hx]
  change volume.withDensity (exponentialPDF 1) = _
  rw [hdensity, withDensity_indicator measurableSet_Ici,
    exponentialWeightMeasure, restrict_withDensity measurableSet_Ici]

/-- Exact compact-set log-concavity of the standard rate-one exponential law. -/
theorem expMeasure_one_compact_logConcave {E F : Set ℝ}
    (hE : IsCompact E) (hF : IsCompact F) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (expMeasure 1 E) ^ t * (expMeasure 1 F) ^ (1 - t) ≤
      expMeasure 1 (realAffineSetCombination t E F) := by
  rw [expMeasure_one_eq_restrict_exponentialWeight,
    Measure.restrict_apply hE.measurableSet, Measure.restrict_apply hF.measurableSet,
    Measure.restrict_apply (isCompact_realAffineSetCombination t hE hF).measurableSet]
  apply (exponentialWeightMeasure_logConcave (hE.inter_right isClosed_Ici)
    (hF.inter_right isClosed_Ici) ht0 ht1).trans
  apply measure_mono
  rintro z ⟨⟨x, y⟩, ⟨⟨hxE, hx0⟩, ⟨hyF, hy0⟩⟩, rfl⟩
  refine ⟨⟨(x, y), ⟨hxE, hyF⟩, rfl⟩, ?_⟩
  exact add_nonneg (mul_nonneg ht0.le hx0) (mul_nonneg (sub_nonneg.mpr ht1.le) hy0)

end KLS
end

#print axioms KLS.exponentialWeightMeasure_eq_volume_image
#print axioms KLS.exponentialWeightMeasure_logConcave
#print axioms KLS.expMeasure_one_compact_logConcave
