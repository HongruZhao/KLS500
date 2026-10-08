import KLS.DensityToClass

/-!
# Log-concavity of actual convolution densities and measures

Prékopa--Leindler proves the pointwise inequality for Mathlib's actual
nonnegative convolution integral. The actual measure convolution is then
identified with this density by Mathlib's withDensity theorem.
-/

open MeasureTheory Set
open scoped ENNReal MeasureTheory

noncomputable section
namespace KLS

theorem lconvolution_logConcave {n : ℕ} {f g : Space n → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfLog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    (hgLog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      g x ^ t * g y ^ (1 - t) ≤ g (t • x + (1 - t) • y))
    (x y : Space n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (f ⋆ₗ g) x ^ t * (f ⋆ₗ g) y ^ (1 - t) ≤
      (f ⋆ₗ g) (t • x + (1 - t) • y) := by
  apply prekopaLeindler
    (hf.mul (hg.comp (measurable_neg.add_const x)))
    (hf.mul (hg.comp (measurable_neg.add_const y)))
    (hf.mul (hg.comp (measurable_neg.add_const (t • x + (1 - t) • y)))) ht0 ht1
  intro u v
  simp only [Pi.mul_apply, Function.comp_def]
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le,
    ENNReal.mul_rpow_of_nonneg _ _ (sub_pos.mpr ht1).le]
  have heq : t • (-u + x) + (1 - t) • (-v + y) =
      -(t • u + (1 - t) • v) + (t • x + (1 - t) • y) := by
    simp only [smul_add, smul_neg, neg_add_rev]
    abel
  calc
    f u ^ t * g (-u + x) ^ t * (f v ^ (1 - t) * g (-v + y) ^ (1 - t)) =
        (f u ^ t * f v ^ (1 - t)) * (g (-u + x) ^ t * g (-v + y) ^ (1 - t)) := by ring
    _ ≤ f (t • u + (1 - t) • v) * g (t • (-u + x) + (1 - t) • (-v + y)) :=
      mul_le_mul' (hfLog u v t ht0 ht1) (hgLog (-u + x) (-v + y) t ht0 ht1)
    _ = _ := by rw [heq]

/-- Actual convolution of the two density measures preserves the compact-set
log-concavity definition. No finite or nonvanishing density is assumed. -/
theorem measureLogConcave_conv_withDensity {n : ℕ} {f g : Space n → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfLog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    (hgLog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      g x ^ t * g y ^ (1 - t) ≤ g (t • x + (1 - t) • y)) :
    measureLogConcave (((volume : Measure (Space n)).withDensity f) ∗
      ((volume : Measure (Space n)).withDensity g)) := by
  rw [conv_withDensity_eq_lconvolution hf hg]
  exact measureLogConcave_withDensity_of_pointwise (measurable_lconvolution volume hf hg)
    (fun x y _ ht0 ht1 => lconvolution_logConcave hf hg hfLog hgLog x y ht0 ht1)

/-- The original convex-potential density hypotheses suffice for actual
convolution log-concavity; no isotropy or Gaussian restriction is used. -/
theorem HasLogConcaveDensity.conv_measureLogConcave {n : ℕ}
    {μ ν : Measure (Space n)} (hμ : HasLogConcaveDensity μ) (hν : HasLogConcaveDensity ν) :
    KLS.measureLogConcave (μ ∗ ν) := by
  obtain ⟨V, hV, hm, rfl⟩ := hμ
  obtain ⟨W, hW, hn, rfl⟩ := hν
  exact measureLogConcave_conv_withDensity hm hn
    (fun x y _ ht0 ht1 => hV.expNegPotential_logConcave x y ht0 ht1)
    (fun x y _ ht0 ht1 => hW.expNegPotential_logConcave x y ht0 ht1)

theorem admissibleMeasure.conv_measureLogConcave {n : ℕ}
    {μ ν : Measure (Space n)} (hμ : admissibleMeasure μ) (hν : admissibleMeasure ν) :
    KLS.measureLogConcave (μ ∗ ν) :=
  hμ.hasLogConcaveDensity.conv_measureLogConcave hν.hasLogConcaveDensity

end KLS
end

#print axioms KLS.lconvolution_logConcave
#print axioms KLS.measureLogConcave_conv_withDensity
#print axioms KLS.HasLogConcaveDensity.conv_measureLogConcave
#print axioms KLS.admissibleMeasure.conv_measureLogConcave
