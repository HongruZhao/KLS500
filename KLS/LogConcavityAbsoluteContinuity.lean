import KLS.LogConcavityBallDensity

/-!
# Absolute continuity of the full compact-set class

A pointwise log-concave density with a full-dimensional positivity set cannot
have an infinite value when it is finite Lebesgue-almost everywhere: one such
value would force infinity on a nonempty open set of midpoints. Applied to the
canonical lower ball density, this rules out the singular part of an isotropic
compact-set log-concave probability. This is an explicit differentiation-of-
measures proof; absolute continuity is a conclusion.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section
namespace KLS

private theorem convex_pos_of_pointwise_logConcave {n : ℕ} {d : Space n → ℝ≥0∞}
    (hlog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      d x ^ t * d y ^ (1 - t) ≤ d (t • x + (1 - t) • y)) :
    Convex ℝ {x | 0 < d x} := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hx
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have ha1 : a < 1 := by linarith
  have hba : b = 1 - a := by linarith
  rw [hba]
  exact (ENNReal.mul_pos (ENNReal.rpow_pos_of_nonneg hx ha).ne'
    (ENNReal.rpow_pos_of_nonneg hy (sub_nonneg.mpr ha1.le)).ne').trans_le
    (hlog x y a ha' ha1)

/-- Full-dimensional positivity and almost-everywhere finiteness upgrade a
pointwise log-concave extended density to a finite density at every point. -/
theorem finite_of_pointwise_logConcave {n : ℕ} {d : Space n → ℝ≥0∞}
    (hlog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      d x ^ t * d y ^ (1 - t) ≤ d (t • x + (1 - t) • y))
    (hspan : affineSpan ℝ {x | 0 < d x} = ⊤)
    (hfinite : ∀ᵐ x ∂volume, d x < ∞) : ∀ x, d x < ∞ := by
  have hinter : (interior {x | 0 < d x}).Nonempty :=
    (convex_pos_of_pointwise_logConcave hlog).interior_nonempty_iff_affineSpan_eq_top.mpr hspan
  intro x
  by_contra hx
  have hx' : d x = ∞ := eq_top_iff.mpr (not_lt.mp hx)
  let f : Space n → Space n := fun y => (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  let U : Set (Space n) := f '' interior {y | 0 < d y}
  have hUopen : IsOpen U := by
    exact ((isOpenMap_add_left ((1 / 2 : ℝ) • x)).comp
      (isOpenMap_smul₀ (by norm_num : (1 / 2 : ℝ) ≠ 0))) _ isOpen_interior
  have hUnonempty : U.Nonempty := hinter.image f
  have hUzero : volume U = 0 := by
    apply measure_mono_null (t := {z | ¬ d z < ∞}) _ (ae_iff.mp hfinite)
    rintro z ⟨y, hy, rfl⟩
    have hypos : 0 < d y := (interior_subset (s := {y | 0 < d y})) hy
    have h := hlog x y (1 / 2) (by norm_num) (by norm_num)
    have heq : d (f y) = ∞ := by
      apply top_unique
      simpa only [hx', ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
        ENNReal.top_mul (ENNReal.rpow_pos_of_nonneg hypos (by norm_num : (0 : ℝ) ≤ 1 / 2)).ne']
        using h
    simp [heq]
  exact hUopen.measure_ne_zero volume hUnonempty hUzero

theorem admissibleMeasure.lowerBallDensity_lt_top {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) : ∀ x, lowerBallDensity μ x < ∞ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  apply finite_of_pointwise_logConcave
    (fun x y t ht0 ht1 => hμ.logConcave.lowerBallDensity_logConcave x y ht0 ht1)
    _ (lowerBallDensity_lt_top_ae μ)
  apply hμ.isotropic.affineSubspace_eq_top_of_ae_mem
  exact (lowerBallDensity_pos_ae μ).mono (fun x hx => subset_affineSpan ℝ _ hx)

/-- Isotropic compact-set log-concave probabilities are absolutely continuous
with respect to ambient Lebesgue measure. -/
theorem admissibleMeasure.absolutelyContinuousLebesgue {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) : AbsolutelyContinuousLebesgue μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hne : ∀ᵐ x ∂μ, volume.rnDeriv μ x ≠ 0 := by
    filter_upwards [lowerBallDensity_ae_eq_inv_rnDeriv μ] with x hx
    have hf := hμ.lowerBallDensity_lt_top x
    rw [hx, ENNReal.inv_lt_top] at hf
    exact hf.ne'
  apply Measure.ae_le_iff_absolutelyContinuous.mp
  intro s hs
  filter_upwards [Measure.ae_rnDeriv_ne_zero_imp_of_ae μ hs, hne] with x hx hn
  exact hx hn

/-- The canonical, measurable ball density represents every measure in the
original compact-set admissible class. Its pointwise values are all finite. -/
theorem admissibleMeasure.eq_withDensity_lowerBallDensity {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) : μ = volume.withDensity (lowerBallDensity μ) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  calc
    μ = volume.withDensity (μ.rnDeriv volume) :=
      (Measure.withDensity_rnDeriv_eq μ volume hμ.absolutelyContinuousLebesgue).symm
    _ = volume.withDensity (lowerBallDensity μ) :=
      withDensity_congr_ae (lowerBallDensity_ae_eq_rnDeriv μ).symm

end KLS
end

#print axioms KLS.finite_of_pointwise_logConcave
#print axioms KLS.admissibleMeasure.absolutelyContinuousLebesgue
#print axioms KLS.admissibleMeasure.eq_withDensity_lowerBallDensity
