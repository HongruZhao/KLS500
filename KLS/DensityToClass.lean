import KLS.PrekopaLeindler
import KLS.ClassToDensity

/-!
# The converse density-to-measure log-concavity bridge

The actual Prékopa--Leindler theorem applied to density-weighted indicators
proves compact-set log-concavity. Convexity of the exact extended potential
implies the necessary pointwise density inequality, including zero densities.
Together with the previously proved forward bridge, the two full classes
are equivalent.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace KLS

theorem measureLogConcave_withDensity_of_pointwise {n : ℕ} {d : Space n → ℝ≥0∞}
    (hd : Measurable d)
    (hlog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      d x ^ t * d y ^ (1 - t) ≤ d (t • x + (1 - t) • y)) :
    measureLogConcave ((volume : Measure (Space n)).withDensity d) := by
  intro E F hE hF t ht0 ht1
  have hZ := measurableSet_affineSetCombination t hE hF
  rw [withDensity_apply d hE.measurableSet,
    withDensity_apply d hF.measurableSet, withDensity_apply d hZ]
  have hp := prekopaLeindler (hd.indicator hE.measurableSet)
    (hd.indicator hF.measurableSet) (hd.indicator hZ) ht0 ht1
    (show ∀ x y, (E.indicator d x) ^ t * (F.indicator d y) ^ (1 - t) ≤
      (affineSetCombination t E F).indicator d (t • x + (1 - t) • y) from by
      intro x y
      by_cases hx : x ∈ E
      · by_cases hy : y ∈ F
        · have hz : t • x + (1 - t) • y ∈ affineSetCombination t E F :=
            ⟨(x, y), ⟨hx, hy⟩, rfl⟩
          simpa only [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hz] using
            hlog x y t ht0 ht1
        · simp only [indicator_of_notMem hy, ENNReal.zero_rpow_of_pos (sub_pos.mpr ht1), mul_zero]
          exact zero_le
      · simp only [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos ht0, zero_mul]
        exact zero_le)
  simpa only [lintegral_indicator hE.measurableSet, lintegral_indicator hF.measurableSet,
    lintegral_indicator hZ] using hp

/-- The exact epigraph definition implies pointwise log-concavity of exp(-V),
including points where V is positive infinity. -/
theorem ExtendedConvex.expNegPotential_logConcave {n : ℕ} {V : Space n → WithTop ℝ}
    (hV : ExtendedConvex V) (x y : Space n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    expNegPotential (V x) ^ t * expNegPotential (V y) ^ (1 - t) ≤
      expNegPotential (V (t • x + (1 - t) • y)) := by
  by_cases hx : V x = ⊤
  · simp only [hx, expNegPotential, ENNReal.zero_rpow_of_pos ht0, zero_mul]
    exact zero_le
  by_cases hy : V y = ⊤
  · simp only [hy, expNegPotential, ENNReal.zero_rpow_of_pos (sub_pos.mpr ht1), mul_zero]
    exact zero_le
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hy
  have hp : (x, a) ∈ {p : Space n × ℝ | V p.1 ≤ (p.2 : WithTop ℝ)} := by
    change V x ≤ (a : WithTop ℝ)
    exact le_of_eq ha.symm
  have hq : (y, b) ∈ {p : Space n × ℝ | V p.1 ≤ (p.2 : WithTop ℝ)} := by
    change V y ≤ (b : WithTop ℝ)
    exact le_of_eq hb.symm
  have hz := hV hp hq ht0.le (sub_pos.mpr ht1).le (by ring : t + (1 - t) = 1)
  change V (t • x + (1 - t) • y) ≤ ((t * a + (1 - t) * b : ℝ) : WithTop ℝ) at hz
  have hztop : V (t • x + (1 - t) • y) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hz
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hztop
  rw [← hc, WithTop.coe_le_coe] at hz
  rw [← ha, ← hb, ← hc]
  change ENNReal.ofReal (Real.exp (-a)) ^ t *
    ENNReal.ofReal (Real.exp (-b)) ^ (1 - t) ≤ ENNReal.ofReal (Real.exp (-c))
  rw [← exp_neg_affine_eq_geometric a b t (1 - t) ht0.le (sub_pos.mpr ht1).le]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hz))

theorem HasLogConcaveDensity.measureLogConcave {n : ℕ} {μ : Measure (Space n)}
    (hμ : HasLogConcaveDensity μ) : measureLogConcave μ := by
  obtain ⟨V, hV, hm, rfl⟩ := hμ
  exact measureLogConcave_withDensity_of_pointwise hm
    (fun x y _ ht0 ht1 => hV.expNegPotential_logConcave x y ht0 ht1)

/-- Exact original Job45 hypotheses imply the requested compact-set class. -/
theorem IsKLSMeasure.admissibleMeasure {n : ℕ} {μ : Measure (Space n)}
    (hμ : IsKLSMeasure μ) : admissibleMeasure μ :=
  ⟨hμ.isProb, hμ.logConcave.measureLogConcave, hμ.isotropic⟩

/-- Full equivalence, with no additional regularity or support restriction. -/
theorem admissibleMeasure_iff_isKLSMeasure {n : ℕ} {μ : Measure (Space n)} :
    admissibleMeasure μ ↔ IsKLSMeasure μ :=
  ⟨admissibleMeasure.isKLSMeasure, IsKLSMeasure.admissibleMeasure⟩

end KLS
end

#print axioms KLS.measureLogConcave_withDensity_of_pointwise
#print axioms KLS.ExtendedConvex.expNegPotential_logConcave
#print axioms KLS.HasLogConcaveDensity.measureLogConcave
#print axioms KLS.admissibleMeasure_iff_isKLSMeasure
