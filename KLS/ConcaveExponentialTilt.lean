import KLS.DensityToClass
import KLS.LogConcavityRestriction
import KLS.TiltedMeasure

/-! Concave exponential tilting preserves the literal compact-set measure class. -/
open MeasureTheory Set
open scoped ENNReal Topology
noncomputable section
namespace KLS
variable {n : ℕ}

theorem exponentialWeight_logConcave {q : Space n → ℝ} (hq : ConcaveOn ℝ univ q)
    (x y : Space n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ENNReal.ofReal (Real.exp (q x)) ^ t * ENNReal.ofReal (Real.exp (q y)) ^ (1-t) ≤
      ENNReal.ofReal (Real.exp (q (t • x + (1-t) • y))) := by
  have hh := hq.2 (mem_univ x) (mem_univ y) ht0.le (sub_nonneg.mpr ht1.le)
    (by ring : t+(1-t)=1)
  change t * q x + (1-t) * q y ≤ q (t • x + (1-t) • y) at hh
  calc
    _ = ENNReal.ofReal (Real.exp (t * q x + (1-t) * q y)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) ht0.le,
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr ht1.le),
        ← Real.exp_mul, ← Real.exp_mul, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hh)

/-- The original density is multiplied by the actual exponential weight and
normalized by the actual partition function. Prékopa--Leindler then proves
compact-set measure log-concavity, including a zero normalization if necessary. -/
theorem HasLogConcaveDensity.measureLogConcave_tilted {μ : Measure (Space n)}
    (hμ : HasLogConcaveDensity μ) {q : Space n → ℝ} (hc : Continuous q)
    (hq : ConcaveOn ℝ univ q) : KLS.measureLogConcave (μ.tilted q) := by
  obtain ⟨V, hV, hd, hrep⟩ := hμ
  let d : Space n → ℝ≥0∞ := fun x => expNegPotential (V x)
  let w : Space n → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (q x))
  let C : ℝ≥0∞ := ENNReal.ofReal (∫ x, Real.exp (q x) ∂μ)⁻¹
  have hw : Measurable w := (Real.continuous_exp.comp hc).measurable.ennreal_ofReal
  have hn : μ.tilted q = C • μ.withDensity w := by
    rw [Measure.tilted, ← withDensity_smul C hw]
    congr 1
    funext x
    change ENNReal.ofReal (Real.exp (q x) / ∫ x, Real.exp (q x) ∂μ) =
      C * ENNReal.ofReal (Real.exp (q x))
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact mul_comm _ _
  have hprod : KLS.measureLogConcave ((volume : Measure (Space n)).withDensity (d*w)) := by
    apply measureLogConcave_withDensity_of_pointwise (hd.mul hw)
    intro x y t ht0 ht1
    change (d x*w x)^t * (d y*w y)^(1-t) ≤ d (t•x+(1-t)•y)*w (t•x+(1-t)•y)
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le,
      ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr ht1.le)]
    calc
      _ = (d x^t*d y^(1-t))*(w x^t*w y^(1-t)) := by ac_rfl
      _ ≤ _ := mul_le_mul' (hV.expNegPotential_logConcave x y ht0 ht1)
        (exponentialWeight_logConcave hq x y ht0 ht1)
  rw [hn, hrep, ← withDensity_mul volume hd hw]
  exact hprod.smul C

end KLS
end
#print axioms KLS.HasLogConcaveDensity.measureLogConcave_tilted
