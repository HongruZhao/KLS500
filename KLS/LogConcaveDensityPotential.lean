import KLS.Definitions

/-!
# Recovering the exact convex-potential density class

A measurable everywhere-finite pointwise log-concave density determines an
extended convex potential. Zero density becomes `+∞`; positivity everywhere
is not required. This is an algebraic endpoint of the measure-differentiation
route, not an assumption that an arbitrary measure already has such a density.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace KLS

def finiteDensityPotential (d : ℝ≥0∞) : WithTop ℝ :=
  if d = 0 then ⊤ else ((-Real.log d.toReal : ℝ) : WithTop ℝ)

theorem expNegPotential_finiteDensityPotential {d : ℝ≥0∞} (hd : d ≠ ⊤) :
    expNegPotential (finiteDensityPotential d) = d := by
  by_cases hz : d = 0
  · simp [finiteDensityPotential, hz, expNegPotential]
  · have hp : 0 < d.toReal := ENNReal.toReal_pos hz hd
    simp only [finiteDensityPotential, ite_eq_right hz, expNegPotential, neg_neg,
      Real.exp_log hp, ENNReal.ofReal_toReal hd]

theorem finiteDensityPotential_le_iff {d : ℝ≥0∞} (hd : d ≠ ⊤) (s : ℝ) :
    finiteDensityPotential d ≤ (s : WithTop ℝ) ↔
      ENNReal.ofReal (Real.exp (-s)) ≤ d := by
  by_cases hz : d = 0
  · simp [finiteDensityPotential, hz, Real.exp_pos]
  · have hp : 0 < d.toReal := ENNReal.toReal_pos hz hd
    rw [finiteDensityPotential, ite_eq_right hz, WithTop.coe_le_coe]
    rw [ENNReal.ofReal_le_iff_le_toReal hd, ← Real.exp_log hp, Real.exp_le_exp]
    simp only [Real.log_exp]
    constructor <;> intro h <;> linarith

theorem exp_neg_affine_eq_geometric (s u a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (Real.exp (-(a * s + b * u))) =
      ENNReal.ofReal (Real.exp (-s)) ^ a * ENNReal.ofReal (Real.exp (-u)) ^ b := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) ha,
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) hb,
    ← Real.exp_mul, ← Real.exp_mul,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

theorem extendedConvex_finiteDensityPotential {n : ℕ} {d : Space n → ℝ≥0∞}
    (hfinite : ∀ x, d x < ⊤)
    (hlog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      (d x) ^ t * (d y) ^ (1 - t) ≤ d (t • x + (1 - t) • y)) :
    ExtendedConvex (fun x => finiteDensityPotential (d x)) := by
  intro p hp q hq a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hq
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hp
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have ha1 : a < 1 := by linarith
  have hba : b = 1 - a := by linarith
  have hp' := (finiteDensityPotential_le_iff (hfinite p.1).ne p.2).mp hp
  have hq' := (finiteDensityPotential_le_iff (hfinite q.1).ne q.2).mp hq
  change finiteDensityPotential (d (a • p.1 + b • q.1)) ≤
    ((a * p.2 + b * q.2 : ℝ) : WithTop ℝ)
  apply (finiteDensityPotential_le_iff (hfinite _).ne _).mpr
  rw [exp_neg_affine_eq_geometric _ _ _ _ ha hb]
  calc
    ENNReal.ofReal (Real.exp (-p.2)) ^ a * ENNReal.ofReal (Real.exp (-q.2)) ^ b ≤
        (d p.1) ^ a * (d q.1) ^ b := by
      gcongr
    _ ≤ d (a • p.1 + b • q.1) := by
      rw [hba]
      exact hlog p.1 q.1 a ha' ha1

/-- An actual finite pointwise log-concave density gives the original Job45
convex-potential representation, including its zero-density boundary. -/
theorem hasLogConcaveDensity_of_pointwise {n : ℕ} {d : Space n → ℝ≥0∞}
    (hd : Measurable d) (hfinite : ∀ x, d x < ⊤)
    (hlog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      (d x) ^ t * (d y) ^ (1 - t) ≤ d (t • x + (1 - t) • y)) :
    HasLogConcaveDensity ((volume : Measure (Space n)).withDensity d) := by
  have heq : (fun x => expNegPotential (finiteDensityPotential (d x))) = d :=
    funext fun x => expNegPotential_finiteDensityPotential (hfinite x).ne
  exact ⟨(fun x => finiteDensityPotential (d x)),
    extendedConvex_finiteDensityPotential hfinite hlog, heq.symm ▸ hd,
    by rw [heq]⟩

end KLS
end

#print axioms KLS.finiteDensityPotential_le_iff
#print axioms KLS.extendedConvex_finiteDensityPotential
#print axioms KLS.hasLogConcaveDensity_of_pointwise
