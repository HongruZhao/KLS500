import KLS.EnergyProductIntegrals
import Mathlib.MeasureTheory.Function.L2Space

/-! Cauchy--Schwarz for genuine finite tensor fields on any measure space. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X] {ν : Measure X}

theorem abs_dotProduct_le_sqrt (a b : ι → ℝ) :
    |a ⬝ᵥ b| ≤ Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have ha := dotProduct_self_nonnegative a
  have hb := dotProduct_self_nonnegative b
  have hs : (Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b))^2 = (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
  have hc : (a ⬝ᵥ b)^2 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
    simpa only [dotProduct, ← pow_two] using hh
  nlinarith [sq_abs (a ⬝ᵥ b), abs_nonneg (a ⬝ᵥ b),
    mul_nonneg (Real.sqrt_nonneg (a ⬝ᵥ a)) (Real.sqrt_nonneg (b ⬝ᵥ b))]

theorem integral_sqrt_mul_le {e l : X → ℝ} (he : Integrable e ν) (hl : Integrable l ν)
    (he0 : ∀ x, 0 ≤ e x) (hl0 : ∀ x, 0 ≤ l x) :
    Integrable (fun x => Real.sqrt (e x) * Real.sqrt (l x)) ν ∧
      (∫ x, Real.sqrt (e x) * Real.sqrt (l x) ∂ν) ≤
        Real.sqrt (∫ x, e x ∂ν) * Real.sqrt (∫ x, l x ∂ν) := by
  have hes : MemLp (fun x => Real.sqrt (e x)) 2 ν := by
    apply (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable he.aestronglyMeasurable)).mpr
    simpa only [Real.sq_sqrt (he0 _)] using he
  have hls : MemLp (fun x => Real.sqrt (l x)) 2 ν := by
    apply (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hl.aestronglyMeasurable)).mpr
    simpa only [Real.sq_sqrt (hl0 _)] using hl
  refine ⟨hes.integrable_mul hls, ?_⟩
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => Real.sqrt_nonneg (e x))
    (Eventually.of_forall fun x => Real.sqrt_nonneg (l x))
    (by simpa using hes) (by simpa using hls)
  simp only [Real.rpow_two, Real.sq_sqrt (he0 _), Real.sq_sqrt (hl0 _)] at hh
  have hs (x : ℝ) : x ^ (2⁻¹ : ℝ) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  simpa only [one_div, hs] using hh

theorem integrable_cross_of_energies {e l c : X → ℝ}
    (he : Integrable e ν) (hl : Integrable l ν)
    (he0 : ∀ x, 0 ≤ e x) (hl0 : ∀ x, 0 ≤ l x)
    (hc : AEStronglyMeasurable c ν)
    (hbound : ∀ x, |c x| ≤ Real.sqrt (e x) * Real.sqrt (l x)) :
    Integrable c ν ∧ (∫ x, c x ∂ν) ≤
      Real.sqrt (∫ x, e x ∂ν) * Real.sqrt (∫ x, l x ∂ν) := by
  obtain ⟨hprod, hcs⟩ := integral_sqrt_mul_le he hl he0 hl0
  have hi : Integrable c ν := hprod.mono' hc (Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hbound x)
  refine ⟨hi, (integral_mono hi hprod fun x => (le_abs_self _).trans (hbound x)).trans hcs⟩

end KLS.TensorEnergy
end
