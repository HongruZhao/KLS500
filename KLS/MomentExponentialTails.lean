import KLS.MomentLegendreEnergy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Exponential tails from actual finite Legendre energy

The Euclidean exponential kernel is proved integrable by comparison with a
product of one-dimensional exponential kernels. The resulting domination
turns the linear coercivity theorem into a genuine integral estimate.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

noncomputable section
namespace KLS

theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|)) := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr_fun _ measurableSet_Ioi
    intro x hx
    change Real.exp (-a * x) = Real.exp (-a * |x|)
    rw [abs_of_pos (show 0 < x from hx)]
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic ha 0).congr_fun _ measurableSet_Iic
    intro x hx
    change Real.exp (a * x) = Real.exp (-a * |x|)
    rw [abs_of_nonpos (show x ≤ 0 from hx)]
    congr 1
    ring
  simpa only [Iic_union_Ioi, integrableOn_univ] using hneg.union hpos

/-- Exponential decay in the Euclidean norm is genuinely integrable in every
finite dimension, including dimension zero. -/
theorem integrable_exp_neg_mul_norm (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space n => Real.exp (-a * ‖x‖)) := by
  let b : ℝ := a / (n + 1)
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hb : 0 < b := div_pos ha hn
  have hprod : Integrable (fun x : Space n => ∏ i : Fin n, Real.exp (-b * |x i|)) := by
    apply (PiLp.volume_preserving_toLp (Fin n)).integrable_comp (by fun_prop) |>.mp
    exact Integrable.fintype_prod (fun _ : Fin n => integrable_exp_neg_mul_abs hb)
  apply hprod.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hsum : (∑ i : Fin n, |x i|) ≤ (n : ℝ) * ‖x‖ := by
    calc
      _ ≤ ∑ _i : Fin n, ‖x‖ := Finset.sum_le_sum (fun i _ => by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i)
      _ = _ := by simp
  have hsum' : (∑ i : Fin n, |x i|) ≤ (n + 1 : ℝ) * ‖x‖ := by
    nlinarith [norm_nonneg x]
  have hmul := mul_le_mul_of_nonneg_left hsum' hb.le
  have hba : b * (n + 1) = a := div_mul_cancel₀ a hn.ne'
  rw [← mul_assoc, hba] at hmul
  rw [← Finset.mul_sum]
  nlinarith

theorem integral_exp_neg_mul_norm_pos (n : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < ∫ x : Space n, Real.exp (-a * ‖x‖) :=
  integral_exp_pos (integrable_exp_neg_mul_norm n ha)

/-- Actual Lebesgue partition function; integrability is proved before it is
used in the variational estimates below. -/
def momentPartitionFunction {n : ℕ} (φ : Space n → ℝ) : ℝ :=
  ∫ x : Space n, Real.exp (-φ x)

theorem exp_neg_le_exp_energy_mul_kernel {n : ℕ} {φ : Space n → ℝ}
    {a A t : ℝ} (hnonneg : ∀ x, 0 ≤ φ x) (hcone : ∀ x, a * ‖x‖ - A ≤ φ x)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Space n) :
    Real.exp (-φ x) ≤ Real.exp (t * A) * Real.exp (-(t * a) * ‖x‖) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_left (hcone x) ht
  have h₂ := mul_le_mul_of_nonneg_right ht1 (hnonneg x)
  nlinarith

theorem integrable_exp_neg_of_linear_coercivity {n : ℕ} {φ : Space n → ℝ}
    (hφ : AEStronglyMeasurable φ volume) {a A : ℝ} (ha : 0 < a)
    (hcone : ∀ x, a * ‖x‖ - A ≤ φ x) :
    Integrable (fun x : Space n => Real.exp (-φ x)) := by
  apply ((integrable_exp_neg_mul_norm n ha).const_mul (Real.exp A)).mono'
    (Real.continuous_exp.comp_aestronglyMeasurable hφ.neg)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change -φ x ≤ A + -a * ‖x‖
  have h := hcone x
  linarith

theorem momentPartitionFunction_le_exp_energy_mul_kernel
    {n : ℕ} {φ : Space n → ℝ} (hφ : AEStronglyMeasurable φ volume)
    {a A t : ℝ} (ha : 0 < a) (hnonneg : ∀ x, 0 ≤ φ x)
    (hcone : ∀ x, a * ‖x‖ - A ≤ φ x) (ht : 0 < t) (ht1 : t ≤ 1) :
    momentPartitionFunction φ ≤
      Real.exp (t * A) * (∫ x : Space n, Real.exp (-(t * a) * ‖x‖)) := by
  rw [momentPartitionFunction, ← integral_const_mul]
  exact integral_mono (integrable_exp_neg_of_linear_coercivity hφ ha hcone)
    ((integrable_exp_neg_mul_norm n (mul_pos ht ha)).const_mul (Real.exp (t * A)))
    (exp_neg_le_exp_energy_mul_kernel hnonneg hcone ht.le ht1)

end KLS
end

#print axioms KLS.integrable_exp_neg_mul_norm
#print axioms KLS.momentPartitionFunction_le_exp_energy_mul_kernel
