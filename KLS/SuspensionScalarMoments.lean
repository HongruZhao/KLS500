import KLS.LaplaceNoise

/-! The centered and normalized extra coordinate on the actual product
probability space, and its cross moment with any orthogonal original variable. -/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace KLS

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

def suspensionExtra (F : E → ℝ) (σ : ℝ) (p : E × ℝ) : ℝ := (p.2 + F p.1) / σ

lemma memLp_suspensionExtra {F : E → ℝ} (hF : MemLp F 2 μ) {β : ℝ} (hβ : 0 < β)
    (σ : ℝ) : MemLp (suspensionExtra F σ) 2 (μ.prod (laplaceNoiseLaw β)) := by
  have : IsProbabilityMeasure (laplaceNoiseLaw β) := isProbabilityMeasure_laplaceNoiseLaw hβ
  have hη : MemLp (fun η : ℝ => η) 2 (laplaceNoiseLaw β) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (integrable_sq_laplaceNoiseLaw hβ)
  convert ((hη.comp_snd μ).add (hF.comp_fst (laplaceNoiseLaw β))).const_mul σ⁻¹ using 1
  ext p
  simp [suspensionExtra, div_eq_mul_inv, mul_comm]

lemma integral_suspensionExtra {F : E → ℝ} (hF : Integrable F μ)
    (hmean : (∫ x, F x ∂μ) = 0) {β : ℝ} (hβ : 0 < β) (σ : ℝ) :
    (∫ p, suspensionExtra F σ p ∂μ.prod (laplaceNoiseLaw β)) = 0 := by
  have : IsProbabilityMeasure (laplaceNoiseLaw β) := isProbabilityMeasure_laplaceNoiseLaw hβ
  unfold suspensionExtra
  rw [integral_div, integral_add ((integrable_id_laplaceNoiseLaw hβ).comp_snd μ)
    (hF.comp_fst (laplaceNoiseLaw β)), integral_fun_snd (fun η : ℝ => η), integral_fun_fst F,
    integral_id_laplaceNoiseLaw hβ, hmean]
  simp

lemma integral_sq_suspensionExtra {F : E → ℝ} (hF : MemLp F 2 μ)
    (hsq : (∫ x, (F x) ^ 2 ∂μ) = 1) {β : ℝ} (hβ : 0 < β) (σ : ℝ) :
    (∫ p, (suspensionExtra F σ p) ^ 2 ∂μ.prod (laplaceNoiseLaw β)) =
      (1 + 2 / β ^ 2) / σ ^ 2 := by
  have : IsProbabilityMeasure (laplaceNoiseLaw β) := isProbabilityMeasure_laplaceNoiseLaw hβ
  have hFi := hF.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hF2 : Integrable (fun x => F x ^ 2) μ := hF.integrable_sq
  have hcross : Integrable (fun p : E × ℝ => 2 * (F p.1 * p.2))
      (μ.prod (laplaceNoiseLaw β)) :=
    (hFi.mul_prod (integrable_id_laplaceNoiseLaw hβ)).const_mul 2
  have hsum : Integrable (fun p : E × ℝ => p.2 ^ 2 + 2 * (F p.1 * p.2))
      (μ.prod (laplaceNoiseLaw β)) :=
    ((integrable_sq_laplaceNoiseLaw hβ).comp_snd μ).add hcross
  have he (p : E × ℝ) : (suspensionExtra F σ p) ^ 2 =
      (p.2 ^ 2 + 2 * (F p.1 * p.2) + (F p.1) ^ 2) / σ ^ 2 := by
    unfold suspensionExtra
    rw [div_pow]
    congr 1
    ring
  simp_rw [he]
  rw [integral_div,
    integral_add hsum
      (hF2.comp_fst (laplaceNoiseLaw β)),
    integral_add ((integrable_sq_laplaceNoiseLaw hβ).comp_snd μ) hcross,
    integral_const_mul, integral_prod_mul F (fun η : ℝ => η),
    integral_fun_snd (fun η : ℝ => η ^ 2), integral_fun_fst (fun x => F x ^ 2),
    integral_id_laplaceNoiseLaw hβ,
    integral_sq_laplaceNoiseLaw hβ, hsq]
  simp only [mul_zero, probReal_univ, one_smul, add_zero]
  rw [add_comm]

lemma integral_mul_suspensionExtra {F a : E → ℝ} (hF : MemLp F 2 μ)
    (ha : MemLp a 2 μ) (horth : (∫ x, a x * F x ∂μ) = 0)
    {β : ℝ} (hβ : 0 < β) (σ : ℝ) :
    (∫ p : E × ℝ, a p.1 * suspensionExtra F σ p ∂μ.prod (laplaceNoiseLaw β)) = 0 := by
  have : IsProbabilityMeasure (laplaceNoiseLaw β) := isProbabilityMeasure_laplaceNoiseLaw hβ
  have hai := ha.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcross := hai.mul_prod (integrable_id_laplaceNoiseLaw hβ)
  have hsame : Integrable (fun p : E × ℝ => a p.1 * F p.1) (μ.prod (laplaceNoiseLaw β)) :=
    (ha.integrable_mul hF).comp_fst (laplaceNoiseLaw β)
  have he (p : E × ℝ) : a p.1 * suspensionExtra F σ p =
      (a p.1 * p.2 + a p.1 * F p.1) / σ := by
    unfold suspensionExtra
    ring
  simp_rw [he]
  rw [integral_div, integral_add hcross hsame, integral_prod_mul a (fun η : ℝ => η),
    integral_fun_fst (fun x => a x * F x), integral_id_laplaceNoiseLaw hβ, horth]
  simp

end KLS
end
#print axioms KLS.integral_sq_suspensionExtra
#print axioms KLS.integral_mul_suspensionExtra
