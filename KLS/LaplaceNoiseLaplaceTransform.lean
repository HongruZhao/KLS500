import KLS.LaplaceNoise

/-! The actual Laplace noise transform on its open convergence interval. -/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace KLS

lemma integrable_exp_mul_laplaceNoiseLaw {β t : ℝ} (hβ : 0 < β) (ht : |t| < β) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (laplaceNoiseLaw β) := by
  apply (integrable_exp_mul_abs_laplaceNoiseLaw hβ ht).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  simpa only [abs_mul] using le_abs_self (t * x)

lemma integral_exp_mul_laplaceNoiseLaw {β t : ℝ} (hβ : 0 < β) (ht : |t| < β) :
    (∫ x : ℝ, Real.exp (t * x) ∂laplaceNoiseLaw β) = β ^ 2 / (β ^ 2 - t ^ 2) := by
  have hplus : 0 < β + t := by linarith [(abs_lt.mp ht).1]
  have hminus : t - β < 0 := sub_neg.mpr ((abs_lt.mp ht).2)
  have hden : 0 < β ^ 2 - t ^ 2 := by
    nlinarith [mul_pos hplus (neg_pos.mpr hminus)]
  have hi := (integrable_laplaceNoiseLaw_iff hβ.le _).1
    (integrable_exp_mul_laplaceNoiseLaw hβ ht)
  rw [integral_laplaceNoiseLaw hβ.le,
    ← intervalIntegral.integral_Iic_add_Ioi (b := 0) hi.restrict hi.restrict]
  have hleft : (∫ x in Iic (0 : ℝ), laplaceNoiseDensity β x * Real.exp (t * x)) =
      β / 2 * (1 / (β + t)) := by
    calc
      _ = ∫ x in Iic (0 : ℝ), β / 2 * Real.exp ((β + t) * x) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x hx
        dsimp only [laplaceNoiseDensity]
        rw [abs_of_nonpos hx, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ = _ := by
        rw [integral_const_mul, integral_exp_mul_Iic hplus]
        simp
  have hright : (∫ x in Ioi (0 : ℝ), laplaceNoiseDensity β x * Real.exp (t * x)) =
      β / 2 * (-1 / (t - β)) := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), β / 2 * Real.exp ((t - β) * x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only [laplaceNoiseDensity]
        rw [abs_of_pos hx, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ = _ := by
        rw [integral_const_mul, integral_exp_mul_Ioi hminus]
        simp
  rw [hleft, hright]
  field_simp [hplus.ne', hminus.ne, hden.ne']
  ring

lemma contDiffAt_laplaceNoise_transform_zero {β : ℝ} (hβ : 0 < β) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => ∫ x, Real.exp (t * x) ∂laplaceNoiseLaw β) 0 := by
  have he : (fun t : ℝ => ∫ x, Real.exp (t * x) ∂laplaceNoiseLaw β) =ᶠ[𝓝 0]
      (fun t => β ^ 2 / (β ^ 2 - t ^ 2)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hβ] with t ht
    exact integral_exp_mul_laplaceNoiseLaw hβ (by simpa using ht)
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => β ^ 2 / (β ^ 2 - t ^ 2)) 0 :=
    contDiffAt_const.div (contDiffAt_const.sub (contDiffAt_id.pow 2))
      (by simpa using (pow_ne_zero 2 hβ.ne'))
  exact hs.congr_of_eventuallyEq he

end KLS
end
#print axioms KLS.integral_exp_mul_laplaceNoiseLaw
#print axioms KLS.contDiffAt_laplaceNoise_transform_zero
