import KLS.LocalTiltSmooth

/-! One genuine radial exponential moment supplies every polynomial moment
at each smaller rate, and hence actual local C∞ Laplace/log-Laplace maps. -/

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace KLS
variable {n : ℕ}

theorem localNormExponentialDomain_of_one_rate {μ : Measure (Space n)}
    {f : Space n → ℝ} {b r : ℝ} (hf : AEStronglyMeasurable f μ)
    (hi : Integrable (fun x => ‖f x‖ * Real.exp (b * ‖x‖)) μ) (hrb : r < b) :
    LocalNormExponentialDomain μ f r := by
  refine ⟨hf, ?_⟩
  intro m
  let C : ℝ := (m.factorial : ℝ) / (b-r)^m
  have hδ : 0 < b-r := sub_pos.mpr hrb
  have hpow : 0 < (b-r)^m := pow_pos hδ m
  apply (hi.const_mul C).mono' ((hf.norm.mul (continuous_norm.pow m).aestronglyMeasurable).mul
    (show Continuous (fun x : Space n => Real.exp (r * ‖x‖)) by fun_prop).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖‖f x‖ * ‖x‖ ^ m * Real.exp (r * ‖x‖)‖ ≤ C * (‖f x‖ * Real.exp (b * ‖x‖))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hp : ‖x‖^m ≤ C * Real.exp ((b-r) * ‖x‖) := by
    dsimp [C]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hpow).mpr
    have hh := (div_le_iff₀ hfac).mp
      (Real.pow_div_factorial_le_exp ((b-r) * ‖x‖) (mul_nonneg hδ.le (norm_nonneg x)) m)
    simpa only [mul_pow, mul_comm] using hh
  have he : Real.exp ((b-r) * ‖x‖) * Real.exp (r * ‖x‖) = Real.exp (b * ‖x‖) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ ‖f x‖ * (C * Real.exp ((b-r) * ‖x‖)) * Real.exp (r * ‖x‖) := by gcongr
    _ = C * (‖f x‖ * Real.exp (b * ‖x‖)) := by rw [← he]; ring

theorem contDiffAt_logLaplace_of_radial_exponential_moment {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    (hi : Integrable (fun x => Real.exp (b * ‖x‖)) μ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (tiltLogLaplace μ) 0 := by
  have hd : LocalNormExponentialDomain μ (fun _ => 1) (b/2) :=
    localNormExponentialDomain_of_one_rate aestronglyMeasurable_const
      (by simpa only [norm_one, one_mul] using hi) (by linarith)
  exact contDiffAt_logLaplace_of_localNormExponentialDomain hd (by simp; linarith)

end KLS
end
