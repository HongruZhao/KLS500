import KLS.MomentPrimalDualHarmonicLimit
import KLS.NormalizedRadialMeanValue

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma weighted_abs_integral_tendsto_zero_of_strong_L2
    {f : ℕ → Space n → ℝ} {g χ : Space n → ℝ}
    (hf : ∀ j, MemLp (f j) 2 volume) (hg : MemLp g 2 volume) (hχ : MemLp χ 2 volume)
    (hconv : Tendsto (fun j => eLpNorm (f j - g) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, χ x * |f j x - g x|) atTop (𝓝 0) := by
  have hn (j : ℕ) : MemLp (fun x => ‖f j x - g x‖) 2 volume := ((hf j).sub hg).norm
  have hz : MemLp (0 : Space n → ℝ) 2 volume := MemLp.zero
  have he (j : ℕ) : eLpNorm ((fun x => ‖f j x - g x‖) - (0 : Space n → ℝ)) 2 volume =
      eLpNorm (f j - g) 2 volume := by
    simp only [sub_zero]
    exact eLpNorm_norm _ ((hf j).sub hg).aestronglyMeasurable
  have hh := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero hn hz hχ (by simpa only [he] using hconv)
  simpa only [Real.norm_eq_abs, Pi.zero_apply, mul_zero, integral_zero] using hh

/-- A compact interior weight converts the genuine strong cutoff limit into
actual weighted L1 convergence to its almost-everywhere representative. -/
lemma weighted_abs_integral_tendsto_zero_of_strong_cutoff_limit
    {w : ℕ → Space n → ℝ} {χ₀ χ g h : Space n → ℝ} {U : Set (Space n)}
    (hw : ∀ j, Continuous (w j)) (hχ₀ : Continuous χ₀) (hχ₀c : HasCompactSupport χ₀)
    (hg : MemLp g 2 volume) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hU : MeasurableSet U) (hχs : tsupport χ ⊆ U) (hχone : ∀ x ∈ U, χ₀ x = 1)
    (hae : h =ᵐ[volume.restrict U] g)
    (hconv : Tendsto (fun j => eLpNorm ((fun x => χ₀ x * w j x) - g) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, χ x * |w j x - h x|) atTop (𝓝 0) := by
  have hf (j : ℕ) : MemLp (fun x => χ₀ x * w j x) 2 volume :=
    (hχ₀.mul (hw j)).memLp_of_hasCompactSupport hχ₀c.mul_right
  have hh := weighted_abs_integral_tendsto_zero_of_strong_L2 hf hg
    (hχ.memLp_of_hasCompactSupport hχc) hconv
  have he (j : ℕ) : (∫ x, χ x * |χ₀ x * w j x - g x|) = ∫ x, χ x * |w j x - h x| := by
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' hU).mp hae] with x hx
    by_cases hxu : x ∈ U
    · rw [hχone x hxu, one_mul, hx hxu]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hxu (hχs ht)), zero_mul, zero_mul]
  simpa only [he] using hh

end KLS
end
