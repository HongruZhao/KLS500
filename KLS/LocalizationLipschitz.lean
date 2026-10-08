import KLS.LocalizationTilt
import Mathlib.Analysis.Calculus.MeanValue

/-! A global state-Lipschitz bound for the actual mean of the normalized law,
uniform over all real times, derived solely from a radius containing the support. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
noncomputable section
namespace KLS.StandardLocalization

variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def score (v : Fin n → ℝ) (x : Space n) : ℝ := ∑ i, v i * x i

theorem continuous_score (v : Fin n → ℝ) : Continuous (score v) := by unfold score; fun_prop

theorem exponent_line (t : ℝ) (c v : Fin n → ℝ) (u : ℝ) (x : Space n) :
    exponent t (c + u • v) x = exponent t c x + u * score v x := by
  simp only [exponent, score, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-- The directional derivative is the actual covariance with the linear score. -/
theorem hasDerivAt_mean_line (hμ : IsCompact μ.support)
    (t : ℝ) (c v : Fin n → ℝ) (i : Fin n) (u : ℝ) :
    HasDerivAt (fun s => mean μ t (c + s • v) i)
      (ProbabilityTheory.covariance (fun x : Space n => x i) (score v)
        (law μ t (c + u • v))) u := by
  have hfi : Integrable (fun x : Space n => x i) μ :=
    integrable_of_continuous_compact_support_measure hμ (by fun_prop)
  have hd := hasDerivAt_tiltAverage hμ (continuous_exponent_state t c) (continuous_score v) hfi u
  letI : IsProbabilityMeasure (μ.tilted (exponent t (c + u • v))) :=
    law_isProbability hμ t (c + u • v)
  have hc := ProbabilityTheory.covariance_eq_sub
    (memLp_two_continuous_tilted hμ (continuous_exponent_state t (c + u • v))
      (f := fun x => x i) (by fun_prop))
    (memLp_two_continuous_tilted hμ (continuous_exponent_state t (c + u • v)) (continuous_score v))
  change HasDerivAt (fun s => mean μ t (c + s • v) i)
    (ProbabilityTheory.covariance (fun x : Space n => x i) (score v)
      (μ.tilted (exponent t (c + u • v)))) u
  rw [hc]
  have hline (s : ℝ) : exponent t (c + s • v) = fun x => exponent t c x + s * score v x := by
    funext x
    exact exponent_line t c v s x
  simpa only [mean, law, tiltAverage, hline, Pi.mul_apply] using hd

/-- An elementary bound on a true covariance under a probability law. -/
theorem norm_covariance_le_of_bounds {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsProbabilityMeasure ν] {f g : α → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfA : ∀ᵐ x ∂ν, ‖f x‖ ≤ A) (hgB : ∀ᵐ x ∂ν, ‖g x‖ ≤ B) :
    ‖ProbabilityTheory.covariance f g ν‖ ≤ 2 * A * B := by
  have hfi : ‖∫ x, f x ∂ν‖ ≤ A := by simpa using norm_integral_le_of_norm_le_const hfA
  have hgi : ‖∫ x, g x ∂ν‖ ≤ B := by simpa using norm_integral_le_of_norm_le_const hgB
  have hfg : ‖∫ x, f x * g x ∂ν‖ ≤ A * B := by
    have hb : ∀ᵐ x ∂ν, ‖f x * g x‖ ≤ A * B := by
      filter_upwards [hfA, hgB] with x hx hy
      rw [norm_mul]
      exact mul_le_mul hx hy (norm_nonneg _) hA
    simpa using norm_integral_le_of_norm_le_const hb
  rw [ProbabilityTheory.covariance_eq_sub hf hg]
  calc ‖(∫ x, f x * g x ∂ν) - (∫ x, f x ∂ν) * ∫ x, g x ∂ν‖
      ≤ ‖∫ x, f x * g x ∂ν‖ + ‖(∫ x, f x ∂ν) * ∫ x, g x ∂ν‖ := norm_sub_le _ _
    _ ≤ A * B + A * B := by
      apply add_le_add hfg
      rw [norm_mul]
      exact mul_le_mul hfi hgi (norm_nonneg _) hA
    _ = 2 * A * B := by ring

theorem abs_score_le {R : ℝ} (hR : 0 ≤ R) (v : Fin n → ℝ) (x : Space n) (hx : ‖x‖ ≤ R) :
    |score v x| ≤ Real.sqrt (n : ℝ) * ‖v‖ * R := by
  change |∑ i, v i * x i| ≤ _
  rw [← inner_toSpace_eq]
  exact (abs_real_inner_le_norm (toSpace v) x).trans
    (mul_le_mul (norm_toSpace_le v) hx (norm_nonneg _) (by positivity))

theorem norm_covariance_score_le (hμ : IsCompact μ.support) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R) (t : ℝ) (c v : Fin n → ℝ) (i : Fin n) :
    ‖ProbabilityTheory.covariance (fun x : Space n => x i) (score v) (law μ t c)‖ ≤
      (2 * R ^ 2 * Real.sqrt (n : ℝ)) * ‖v‖ := by
  letI : IsProbabilityMeasure (μ.tilted (exponent t c)) := law_isProbability hμ t c
  have hfA : ∀ᵐ x ∂law μ t c, ‖x i‖ ≤ R :=
    (ae_norm_le hμ hR t c).mono fun x hx => (PiLp.norm_apply_le x i).trans hx
  have hgB : ∀ᵐ x ∂law μ t c, ‖score v x‖ ≤ Real.sqrt (n : ℝ) * ‖v‖ * R :=
    (ae_norm_le hμ hR t c).mono fun x hx => by
      simpa only [Real.norm_eq_abs] using abs_score_le hR0 v x hx
  have h := norm_covariance_le_of_bounds
    (memLp_two_continuous_tilted hμ (continuous_exponent_state t c) (by fun_prop))
    (memLp_two_continuous_tilted hμ (continuous_exponent_state t c) (continuous_score v))
    hR0 (by positivity) hfA hgB
  calc _ ≤ 2 * R * (Real.sqrt (n : ℝ) * ‖v‖ * R) := by simpa only [law] using h
    _ = _ := by ring

/-- The bound is uniform in time; in particular it is uniform on every finite nonnegative window. -/
theorem norm_mean_sub_le (hμ : IsCompact μ.support) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R) (t : ℝ) (c₁ c₂ : Fin n → ℝ) :
    ‖mean μ t c₁ - mean μ t c₂‖ ≤
      (2 * R ^ 2 * Real.sqrt (n : ℝ)) * ‖c₁ - c₂‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hd (u : ℝ) := hasDerivAt_mean_line hμ t c₂ (c₁ - c₂) i u
  have hbound (u : ℝ) := norm_covariance_score_le hμ hR0 hR t
    (c₂ + u • (c₁ - c₂)) (c₁ - c₂) i
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun u _ => (hd u).hasDerivWithinAt) (fun u _ => hbound u)
  simpa only [one_smul, zero_smul, add_zero, add_sub_cancel, Pi.sub_apply] using h

/-- Each covariance entry is bounded by the same compact support radius. -/
theorem norm_covariance_entry_le (hμ : IsCompact μ.support) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R) (t : ℝ) (c : Fin n → ℝ) (i j : Fin n) :
    ‖covariance μ t c i j‖ ≤ 2 * R ^ 2 := by
  letI : IsProbabilityMeasure (μ.tilted (exponent t c)) := law_isProbability hμ t c
  have hb (k : Fin n) : ∀ᵐ x ∂law μ t c, ‖x k‖ ≤ R :=
    (ae_norm_le hμ hR t c).mono fun x hx => (PiLp.norm_apply_le x k).trans hx
  have h := norm_covariance_le_of_bounds
    (memLp_two_continuous_tilted hμ (continuous_exponent_state t c) (by fun_prop))
    (memLp_two_continuous_tilted hμ (continuous_exponent_state t c) (by fun_prop)) hR0 hR0 (hb i) (hb j)
  calc _ ≤ 2 * R * R := by simpa only [covariance, law] using h
    _ = _ := by ring

end KLS.StandardLocalization
end
#print axioms KLS.StandardLocalization.hasDerivAt_mean_line
#print axioms KLS.StandardLocalization.norm_mean_sub_le
#print axioms KLS.StandardLocalization.norm_covariance_entry_le
