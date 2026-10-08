import KLS.ScalarUpperCutoff

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Compact testing of the literal elliptic subsolution gives a vanishing
cutoff error using only integrability of its actual gradient norm. -/
theorem weighted_subsolution_cutoff_integral_le {φ f χ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f)
    (hχ : ContDiff ℝ 1 χ) (hcompact : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) {c : ℝ}
    (hc : ∀ x, ‖gradient χ x‖ ≤ c)
    {t : ℝ} (ht : 0 < t) (hsub : ∀ x, f x - t * weightedDiffusion φ f x ≤ 0)
    (hgrad : Integrable (fun x => ‖gradient f x‖) (potentialMeasure φ)) :
    (∫ x, χ x ^ 2*(f x*smoothUpperTest f 0 x) ∂potentialMeasure φ) ≤
      2*t*c*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  let ζ := fun x => χ x ^ 2*smoothUpperTest f 0 x
  have hζ : ContDiff ℝ 1 ζ := (hχ.pow 2).mul (smoothUpperTest_contDiff hf1 0)
  have hcχ : HasCompactSupport (fun x => χ x ^ 2) := by
    simpa only [pow_two,Pi.mul_def] using hcompact.mul_right (f' := χ)
  have hcζ : HasCompactSupport ζ := hcχ.mul_right
  have hIf : Integrable (fun x => ζ x*f x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hζ.continuous.mul hf.continuous) hcζ.mul_right
  have hIL : Integrable (fun x => ζ x*weightedDiffusion φ f x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hζ.continuous.mul (contDiff_weightedDiffusion hφ hf).continuous) hcζ.mul_right
  have hIp : Integrable (fun x => inner ℝ (gradient ζ x) (gradient f x))
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((continuous_gradient_of_contDiff hζ).inner (continuous_gradient_of_contDiff hf1))
      (by
        apply HasCompactSupport.of_support_subset_isCompact (hasCompactSupport_gradient hcζ)
        intro x hx
        by_contra hn
        have hz : gradient ζ x = 0 := image_eq_zero_of_notMem_tsupport hn
        exact hx (by simp only [hz,inner_zero_left]))
  have hibp := integral_mul_weightedDiffusion_of_hasCompactSupport_left
    (hφ.of_le (by norm_num)) hζ (hf.of_le (by norm_num)) hcζ
  have hraw : (∫ x, ζ x*(f x-t*weightedDiffusion φ f x) ∂potentialMeasure φ) ≤ 0 :=
    integral_nonpos fun x => mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (sq_nonneg _) (smoothUpperTest_nonneg _ _ _)) (hsub x)
  have hsplit : (∫ x, ζ x*(f x-t*weightedDiffusion φ f x) ∂potentialMeasure φ) =
      (∫ x, ζ x*f x ∂potentialMeasure φ) -
        t*(∫ x, ζ x*weightedDiffusion φ f x ∂potentialMeasure φ) := by
    calc
      _ = ∫ x, ζ x*f x-t*(ζ x*weightedDiffusion φ f x) ∂potentialMeasure φ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := by rw [integral_sub hIf (hIL.const_mul t),integral_const_mul]
  rw [hsplit,hibp] at hraw
  have hmass : (∫ x, ζ x*f x ∂potentialMeasure φ) =
      ∫ x, χ x ^ 2*(f x*smoothUpperTest f 0 x) ∂potentialMeasure φ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp [ζ];ring
  rw [hmass] at hraw
  have herr := integral_mono (hgrad.const_mul (-2*c)) hIp (fun x => by
    simpa only [neg_mul,mul_assoc] using
      smoothUpperTest_cutoff_gradient_pairing_lower hf1 hχ hχ0 hχ1 hc x)
  rw [integral_const_mul] at herr
  have hm := mul_le_mul_of_nonneg_left herr ht.le
  nlinarith

/-- A genuine global elliptic subsolution with integrable value and actual
gradient norm is nonpositive. No boundedness or diffusion-domain premise is used. -/
theorem nonpos_of_weighted_resolvent_subsolution {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f)
    {t : ℝ} (ht : 0 < t) (hsub : ∀ x, f x - t * weightedDiffusion φ f x ≤ 0)
    (hI : Integrable f (potentialMeasure φ))
    (hgrad : Integrable (fun x => ‖gradient f x‖) (potentialMeasure φ)) :
    ∀ x, f x ≤ 0 := by
  obtain ⟨hD,hD0,hDpos⟩ := smoothUpperTest_zero_defect hf.continuous hI
  obtain ⟨K,hK,hbound⟩ := smoothCutoff_gradient_bound (n := n)
  have hlim := integral_smoothCutoff_sq_tendsto hD hD0
  have herr : Tendsto
      (fun k => 2*t*(cutoffScale k*K)*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ))
      atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using
      ((cutoffScale_tendsto_zero.mul_const K).const_mul (2*t)).mul_const
        (∫ x, ‖gradient f x‖ ∂potentialMeasure φ)
  have hB (k : ℕ) := weighted_subsolution_cutoff_integral_le hφ hf
    ((smoothCutoff_contDiff k).of_le (by simp)) (smoothCutoff_hasCompactSupport k)
    (fun x => (faithfulCutoff_bounds k x).1) (fun x => (faithfulCutoff_bounds k x).2)
    (hbound k) ht hsub hgrad
  have hz : (∫ x, f x*smoothUpperTest f 0 x ∂potentialMeasure φ) = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto hlim herr (Eventually.of_forall hB))
      (integral_nonneg hD0)
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hD0) hD).mp hz
  apply continuous_le_const_of_ae_potentialMeasure hφ.continuous hf.continuous
  filter_upwards [hae] with x hx
  by_contra hn
  have hp := hDpos x (lt_of_not_ge hn)
  change f x*smoothUpperTest f 0 x = 0 at hx
  linarith

end KLS
end
