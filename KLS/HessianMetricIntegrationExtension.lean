import KLS.HessianMetricCutoffSequence
import KLS.HessianMetricIntegrationRight

/-!
# Integration extension for bounded diffusion subsolutions

The actual cutoffs imply integrability before any unrestricted integral
identity is used. A Fatou argument controls the nonnegative function `Lf + a f`;
then dominated convergence and compact-test symmetry give `∫ Lf = 0`.
-/

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff

noncomputable section
namespace KLS

/-- A generic Fatou consequence, valid on an arbitrary measurable domain. -/
lemma integrable_of_tendsto_integral_norm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : ℕ → α → ℝ} {f : α → ℝ} {r : ℝ}
    (hf : AEStronglyMeasurable f μ) (hF : ∀ k, Integrable (F k) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 (f x)))
    (hint : Tendsto (fun k => ∫ x, ‖F k x‖ ∂μ) atTop (𝓝 r)) :
    Integrable f μ := by
  have hfatou : (∫⁻ x, ‖f x‖ₑ ∂μ) ≤
      liminf (fun k => ∫⁻ x, ‖F k x‖ₑ ∂μ) atTop := by
    calc
      (∫⁻ x, ‖f x‖ₑ ∂μ) = ∫⁻ x, liminf (fun k => ‖F k x‖ₑ) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact hx.enorm.liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' (fun k => (hF k).aestronglyMeasurable.aemeasurable.enorm)
  have hlim' : Tendsto (fun k => ∫⁻ x, ‖F k x‖ₑ ∂μ) atTop (𝓝 (ENNReal.ofReal r)) := by
    convert! ENNReal.continuous_ofReal.continuousAt.tendsto.comp hint using 1
    funext k
    exact (ofReal_integral_norm_eq_lintegral_enorm (hF k)).symm
  refine ⟨hf, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  exact lt_of_le_of_lt hfatou (hlim'.liminf_eq ▸ ENNReal.ofReal_lt_top)

variable {n : ℕ}

/-- The A.5 integration extension for the actual Hessian diffusion. All cutoff
and integrability facts are conclusions of the genuine potential assumptions. -/
theorem integrable_hessianMetricDiffusion_and_integral_eq_zero
    {φ V f : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hconv : ConvexOn ℝ univ φ) [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hgrad : Bornology.IsBounded (range (gradient φ)))
    (hf : ContDiff ℝ 2 f) {B a : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (hsub : ∀ x, 0 ≤ hessianMetricDiffusion φ V f x + a * f x) :
    Integrable (hessianMetricDiffusion φ V f) (potentialMeasure φ) ∧
      (∫ x, hessianMetricDiffusion φ V f x ∂potentialMeasure φ) = 0 := by
  obtain ⟨x₀, _, hχ, _, hχlim, hχL, hχerr⟩ :=
    exists_hessianMetricCutoffSequence hφ hV hconv hpos hMA hgrad
  let χ := hessianMetricCutoffSequence φ x₀
  let L := hessianMetricDiffusion φ V f
  let G : Space n → ℝ := fun x => L x + a * f x
  have hLcont : Continuous L := continuous_hessianMetricDiffusion hφ hV hf hpos
  have hGcont : Continuous G := hLcont.add (continuous_const.mul hf.continuous)
  have hfi : Integrable f (potentialMeasure φ) :=
    (integrable_const B).mono' hf.continuous.aestronglyMeasurable (Eventually.of_forall hB)
  have hχnorm (k : ℕ) (x : Space n) : ‖χ k x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (((hχ k).2.2 x).1)]
    exact ((hχ k).2.2 x).2
  have hχfi (k : ℕ) : Integrable (fun x => χ k x * f x) (potentialMeasure φ) :=
    hfi.bdd_mul (hχ k).1.continuous.aestronglyMeasurable
      (Eventually.of_forall (hχnorm k))
  have hχLi (k : ℕ) : Integrable (fun x => χ k x * L x) (potentialMeasure φ) :=
    (hessianMetricIntegrability_of_hasCompactSupport_left hφ hV hpos
      ((hχ k).1.of_le (by norm_num)) hf (hχ k).2.1).1
  have hfχLi (k : ℕ) : Integrable
      (fun x => f x * hessianMetricDiffusion φ V (χ k) x) (potentialMeasure φ) :=
    (hχL k).bdd_mul hf.continuous.aestronglyMeasurable (Eventually.of_forall hB)
  have hcomm (k : ℕ) : (∫ x, χ k x * L x ∂potentialMeasure φ) =
      ∫ x, f x * hessianMetricDiffusion φ V (χ k) x ∂potentialMeasure φ :=
    (integral_mul_hessianMetricDiffusion_comm_of_hasCompactSupport_right
      hφ hV hpos hMA hf (hχ k).1 (hχ k).2.1).symm
  have herror : Tendsto
      (fun k => ∫ x, f x * hessianMetricDiffusion φ V (χ k) x ∂potentialMeasure φ)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (show Tendsto (fun k => B * ∫ x, ‖hessianMetricDiffusion φ V (χ k) x‖
        ∂potentialMeasure φ) atTop (𝓝 0) by simpa using hχerr.const_mul B)
    calc
      ‖∫ x, f x * hessianMetricDiffusion φ V (χ k) x ∂potentialMeasure φ‖ ≤
          ∫ x, ‖f x * hessianMetricDiffusion φ V (χ k) x‖ ∂potentialMeasure φ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x, B * ‖hessianMetricDiffusion φ V (χ k) x‖ ∂potentialMeasure φ := by
        apply integral_mono (hfχLi k).norm ((hχL k).norm.const_mul B)
        intro x
        dsimp only
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  have htestlim : Tendsto (fun k => ∫ x, χ k x * f x ∂potentialMeasure φ)
      atTop (𝓝 (∫ x, f x ∂potentialMeasure φ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun k => (hχfi k).aestronglyMeasurable) hfi.norm
    · intro k
      filter_upwards [] with x
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχnorm k x)
    · filter_upwards [] with x
      simpa only [one_mul] using (hχlim x).mul_const (f x)
  have hχGi (k : ℕ) : Integrable (fun x => χ k x * G x) (potentialMeasure φ) := by
    convert! (hχLi k).add ((hχfi k).const_mul a) using 1
    funext x
    dsimp [G]
    ring
  have hχGint (k : ℕ) : (∫ x, χ k x * G x ∂potentialMeasure φ) =
      (∫ x, f x * hessianMetricDiffusion φ V (χ k) x ∂potentialMeasure φ) +
        a * (∫ x, χ k x * f x ∂potentialMeasure φ) := by
    have heq : (fun x => χ k x * G x) = fun x => χ k x * L x + a * (χ k x * f x) := by
      funext x
      dsimp [G]
      ring
    rw [heq, integral_add (hχLi k) ((hχfi k).const_mul a), integral_const_mul, hcomm k]
  have hGlim : Tendsto (fun k => ∫ x, ‖χ k x * G x‖ ∂potentialMeasure φ)
      atTop (𝓝 (a * ∫ x, f x ∂potentialMeasure φ)) := by
    have heq (k : ℕ) : (∫ x, ‖χ k x * G x‖ ∂potentialMeasure φ) =
        ∫ x, χ k x * G x ∂potentialMeasure φ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact Real.norm_of_nonneg (mul_nonneg ((hχ k).2.2 x).1 (hsub x))
    simp_rw [heq, hχGint]
    simpa only [zero_add] using herror.add (htestlim.const_mul a)
  have hGi : Integrable G (potentialMeasure φ) := by
    apply integrable_of_tendsto_integral_norm hGcont.aestronglyMeasurable hχGi _ hGlim
    filter_upwards [] with x
    simpa only [one_mul] using (hχlim x).mul_const (G x)
  have hLi : Integrable L (potentialMeasure φ) := by
    convert! hGi.sub (hfi.const_mul a) using 1
    funext x
    dsimp [G]
    ring
  refine ⟨hLi, ?_⟩
  have hLlim : Tendsto (fun k => ∫ x, χ k x * L x ∂potentialMeasure φ)
      atTop (𝓝 (∫ x, L x ∂potentialMeasure φ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖L x‖)
      (fun k => (hχLi k).aestronglyMeasurable) hLi.norm
    · intro k
      filter_upwards [] with x
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχnorm k x)
    · filter_upwards [] with x
      simpa only [one_mul] using (hχlim x).mul_const (L x)
  exact tendsto_nhds_unique hLlim (by simpa only [hcomm] using herror)

end KLS
end

#print axioms KLS.integrable_of_tendsto_integral_norm
#print axioms KLS.integrable_hessianMetricDiffusion_and_integral_eq_zero
