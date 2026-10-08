import KLS.HessianMetricCutoffSequence

/-!
# Sublevel cutoffs under integrable potential drift

The actual potential diffusion Lφ need only be L¹. The error constant uses
its L¹ norm, so no bounded gradient range or bounded target support is required.
-/

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma hessianMetricDiffusion_potentialHeight_eq (φ V : Space n → ℝ) (x₀ x : Space n) :
    hessianMetricDiffusion φ V (potentialHeight φ x₀) x = hessianMetricDiffusion φ V φ x := by
  simp only [hessianMetricDiffusion, coordinateHessian_potentialHeight,
    coordinateDerivative_potentialHeight]

theorem potentialSublevelTail_energy_le_of_integrable_drift {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hconv : ConvexOn ℝ univ φ) [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (x₀ : Space n) {c : ℝ} (hc : 0 < c)
    (hLW : Integrable (hessianMetricDiffusion φ V (potentialHeight φ x₀)) (potentialMeasure φ)) :
    (∫ x, c ^ 2 * ‖deriv (deriv sublevelCutoffProfile) (c * potentialHeight φ x₀ x)‖ *
      inverseHessianGradientForm φ (potentialHeight φ x₀) x ∂potentialMeasure φ) ≤
      c * (∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖) *
        ∫ x, ‖hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ ∂potentialMeasure φ := by
  rw [(potentialSublevelTail_energy_identity hφ hV hconv hpos hMA x₀ hc).2]
  have hp : Integrable (fun x => potentialSublevelTail φ x₀ c x *
      hessianMetricDiffusion φ V (potentialHeight φ x₀) x) (potentialMeasure φ) :=
    hLW.bdd_mul (potentialSublevelTail_contDiff hφ x₀ c).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => scaledSublevelTail_norm_le hc.le _)
  calc
    _ ≤ ‖∫ x, potentialSublevelTail φ x₀ c x *
      hessianMetricDiffusion φ V (potentialHeight φ x₀) x ∂potentialMeasure φ‖ := le_abs_self _
    _ ≤ ∫ x, ‖potentialSublevelTail φ x₀ c x *
      hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ ∂potentialMeasure φ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, (c * ∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖) *
      ‖hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ ∂potentialMeasure φ := by
      apply integral_mono hp.norm (hLW.norm.const_mul _)
      intro x
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (scaledSublevelTail_norm_le hc.le _) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem potentialSublevelCutoff_L1_bound_of_integrable_drift {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hconv : ConvexOn ℝ univ φ) [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (x₀ : Space n) {c C : ℝ} (hc : 0 < c)
    (hLW : Integrable (hessianMetricDiffusion φ V (potentialHeight φ x₀)) (potentialMeasure φ))
    (hderiv : ∀ t, ‖deriv sublevelCutoffProfile t‖ ≤ C) :
    Integrable (hessianMetricDiffusion φ V (potentialSublevelCutoff φ x₀ c)) (potentialMeasure φ) ∧
      (∫ x, ‖hessianMetricDiffusion φ V (potentialSublevelCutoff φ x₀ c) x‖ ∂potentialMeasure φ) ≤
        c * (∫ x, ‖hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ ∂potentialMeasure φ) *
          (C + ∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖) := by
  let E (x : Space n) := c ^ 2 * ‖deriv (deriv sublevelCutoffProfile) (c * potentialHeight φ x₀ x)‖ *
    inverseHessianGradientForm φ (potentialHeight φ x₀) x
  have hE : Integrable E (potentialMeasure φ) :=
    (potentialSublevelTail_energy_identity hφ hV hconv hpos hMA x₀ hc).1
  have hpoint (x : Space n) :
      ‖hessianMetricDiffusion φ V (potentialSublevelCutoff φ x₀ c) x‖ ≤
        c * C * ‖hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ + E x := by
    rw [hessianMetricDiffusion_potentialSublevelCutoff hφ]
    have hfirst : ‖c * deriv sublevelCutoffProfile (c * potentialHeight φ x₀ x) *
        hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ ≤
        c * C * ‖hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ := by
      rw [norm_mul, norm_mul, Real.norm_of_nonneg hc.le]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hderiv _) hc.le) (norm_nonneg _)
    have hsecond : ‖c ^ 2 * deriv (deriv sublevelCutoffProfile) (c * potentialHeight φ x₀ x) *
        inverseHessianGradientForm φ (potentialHeight φ x₀) x‖ = E x := by
      simp only [norm_mul, norm_pow, Real.norm_of_nonneg hc.le,
        Real.norm_of_nonneg (inverseHessianGradientForm_nonneg hpos _ _)]
      rfl
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond.le)
  have hmajor : Integrable (fun x => c * C *
      ‖hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ + E x) (potentialMeasure φ) :=
    (hLW.norm.const_mul (c * C)).add hE
  have hL : Integrable (hessianMetricDiffusion φ V (potentialSublevelCutoff φ x₀ c)) (potentialMeasure φ) :=
    hmajor.mono' (continuous_hessianMetricDiffusion hφ hV
      (potentialSublevelCutoff_contDiff hφ x₀ c) hpos).aestronglyMeasurable (Eventually.of_forall hpoint)
  refine ⟨hL, ?_⟩
  have hi := integral_mono hL.norm hmajor hpoint
  rw [integral_add (hLW.norm.const_mul _) hE, integral_const_mul] at hi
  have he := potentialSublevelTail_energy_le_of_integrable_drift hφ hV hconv hpos hMA x₀ hc hLW
  dsimp only [E] at hi
  nlinarith

/-- The actual sublevel sequence with vanishing L¹ error, under Lφ∈L¹. -/
theorem exists_hessianMetricCutoffSequence_of_integrable_drift {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hconv : ConvexOn ℝ univ φ) [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hLφ : Integrable (hessianMetricDiffusion φ V φ) (potentialMeasure φ)) :
    ∃ x₀ : Space n, (∀ x, φ x₀ ≤ φ x) ∧
      (∀ k, ContDiff ℝ 2 (hessianMetricCutoffSequence φ x₀ k) ∧
        HasCompactSupport (hessianMetricCutoffSequence φ x₀ k) ∧
        ∀ x, hessianMetricCutoffSequence φ x₀ k x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, Monotone (fun k => hessianMetricCutoffSequence φ x₀ k x)) ∧
      (∀ x, Tendsto (fun k => hessianMetricCutoffSequence φ x₀ k x) atTop (𝓝 1)) ∧
      (∀ k, Integrable (hessianMetricDiffusion φ V (hessianMetricCutoffSequence φ x₀ k))
        (potentialMeasure φ)) ∧
      Tendsto (fun k => ∫ x, ‖hessianMetricDiffusion φ V (hessianMetricCutoffSequence φ x₀ k) x‖
        ∂potentialMeasure φ) atTop (𝓝 0) := by
  obtain ⟨x₀, hmin⟩ := exists_minimizer_of_finite_potentialMeasure hφ.continuous hconv
  have hLW : Integrable (hessianMetricDiffusion φ V (potentialHeight φ x₀)) (potentialMeasure φ) := by
    simpa only [funext (hessianMetricDiffusion_potentialHeight_eq φ V x₀)] using hLφ
  obtain ⟨C, _, hderiv⟩ := sublevelCutoffProfile_deriv_bounded
  have hbound (k : ℕ) := potentialSublevelCutoff_L1_bound_of_integrable_drift
    hφ hV hconv hpos hMA x₀ (cutoffScale_pos k) hLW hderiv
  refine ⟨x₀, hmin, ?_, hessianMetricCutoffSequence_monotone hmin,
    hessianMetricCutoffSequence_tendsto_one φ x₀, fun k => (hbound k).1, ?_⟩
  · intro k
    exact ⟨potentialSublevelCutoff_contDiff hφ x₀ (cutoffScale k),
      potentialSublevelCutoff_hasCompactSupport hφ.continuous hconv x₀ (cutoffScale_pos k),
      fun x => potentialSublevelCutoff_mem_Icc φ x₀ x (cutoffScale k)⟩
  · apply squeeze_zero (fun k => integral_nonneg (fun x => norm_nonneg _))
      (fun k => (hbound k).2)
    simpa only [zero_mul] using (cutoffScale_tendsto_zero.mul_const
      (∫ x, ‖hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ ∂potentialMeasure φ)).mul_const
        (C + ∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖)

end KLS
end

#print axioms KLS.potentialSublevelTail_energy_le_of_integrable_drift
#print axioms KLS.potentialSublevelCutoff_L1_bound_of_integrable_drift
#print axioms KLS.exists_hessianMetricCutoffSequence_of_integrable_drift
