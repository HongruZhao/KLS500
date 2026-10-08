import KLS.HessianMetricSublevelCutoff

/-!
# Vanishing L¹ diffusion error for the actual sublevel cutoffs

The compact auxiliary primitive controls the possibly unbounded inverse
Hessian energy. The resulting error is bounded by a constant times the
cutoff scale, with no global bound on the inverse Hessian.
-/

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

lemma continuous_hessianMetricDiffusion {φ V g : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V) (hg : ContDiff ℝ 2 g)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) :
    Continuous (hessianMetricDiffusion φ V g) := by
  unfold hessianMetricDiffusion
  apply Continuous.sub
  · apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (contDiff_inverseHessian_entry hφ hpos i j).continuous.mul
      (contDiff_coordinateHessian hg (m := 0) (by norm_num) i j).continuous
  · apply continuous_finsetSum
    intro i _
    exact ((contDiff_coordinateDerivative hV (m := 0) (by norm_num) i).continuous.comp
      (contDiff_gradient hφ (m := 0) (by norm_num)).continuous).mul
        (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous

/-- A bounded actual gradient range supplies the potential-height drift bound. -/
theorem exists_bound_diffusion_potentialHeight {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hgrad : Bornology.IsBounded (range (gradient φ))) (x₀ : Space n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ ≤ D := by
  let F : Space n → ℝ := fun z => (n : ℝ) - ∑ i, coordinateDerivative V i z * z i
  have hF : Continuous F := by
    apply continuous_const.sub
    apply continuous_finsetSum
    intro i _
    exact (contDiff_coordinateDerivative hV (m := 0) (by norm_num) i).continuous.mul
      (EuclideanSpace.proj i).continuous
  obtain ⟨D, hD⟩ := hgrad.isCompact_closure.bddAbove_image hF.norm.continuousOn
  have hbound (x : Space n) : ‖hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ ≤ D := by
    rw [hessianMetricDiffusion_potentialHeight (hφ.of_le (by norm_num)) hpos]
    simp_rw [coordinateDerivative_eq_gradient φ]
    exact hD ⟨gradient φ x, subset_closure ⟨x, rfl⟩, rfl⟩
  exact ⟨D, (norm_nonneg _).trans (hbound 0), hbound⟩

/-- The actual auxiliary identity gives the inverse-Hessian energy estimate. -/
theorem potentialSublevelTail_energy_le {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hconv : ConvexOn ℝ univ φ) [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (x₀ : Space n) {c D : ℝ} (hc : 0 < c) (_hD : 0 ≤ D)
    (hbound : ∀ x, ‖hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ ≤ D) :
    (∫ x, c ^ 2 * ‖deriv (deriv sublevelCutoffProfile) (c * potentialHeight φ x₀ x)‖ *
      inverseHessianGradientForm φ (potentialHeight φ x₀) x ∂potentialMeasure φ) ≤
      c * (∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖) * D := by
  rw [(potentialSublevelTail_energy_identity hφ hV hconv hpos hMA x₀ hc).2]
  have hM : 0 ≤ ∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hnorm (x : Space n) :
      ‖potentialSublevelTail φ x₀ c x * hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ ≤
      c * (∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖) * D := by
    rw [norm_mul]
    exact mul_le_mul (scaledSublevelTail_norm_le hc.le _) (hbound x) (norm_nonneg _)
      (mul_nonneg hc.le hM)
  have hi := norm_integral_le_of_norm_le_const (μ := potentialMeasure φ) (Eventually.of_forall hnorm)
  have hi' : ‖∫ x, potentialSublevelTail φ x₀ c x *
      hessianMetricDiffusion φ V (potentialHeight φ x₀) x ∂potentialMeasure φ‖ ≤
      c * (∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖) * D := by simpa using hi
  exact (le_abs_self _).trans hi'

/-- An explicit O(scale) L¹ bound, with only the genuine drift bound as input. -/
theorem potentialSublevelCutoff_L1_bound {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hconv : ConvexOn ℝ univ φ) [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (x₀ : Space n) {c D C : ℝ} (hc : 0 < c) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ ≤ D)
    (hderiv : ∀ t, ‖deriv sublevelCutoffProfile t‖ ≤ C) :
    Integrable (hessianMetricDiffusion φ V (potentialSublevelCutoff φ x₀ c)) (potentialMeasure φ) ∧
      (∫ x, ‖hessianMetricDiffusion φ V (potentialSublevelCutoff φ x₀ c) x‖ ∂potentialMeasure φ) ≤
        c * D * (C + ∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖) := by
  let E (x : Space n) := c ^ 2 * ‖deriv (deriv sublevelCutoffProfile) (c * potentialHeight φ x₀ x)‖ *
    inverseHessianGradientForm φ (potentialHeight φ x₀) x
  have hE : Integrable E (potentialMeasure φ) :=
    (potentialSublevelTail_energy_identity hφ hV hconv hpos hMA x₀ hc).1
  have hpoint (x : Space n) :
      ‖hessianMetricDiffusion φ V (potentialSublevelCutoff φ x₀ c) x‖ ≤ c * C * D + E x := by
    rw [hessianMetricDiffusion_potentialSublevelCutoff hφ]
    have hfirst : ‖c * deriv sublevelCutoffProfile (c * potentialHeight φ x₀ x) *
        hessianMetricDiffusion φ V (potentialHeight φ x₀) x‖ ≤ c * C * D := by
      rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hderiv _) hc.le) (hbound x) (norm_nonneg _)
        (mul_nonneg hc.le hC)
    have hsecond : ‖c ^ 2 * deriv (deriv sublevelCutoffProfile) (c * potentialHeight φ x₀ x) *
        inverseHessianGradientForm φ (potentialHeight φ x₀) x‖ = E x := by
      simp only [norm_mul, norm_pow, Real.norm_of_nonneg hc.le,
        Real.norm_of_nonneg (inverseHessianGradientForm_nonneg hpos _ _)]
      rfl
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond.le)
  have hmajor : Integrable (fun x => c * C * D + E x) (potentialMeasure φ) :=
    (integrable_const (c * C * D)).add hE
  have hL : Integrable (hessianMetricDiffusion φ V (potentialSublevelCutoff φ x₀ c)) (potentialMeasure φ) :=
    hmajor.mono' (continuous_hessianMetricDiffusion hφ hV
      (potentialSublevelCutoff_contDiff hφ x₀ c) hpos).aestronglyMeasurable (Eventually.of_forall hpoint)
  refine ⟨hL, ?_⟩
  have hi : (∫ x, ‖hessianMetricDiffusion φ V (potentialSublevelCutoff φ x₀ c) x‖ ∂potentialMeasure φ) ≤
      c * C * D + ∫ x, E x ∂potentialMeasure φ := by
    have h := integral_mono hL.norm hmajor hpoint
    rw [integral_add (integrable_const _) hE] at h
    simpa using h
  calc
    _ ≤ c * C * D + ∫ x, E x ∂potentialMeasure φ := hi
    _ ≤ c * C * D + c * (∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖) * D :=
      add_le_add_right (potentialSublevelTail_energy_le hφ hV hconv hpos hMA x₀ hc hD hbound) _
    _ = _ := by ring

/-- The scale-independent constant is constructed from the actual bounded
gradient range and the fixed smooth cutoff profile. -/
theorem exists_potentialSublevelCutoff_L1_bound {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hconv : ConvexOn ℝ univ φ) [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hgrad : Bornology.IsBounded (range (gradient φ))) :
    ∃ x₀ : Space n, (∀ x, φ x₀ ≤ φ x) ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ c > 0,
      Integrable (hessianMetricDiffusion φ V (potentialSublevelCutoff φ x₀ c)) (potentialMeasure φ) ∧
      (∫ x, ‖hessianMetricDiffusion φ V (potentialSublevelCutoff φ x₀ c) x‖ ∂potentialMeasure φ) ≤ c * K := by
  obtain ⟨x₀, hx₀⟩ := exists_minimizer_of_finite_potentialMeasure hφ.continuous hconv
  obtain ⟨D, hD, hbound⟩ := exists_bound_diffusion_potentialHeight hφ hV hpos hgrad x₀
  obtain ⟨C, hC, hderiv⟩ := sublevelCutoffProfile_deriv_bounded
  let K := D * (C + ∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖)
  refine ⟨x₀, hx₀, K, mul_nonneg hD (add_nonneg hC (integral_nonneg (fun _ => norm_nonneg _))), ?_⟩
  intro c hc
  have h := potentialSublevelCutoff_L1_bound hφ hV hconv hpos hMA x₀ hc hD hC hbound hderiv
  simpa only [K, mul_assoc] using h

end KLS
end

#print axioms KLS.exists_bound_diffusion_potentialHeight
#print axioms KLS.potentialSublevelTail_energy_le
#print axioms KLS.potentialSublevelCutoff_L1_bound
#print axioms KLS.exists_potentialSublevelCutoff_L1_bound
