import KLS.SmoothCutoffSequence

/-!
# Classical weighted L² Liouville theorem on all of Euclidean space

Actual scaled compact cutoffs and the proved Caccioppoli estimate force zero
Dirichlet energy by Fatou. Strict positivity of the finite real potential's
density then makes the continuous gradient identically zero.

This is a theorem about classical C² solutions on all of Euclidean space.
It does not prove regularity of weak L² solutions, a bounded-domain Neumann
statement, or an approximation theorem for potentials infinite off a convex set.
-/

open MeasureTheory InnerProductSpace Filter Set
open scoped Topology ContDiff ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

lemma weighted_caccioppoli_le_L2 {φ χ h : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hχ : ContDiff ℝ 1 χ) (hh : ContDiff ℝ 2 h)
    (hc : HasCompactSupport χ) (hharm : ∀ x, weightedDiffusion φ h x = 0)
    (hL2 : MemLp h 2 (potentialMeasure φ)) {a : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ x, ‖gradient χ x‖ ≤ a) :
    (∫ x, χ x ^ 2 * ‖gradient h x‖ ^ 2 ∂potentialMeasure φ) ≤
      4 * (a ^ 2 * ∫ x, h x ^ 2 ∂potentialMeasure φ) := by
  have hgχ := continuous_gradient_of_contDiff hχ
  have hB : Integrable (fun x => h x ^ 2 * ‖gradient χ x‖ ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hh.continuous.pow 2).mul (hgχ.norm.pow 2))
      (by simpa [pow_two, Pi.mul_def] using (hasCompactSupport_gradient hc).norm.mul_right.mul_left)
  have hm := integral_mono hB (hL2.integrable_sq.const_mul (a ^ 2)) (fun x =>
    calc
      h x ^ 2 * ‖gradient χ x‖ ^ 2 ≤ h x ^ 2 * a ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2) (sq_nonneg _)
      _ = a ^ 2 * h x ^ 2 := by ring)
  rw [integral_const_mul] at hm
  exact (weighted_caccioppoli hφ hχ hh hc hharm).trans (mul_le_mul_of_nonneg_left hm (by norm_num))

/-- No global derivative integrability is assumed: Fatou produces zero extended energy. -/
theorem lintegral_gradient_sq_eq_zero_of_weighted_harmonic {φ h : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hh : ContDiff ℝ 2 h)
    (hL2 : MemLp h 2 (potentialMeasure φ)) (hharm : ∀ x, weightedDiffusion φ h x = 0) :
    (∫⁻ x, ENNReal.ofReal (‖gradient h x‖ ^ 2) ∂potentialMeasure φ) = 0 := by
  obtain ⟨K, hK, hbound⟩ := smoothCutoff_gradient_bound (n := n)
  have hgh := continuous_gradient_of_contDiff (hh.of_le (by norm_num))
  let F : ℕ → Space n → ℝ≥0∞ := fun k x =>
    ENNReal.ofReal (smoothCutoff n k x ^ 2 * ‖gradient h x‖ ^ 2)
  have hFm (k : ℕ) : Measurable (F k) :=
    (((smoothCutoff_contDiff k).continuous.pow 2).mul (hgh.norm.pow 2)).measurable.ennreal_ofReal
  have hFt (x : Space n) : Tendsto (fun k => F k x) atTop
      (𝓝 (ENNReal.ofReal (‖gradient h x‖ ^ 2))) := by
    simpa only [one_pow, one_mul, F] using ENNReal.tendsto_ofReal
      (((smoothCutoff_tendsto_one x).pow 2).mul_const (‖gradient h x‖ ^ 2))
  have hupper (k : ℕ) : (∫⁻ x, F k x ∂potentialMeasure φ) ≤
      ENNReal.ofReal (4 * ((cutoffScale k * K) ^ 2 * ∫ x, h x ^ 2 ∂potentialMeasure φ)) := by
    have hE : Integrable (fun x => smoothCutoff n k x ^ 2 * ‖gradient h x‖ ^ 2)
        (potentialMeasure φ) :=
      integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
        (((smoothCutoff_contDiff k).continuous.pow 2).mul (hgh.norm.pow 2))
        (by simpa [pow_two, Pi.mul_def] using (smoothCutoff_hasCompactSupport k).mul_right.mul_right)
    rw [show (∫⁻ x, F k x ∂potentialMeasure φ) = ENNReal.ofReal
      (∫ x, smoothCutoff n k x ^ 2 * ‖gradient h x‖ ^ 2 ∂potentialMeasure φ) from
      (ofReal_integral_eq_lintegral_ofReal hE
        (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))).symm]
    exact ENNReal.ofReal_le_ofReal (weighted_caccioppoli_le_L2 hφ (smoothCutoff_contDiff k) hh
      (smoothCutoff_hasCompactSupport k) hharm hL2
      (mul_nonneg (cutoffScale_pos k).le hK) (hbound k))
  have hupperT : Tendsto (fun k => ENNReal.ofReal
      (4 * ((cutoffScale k * K) ^ 2 * ∫ x, h x ^ 2 ∂potentialMeasure φ))) atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal ((((cutoffScale_tendsto_zero.mul_const K).pow 2).mul_const
        (∫ x, h x ^ 2 ∂potentialMeasure φ)).const_mul 4)
  have hIntT : Tendsto (fun k => ∫⁻ x, F k x ∂potentialMeasure φ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupperT (fun _ => bot_le) hupper
  have hfatou := lintegral_liminf_le (μ := potentialMeasure φ) (u := atTop) hFm
  have heq : (fun x => liminf (fun k => F k x) atTop) =
      fun x => ENNReal.ofReal (‖gradient h x‖ ^ 2) := funext fun x => (hFt x).liminf_eq
  rw [heq, hIntT.liminf_eq] at hfatou
  exact le_antisymm hfatou bot_le

/-- The actual density of a finite continuous real potential has the same null sets as volume. -/
lemma volume_absolutelyContinuous_potentialMeasure {φ : Space n → ℝ} (hφ : Continuous φ) :
    (volume : Measure (Space n)) ≪ potentialMeasure φ := by
  apply withDensity_absolutelyContinuous' (hφ.measurable.neg.exp.ennreal_ofReal.aemeasurable)
  exact Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

/-- Classical weighted L² harmonic functions have identically zero gradient. -/
theorem gradient_eq_zero_of_weighted_harmonic {φ h : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hh : ContDiff ℝ 2 h)
    (hL2 : MemLp h 2 (potentialMeasure φ)) (hharm : ∀ x, weightedDiffusion φ h x = 0) :
    gradient h = 0 := by
  have hgh := continuous_gradient_of_contDiff (hh.of_le (by norm_num))
  have hae := (lintegral_eq_zero_iff (hgh.norm.pow 2).measurable.ennreal_ofReal).mp
    (lintegral_gradient_sq_eq_zero_of_weighted_harmonic hφ hh hL2 hharm)
  have hgzero : gradient h =ᵐ[potentialMeasure φ] 0 := by
    filter_upwards [hae] with x hx
    have hs : ‖gradient h x‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
    have hn : ‖gradient h x‖ = 0 := by nlinarith [norm_nonneg (gradient h x)]
    exact norm_eq_zero.mp hn
  exact MeasureTheory.Measure.eq_of_ae_eq
    ((volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq hgzero) hgh continuous_const

/-- Full-space classical Liouville, proved from actual L² membership and the actual equation.
No probability normalization, convexity, or spectral inequality is needed. -/
theorem classical_weighted_liouville {φ h : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hh : ContDiff ℝ 2 h)
    (hL2 : MemLp h 2 (potentialMeasure φ)) (hharm : ∀ x, weightedDiffusion φ h x = 0) :
    ∃ c : ℝ, ∀ x, h x = c := by
  have hg := gradient_eq_zero_of_weighted_harmonic hφ hh hL2 hharm
  have hd (x : Space n) : fderiv ℝ h x = 0 := by
    apply (toDual ℝ (Space n)).symm.injective
    change gradient h x = (toDual ℝ (Space n)).symm 0
    rw [map_zero]
    exact congrFun hg x
  exact ⟨h 0, fun x => is_const_of_fderiv_eq_zero (hh.differentiable (by norm_num)) hd x 0⟩

end KLS
end

#print axioms KLS.lintegral_gradient_sq_eq_zero_of_weighted_harmonic
#print axioms KLS.volume_absolutelyContinuous_potentialMeasure
#print axioms KLS.gradient_eq_zero_of_weighted_harmonic
#print axioms KLS.classical_weighted_liouville
