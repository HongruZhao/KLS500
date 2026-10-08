import KLS.WeakWeightedIntegration
import KLS.WeightedFaithfulCutoff

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem integral_raw_derivative_compact_weight
    {φ f F χ : Space n → ℝ} {i : Fin n}
    (hφ : ContDiff ℝ 1 φ) (hFw : HasLocalWeakCoordinateDerivative f F i)
    (hf : Integrable f (potentialMeasure φ)) (_hF : Integrable F (potentialMeasure φ))
    (hfd : Integrable (fun x => f x * coordinateDerivative φ i x) (potentialMeasure φ))
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    (∫ x, F x * χ x ∂potentialMeasure φ) =
      (∫ x, (f x * coordinateDerivative φ i x) * χ x ∂potentialMeasure φ) -
        ∫ x, f x * coordinateDerivative χ i x ∂potentialMeasure φ := by
  have hχb := hχ.continuous.memLp_top_of_hasCompactSupport hc (potentialMeasure φ)
  have hdχ := (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
  have hdχb := hdχ.memLp_top_of_hasCompactSupport
    (hasCompactSupport_coordinateDerivative hc i) (potentialMeasure φ)
  have ha : Integrable (fun x => (f x * coordinateDerivative φ i x) * χ x)
      (potentialMeasure φ) := hfd.mul_of_top_left hχb
  have hb : Integrable (fun x => f x * coordinateDerivative χ i x)
      (potentialMeasure φ) := hf.mul_of_top_left hdχb
  have hw := hFw (fun x => Real.exp (-φ x) * χ x) (hφ.neg.exp.mul hχ) hc.mul_left
  have hleft : (∫ x, f x * coordinateDerivative (fun y => Real.exp (-φ y) * χ y) i x) =
      (∫ x, f x * coordinateDerivative χ i x ∂potentialMeasure φ) -
        ∫ x, (f x * coordinateDerivative φ i x) * χ x ∂potentialMeasure φ := by
    rw [← integral_sub hb ha, integral_potentialMeasure hφ.continuous.measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      have hρ : DifferentiableAt ℝ (fun y => Real.exp (-φ y)) x :=
        ((hφ.differentiable (by norm_num) x).neg).exp
      rw [coordinateDerivative_mul hρ (hχ.differentiable (by norm_num) x)]
      change f x * (fderiv ℝ (fun y => Real.exp (-φ y)) x (EuclideanSpace.single i 1) * χ x +
        Real.exp (-φ x) * coordinateDerivative χ i x) = _
      rw [fderiv_exp_neg_apply (hφ.differentiable (by norm_num) x)]
      dsimp only [coordinateDerivative]
      ring
  have hright : (∫ x, F x * (Real.exp (-φ x) * χ x)) =
      ∫ x, F x * χ x ∂potentialMeasure φ := by
    rw [integral_potentialMeasure hφ.continuous.measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hleft, hright] at hw
  linarith

theorem integral_mul_smoothCutoff_tendsto_raw
    {μ : Measure (Space n)} {f : Space n → ℝ} (hf : Integrable f μ) :
    Tendsto (fun k => ∫ x, f x * smoothCutoff n k x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hm (k : ℕ) : AEStronglyMeasurable (fun x => f x * smoothCutoff n k x) μ :=
    hf.aestronglyMeasurable.mul (smoothCutoff_contDiff k).continuous.aestronglyMeasurable
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    hm hf.norm
  · intro k
    exact Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_of_nonneg (faithfulCutoff_bounds k x).1]
      exact mul_le_of_le_one_right (norm_nonneg _) (faithfulCutoff_bounds k x).2
  · exact Eventually.of_forall fun x => by
      simpa only [mul_one] using (smoothCutoff_tendsto_one x).const_mul (f x)

theorem integral_mul_smoothCutoff_derivative_tendsto_raw
    {μ : Measure (Space n)} {f : Space n → ℝ} (hf : Integrable f μ) (i : Fin n) :
    Tendsto (fun k => ∫ x, f x * coordinateDerivative (smoothCutoff n k) i x ∂μ) atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := smoothCutoff_gradient_bound (n := n)
  have hD (k : ℕ) (x : Space n) : ‖coordinateDerivative (smoothCutoff n k) i x‖ ≤ K := by
    have hs : cutoffScale k ≤ 1 := by
      unfold cutoffScale
      apply inv_le_one_of_one_le₀
      linarith [Nat.cast_nonneg (α := ℝ) k]
    exact ((norm_coordinateDerivative_le _ i x).trans (hbound k x)).trans
      (mul_le_of_le_one_left hK hs)
  have hm (k : ℕ) : AEStronglyMeasurable (fun x => f x * coordinateDerivative (smoothCutoff n k) i x) μ :=
    hf.aestronglyMeasurable.mul (measurable_coordinateDerivative (smoothCutoff n k) i).aestronglyMeasurable
  have ht := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ * K) hm
    (hf.norm.mul_const K)
    (fun k => Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hD k x) (norm_nonneg _))
    (Eventually.of_forall fun x => by
      simpa only [mul_zero] using (smoothCutoff_coordinateDerivative_tendsto_zero i x).const_mul (f x))
  simpa only [integral_zero] using ht

/-- Expanding compact tests give the global weighted mean identity from
the original raw weak derivative and actual integrability data. -/
theorem integral_raw_derivative_potential
    {φ f F : Space n → ℝ} {i : Fin n}
    (hφ : ContDiff ℝ 1 φ) (hFw : HasLocalWeakCoordinateDerivative f F i)
    (hf : Integrable f (potentialMeasure φ)) (hF : Integrable F (potentialMeasure φ))
    (hfd : Integrable (fun x => f x * coordinateDerivative φ i x) (potentialMeasure φ)) :
    (∫ x, F x ∂potentialMeasure φ) = ∫ x, f x * coordinateDerivative φ i x ∂potentialMeasure φ := by
  have hl := integral_mul_smoothCutoff_tendsto_raw hF
  have hr := (integral_mul_smoothCutoff_tendsto_raw hfd).sub
    (integral_mul_smoothCutoff_derivative_tendsto_raw hf i)
  have he : (fun k => ∫ x, F x * smoothCutoff n k x ∂potentialMeasure φ) =
      fun k => (∫ x, (f x * coordinateDerivative φ i x) * smoothCutoff n k x ∂potentialMeasure φ) -
        ∫ x, f x * coordinateDerivative (smoothCutoff n k) i x ∂potentialMeasure φ := by
    funext k
    exact integral_raw_derivative_compact_weight hφ hFw hf hF hfd
      (smoothCutoff_contDiff k) (smoothCutoff_hasCompactSupport k)
  rw [he] at hl
  simpa only [sub_zero] using tendsto_nhds_unique hl hr

end KLS
end
