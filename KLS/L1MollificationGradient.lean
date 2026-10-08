import KLS.AbsolutelyContinuousCompactSmoothing
import KLS.L1CompactTestExtension

open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Compact local Lipschitz regularity gives an integrable actual gradient for
 every finite measure; its total derivative vanishes away from the support. -/
theorem integrable_gradient_of_compact_locallyLipschitz
    {μ : Measure (Space n)} [IsFiniteMeasure μ] {f : Space n → ℝ}
    (hf : LocallyLipschitz f) (hc : HasCompactSupport f) : Integrable (gradient f) μ := by
  obtain ⟨C, hC, hb⟩ := compact_locallyLipschitz_fderiv_bound hf hc
  apply (integrable_const C).mono' (measurable_gradient f).aestronglyMeasurable
  exact ae_of_all μ fun x => by simpa only [norm_gradient_eq_norm_fderiv] using hb x

lemma norm_space_le_sum_abs_coordinates (v : Space n) : ‖v‖ ≤ ∑ i, |v i| := by
  have hv : (∑ i : Fin n, EuclideanSpace.single i (v i)) = v := by
    ext j
    simp [Pi.single_apply]
  calc
    ‖v‖ = ‖∑ i : Fin n, EuclideanSpace.single i (v i)‖ := congrArg norm hv.symm
    _ ≤ ∑ i : Fin n, ‖EuclideanSpace.single i (v i)‖ := norm_sum_le _ _
    _ = ∑ i, |v i| := by simp

/-- L2 convergence on a probability measure implies the actual scalar L1 convergence. -/
theorem lintegral_abs_tendsto_zero_of_eLpNorm_two
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {F : ℕ → Space n → ℝ}
    (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (hlim : Tendsto (fun k => eLpNorm (F k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ x, ENNReal.ofReal |F k x| ∂μ) atTop (𝓝 0) := by
  have he (k : ℕ) : (∫⁻ x, ENNReal.ofReal |F k x| ∂μ) = eLpNorm (F k) 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm (hF k)]
    simp only [← ofReal_norm, Real.norm_eq_abs]
  simp_rw [he]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) (fun _ => eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

/-- Actual smooth compact mollifications converge in L1 gradient norm for every
 absolutely continuous probability measure. This uses proved weighted L2
 mollification of the actual coordinate derivatives. -/
theorem lintegral_gradient_mollify_sub_tendsto_zero
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hc : HasCompactSupport f) :
    Tendsto (fun k => ∫⁻ x, ENNReal.ofReal ‖gradient (mollify k f) x - gradient f x‖ ∂μ)
      atTop (𝓝 0) := by
  have hs := compact_locallyLipschitz_absolutelyContinuous_smoothing hμ hf hc
  have ht (i : Fin n) : Tendsto (fun k => ∫⁻ x, ENNReal.ofReal
      |coordinateDerivative (mollify k f) i x - coordinateDerivative f i x| ∂μ) atTop (𝓝 0) :=
    lintegral_abs_tendsto_zero_of_eLpNorm_two
      (fun k => ((measurable_coordinateDerivative _ _).sub (measurable_coordinateDerivative _ _)).aestronglyMeasurable)
      (hs.2.2 i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => ht i)
  simp only [Finset.sum_const_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
  intro k
  calc
    _ ≤ ∫⁻ x, ∑ i : Fin n, ENNReal.ofReal
        |coordinateDerivative (mollify k f) i x - coordinateDerivative f i x| ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [coordinateDerivative_eq_gradient, PiLp.sub_apply] using
        norm_space_le_sum_abs_coordinates (gradient (mollify k f) x - gradient f x)
    _ = _ := lintegral_finsetSum Finset.univ (fun i _ =>
      ((measurable_coordinateDerivative _ _).sub (measurable_coordinateDerivative _ _)).abs.ennreal_ofReal)

end KLS
end
