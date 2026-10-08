import KLS.AbsolutelyContinuousCompactSmoothing
import KLS.WeightedFaithfulGraph

/-! Actual Poincare inequalities pass to strong convergence of values and all derivatives. -/
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma integral_sq_eq_norm_toLp_sq {μ : Measure (Space n)} {f : Space n → ℝ}
    (hf : MemLp f 2 μ) : (∫ x, f x ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  rw [integral_sq_eq_toReal_eLpNorm_sq hf, Lp.norm_toLp]

lemma norm_center_toLp_sq_eq_variance {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ‖CenteredL2.center μ (hf.toLp f)‖ ^ 2 = ProbabilityTheory.variance f μ := by
  rw [CenteredL2.norm_center_sq_eq_variance, ProbabilityTheory.variance_congr hf.coeFn_toLp]

theorem real_poincare_bound_of_strong_graph_limit {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : ℕ → Space n → ℝ} {g : Space n → ℝ} {C : ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (hfd : ∀ k (i : Fin n), MemLp (coordinateDerivative (f k) i) 2 μ)
    (hgd : ∀ i : Fin n, MemLp (coordinateDerivative g i) 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - g) 2 μ) atTop (𝓝 0))
    (hdconv : ∀ i : Fin n, Tendsto (fun k => eLpNorm
      (coordinateDerivative (f k) i - coordinateDerivative g i) 2 μ) atTop (𝓝 0))
    (hbound : ∀ k, ProbabilityTheory.variance (f k) μ ≤
      C * ∑ i : Fin n, ∫ x, coordinateDerivative (f k) i x ^ 2 ∂μ) :
    ProbabilityTheory.variance g μ ≤ C * ∑ i : Fin n, ∫ x, coordinateDerivative g i x ^ 2 ∂μ := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr hconv
  have hvar : Tendsto (fun k => ProbabilityTheory.variance (f k) μ) atTop
      (𝓝 (ProbabilityTheory.variance g μ)) := by
    simpa only [Function.comp_def, norm_center_toLp_sq_eq_variance] using
      (((continuous_centeredL2_center μ).tendsto _).comp hLp).norm.pow 2
  have henergy : Tendsto (fun k => ∑ i : Fin n, ∫ x, coordinateDerivative (f k) i x ^ 2 ∂μ)
      atTop (𝓝 (∑ i : Fin n, ∫ x, coordinateDerivative g i x ^ 2 ∂μ)) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun k => coordinateDerivative (f k) i) (fun k => hfd k i)
      (coordinateDerivative g i) (hgd i)).mpr (hdconv i)
    simpa only [← integral_sq_eq_norm_toLp_sq] using ht.norm.pow 2
  exact le_of_tendsto_of_tendsto hvar (henergy.const_mul C) (Eventually.of_forall hbound)

end KLS
end
