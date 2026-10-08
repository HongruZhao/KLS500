import KLS.BoundedVarianceCheegerShell
import KLS.BoundaryComparison

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace KLS
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

/-- A positive bounded-variance coefficient yields the faithful open outer
Minkowski inequality for every measurable set under any probability law. -/
theorem boundedVariance_min_div_le_openBoundaryMeasure
    {K : ℝ} (hK0 : 0 < K)
    (hbound : ∀ f : Space n → ℝ, LocallyLipschitz f → Integrable (gradient f) μ →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) →
        ProbabilityTheory.variance f μ ≤ K*B*(∫ x, ‖gradient f x‖ ∂μ))
    {A : Set (Space n)} (hA : MeasurableSet A) :
    min (μ A) (1-μ A) /
        ENNReal.ofReal (2*K) ≤ openBoundaryMeasure (μ) A := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  have hlim : Tendsto (fun ε : ℝ => min (μ A) (1-μ A) /
      ENNReal.ofReal (2*K+4*ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (min (μ A) (1-μ A) /
        ENNReal.ofReal (2*K))) := by
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hadd : Tendsto (fun ε : ℝ => 2*K+4*ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (2*K)) := by
      simpa using tendsto_const_nhds.add (hid.const_mul 4)
    exact ENNReal.Tendsto.const_div
      ((ENNReal.continuous_ofReal.tendsto _).comp hadd) (Or.inl ENNReal.ofReal_ne_top)
  calc
    _ = Filter.liminf (fun ε : ℝ => min (μ A) (1-μ A) /
        ENNReal.ofReal (2*K+4*ε)) (𝓝[>] (0 : ℝ)) := hlim.liminf_eq.symm
    _ ≤ _ := Filter.liminf_le_liminf (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact boundedVariance_min_div_le_enlargement_quotient hK0 hbound hA hne hε)

/-- A positive bounded-variance coefficient gives the true open Cheeger lower
bound. No median or coarea estimate is assumed. -/
theorem boundedVariance_inv_le_openCheegerConstant
    {K : ℝ} (hK0 : 0 < K)
    (hbound : ∀ f : Space n → ℝ, LocallyLipschitz f → Integrable (gradient f) μ →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) →
        ProbabilityTheory.variance f μ ≤ K*B*(∫ x, ‖gradient f x‖ ∂μ)) :
    ENNReal.ofReal ((2*K)⁻¹) ≤ openCheegerConstant (μ) := by
  apply le_iInf
  intro A
  have hK : 0 < 2*K := mul_pos (by norm_num) hK0
  have hmin0 : min (μ A.1) (1-μ A.1) ≠ 0 :=
    ne_of_gt (lt_min A.2.2.1 (tsub_pos_iff_lt.mpr A.2.2.2))
  have hmintop : min (μ A.1) (1-μ A.1) ≠ ⊤ :=
    ne_of_lt ((min_le_left _ _).trans_lt (measure_lt_top (μ) A.1))
  rw [ENNReal.ofReal_inv_of_pos hK]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hmin0) (Or.inl hmintop)).mpr
  simpa only [div_eq_mul_inv,mul_comm] using
    boundedVariance_min_div_le_openBoundaryMeasure hK0 hbound A.2.1

/-- An actual bounded-variance bound gives the exact original closed-neighborhood
Cheeger lower bound for any probability law. -/
theorem boundedVariance_inv_le_cheegerConstant
    {K : ℝ} (hK0 : 0 < K)
    (hbound : ∀ f : Space n → ℝ, LocallyLipschitz f → Integrable (gradient f) μ →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) →
        ProbabilityTheory.variance f μ ≤ K*B*(∫ x, ‖gradient f x‖ ∂μ)) :
    ENNReal.ofReal ((2*K)⁻¹) ≤ cheegerConstant (μ) :=
  le_cheegerConstant_of_le_openCheegerConstant (μ)
    (boundedVariance_inv_le_openCheegerConstant hK0 hbound)

end KLS
end
