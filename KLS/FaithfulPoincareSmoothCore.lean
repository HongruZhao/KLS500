import KLS.PoincareGraphLimit

/-! Compact smooth tests determine positive faithful Poincare bounds for absolutely continuous laws. -/
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

theorem real_poincare_compact_locallyLipschitz_of_smooth_tests
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume) {C : ℝ}
    (hP : ∀ f : Space n → ℝ, ContDiff ℝ 3 f → HasCompactSupport f →
      ProbabilityTheory.variance f μ ≤ C * ∑ i : Fin n, ∫ x, coordinateDerivative f i x ^ 2 ∂μ)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hc : HasCompactSupport f) :
    ProbabilityTheory.variance f μ ≤ C * ∑ i : Fin n, ∫ x, coordinateDerivative f i x ^ 2 ∂μ := by
  obtain ⟨hm, hv, hd⟩ := compact_locallyLipschitz_absolutelyContinuous_smoothing hμ hf hc
  have hf2 : MemLp f 2 μ := hf.continuous.memLp_of_hasCompactSupport hc
  obtain ⟨B, hB, hb⟩ := compact_locallyLipschitz_coordinateDerivative_bound hf hc
  have hd2 (i : Fin n) : MemLp (coordinateDerivative f i) 2 μ :=
    (memLp_const B).mono' (measurable_coordinateDerivative f i).aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg hB] using hb i x)
  exact real_poincare_bound_of_strong_graph_limit (fun k => (hm k).2.2.1) hf2
    (fun k => (hm k).2.2.2) hd2 hv hd (fun k => hP _ (hm k).1 (hm k).2.1)

theorem energy_eq_ofReal_sum_coordinate_integrals {μ : Measure (Space n)} {f : Space n → ℝ}
    (he : energy μ f < ⊤) :
    energy μ f = ENNReal.ofReal (∑ i : Fin n, ∫ x, coordinateDerivative f i x ^ 2 ∂μ) := by
  calc
    energy μ f = ENNReal.ofReal (energy μ f).toReal := (ENNReal.ofReal_toReal he.ne).symm
    _ = _ := by
      rw [energy_toReal_eq_integral_of_lt_top he]
      congr 1
      have hgrad : (fun x => ‖gradient f x‖ ^ 2) =
          fun x => ∑ i : Fin n, coordinateDerivative f i x ^ 2 := by
        funext x
        simp_rw [EuclideanSpace.real_norm_sq_eq, coordinateDerivative_eq_gradient]
      rw [hgrad, integral_finsetSum Finset.univ
        (fun i _ => (memLp_coordinateDerivative_of_energy_lt_top he i).integrable_sq)]

/-- The original locally Lipschitz L2 test class, including infinite-energy tests,
is controlled by a positive constant as soon as all actual compact C3 tests are controlled. -/
theorem mem_poincareConstants_of_compact_smooth_tests
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {C : ℝ≥0} (hC : 0 < C)
    (hP : ∀ f : Space n → ℝ, ContDiff ℝ 3 f → HasCompactSupport f →
      ProbabilityTheory.variance f μ ≤ (C : ℝ) *
        ∑ i : Fin n, ∫ x, coordinateDerivative f i x ^ 2 ∂μ) :
    C ∈ poincareConstants μ := by
  intro f hf
  by_cases he : energy μ f < ⊤
  · obtain ⟨hc, hv, hd⟩ := faithful_test_compact_cutoff_approximation hμ hf he
    have hreal := real_poincare_bound_of_strong_graph_limit
      (fun k => (hc k).2.2.1) hf.2 (fun k => (hc k).2.2.2)
      (memLp_coordinateDerivative_of_energy_lt_top he) hv hd
      (fun k => real_poincare_compact_locallyLipschitz_of_smooth_tests hμ hP (hc k).2.1 (hc k).1)
    have hvar : variance μ f = ENNReal.ofReal (ProbabilityTheory.variance f μ) :=
      (ENNReal.ofReal_toReal hf.2.evariance_lt_top.ne).symm
    rw [hvar, energy_eq_ofReal_sum_coordinate_integrals he,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal hreal
  · have htop : energy μ f = ⊤ := top_le_iff.mp (not_lt.mp he)
    rw [htop, ENNReal.mul_top (by exact_mod_cast hC.ne')]
    exact le_top

end KLS
end
