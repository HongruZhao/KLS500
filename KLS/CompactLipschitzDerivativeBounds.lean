import KLS.WeightedFaithfulSmoothing

/-! Uniform bounds for the actual derivatives of compact locally Lipschitz tests. -/
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal
noncomputable section
namespace KLS
variable {n : ℕ}

theorem compact_locallyLipschitz_fderiv_bound {f : Space n → ℝ}
    (hf : LocallyLipschitz f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ C := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_ball (0 : Space n)
  obtain ⟨L, hL⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Space n) R)
  refine ⟨L, L.coe_nonneg, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact norm_fderiv_le_of_lipschitzOn ℝ
      (mem_of_superset (isOpen_ball.mem_nhds (hR hx)) ball_subset_closedBall) hL
  · rw [fderiv_of_notMem_tsupport ℝ hx, norm_zero]
    exact L.coe_nonneg

theorem compact_locallyLipschitz_coordinateDerivative_bound {f : Space n → ℝ}
    (hf : LocallyLipschitz f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : Fin n, ∀ x, ‖coordinateDerivative f i x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_locallyLipschitz_fderiv_bound hf hc
  refine ⟨C, hC, fun i x => ?_⟩
  calc
    ‖coordinateDerivative f i x‖ ≤ ‖fderiv ℝ f x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
      (fderiv ℝ f x).le_opNorm _
    _ ≤ C := by simpa using hb x

theorem memLp_volume_compact_coordinateDerivative {f : Space n → ℝ}
    (hf : LocallyLipschitz f) (hc : HasCompactSupport f) (i : Fin n) :
    MemLp (coordinateDerivative f i) 2 volume := by
  obtain ⟨C, hC, hb⟩ := compact_locallyLipschitz_coordinateDerivative_bound hf hc
  have hI := memLp_indicator_const (μ := (volume : Measure (Space n))) 2
    hc.measurableSet.nullMeasurableSet C (Or.inr hc.measure_lt_top.ne)
  apply hI.mono' (measurable_coordinateDerivative f i).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ tsupport f
    · simpa only [indicator_of_mem hx] using hb i x
    · simp only [indicator_of_notMem hx, coordinateDerivative,
        fderiv_of_notMem_tsupport ℝ hx, zero_apply, norm_zero, le_refl]

end KLS
end
