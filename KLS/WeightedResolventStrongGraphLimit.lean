import KLS.WeightedMassResolventIdentity

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual variational resolvent approaches a graph value at the energy rate. -/
theorem weightedResolvent_graph_error_sq_le (φ : Space n → ℝ)
    {t : ℝ} (ht : 0 < t) (U : WeightedCenteredH1 φ) :
    ‖weightedResolvent φ ht (weightedH1Value φ U)-weightedH1Value φ U‖ ^ 2 ≤
      t*weightedEnergyForm φ U U := by
  let R := weightedResolventH1 φ ht (weightedH1Value φ U)
  have hv := weightedResolvent_variational φ ht (weightedH1Value φ U) (R-U)
  have hR : weightedH1Value φ R=weightedResolvent φ ht (weightedH1Value φ U) := rfl
  have hE (V : WeightedCenteredH1 φ) : 0 ≤ weightedEnergyForm φ V V := by
    rw [weightedEnergyForm_self]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hRU := hE (R-U)
  simp only [map_sub,sub_apply] at hRU
  rw [weightedEnergyForm_symm φ U R] at hRU
  have hR0 := mul_nonneg ht.le (hE R)
  have hRU0 := mul_nonneg ht.le hRU
  simp only [map_sub,inner_sub_right,hR] at hv
  have hn := norm_sub_sq_real (weightedResolvent φ ht (weightedH1Value φ U)) (weightedH1Value φ U)
  rw [real_inner_comm (weightedH1Value φ U) (weightedResolvent φ ht (weightedH1Value φ U)),
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hv
  rw [real_inner_comm (weightedH1Value φ U) (weightedResolvent φ ht (weightedH1Value φ U))] at hn
  dsimp only [R] at hv hR0 hRU0
  nlinarith

/-- Strong convergence to a concrete graph value along every positive parameter
family tending to zero, proved directly from its actual energy. -/
theorem weightedResolvent_tendsto_graph_value (φ : Space n → ℝ)
    {α : Type*} {l : Filter α} {t : α → ℝ} (ht : ∀ a, 0 < t a)
    (ht0 : Tendsto t l (𝓝 0)) (U : WeightedCenteredH1 φ) :
    Tendsto (fun a => weightedResolvent φ (ht a) (weightedH1Value φ U)) l
      (𝓝 (weightedH1Value φ U)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hm : Tendsto (fun a => t a*weightedEnergyForm φ U U) l (𝓝 0) := by
    simpa using ht0.mul_const (weightedEnergyForm φ U U)
  have he := hm.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  filter_upwards [he] with a ha
  rw [dist_eq_norm]
  have hb := weightedResolvent_graph_error_sq_le φ (ht a) U
  nlinarith [norm_nonneg (weightedResolvent φ (ht a) (weightedH1Value φ U)-weightedH1Value φ U)]

end KLS
end
