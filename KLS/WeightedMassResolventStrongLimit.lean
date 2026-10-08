import KLS.WeightedResolventStrongGraphLimit
import KLS.WeightedSmoothL2Density

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Actual mean restoration converts convergence of a centered graph value
into convergence of the full forcing function. -/
theorem weightedMassResolvent_tendsto_of_center_graph (hφ : Continuous φ)
    {α : Type*} {l : Filter α} {t : α → ℝ} (ht : ∀ a, 0 < t a)
    (ht0 : Tendsto t l (𝓝 0)) (g : Lp ℝ 2 (potentialMeasure φ))
    (U : WeightedCenteredH1 φ) (hU : weightedH1Value φ U = CenteredL2.center (potentialMeasure φ) g) :
    Tendsto (fun a => weightedMassResolvent φ (ht a) g) l (𝓝 g) := by
  have hc := weightedResolvent_tendsto_graph_value φ ht ht0 U
  rw [hU] at hc
  have hm := tendsto_const_nhds.add hc (a := weightedMassProjection φ g)
  have he : weightedMassProjection φ g+CenteredL2.center (potentialMeasure φ) g=g := by
    rw [weightedMassProjection_apply,CenteredL2.center]
    abel
  simpa only [weightedResolvent_center hφ,he,← weightedMassResolvent_apply] using hm

/-- Compact smooth forcing has the actual positive-time strong resolvent limit. -/
theorem weightedMassResolvent_tendsto_smoothCompact (hφ : Continuous φ)
    {α : Type*} {l : Filter α} {t : α → ℝ} (ht : ∀ a, 0 < t a)
    (ht0 : Tendsto t l (𝓝 0)) {g : Space n → ℝ}
    (hg : ContDiff ℝ 3 g) (hgc : HasCompactSupport g) (hg2 : MemLp g 2 (potentialMeasure φ)) :
    Tendsto (fun a => weightedMassResolvent φ (ht a) (hg2.toLp g)) l (𝓝 (hg2.toLp g)) := by
  obtain ⟨U,hU,_⟩ := exists_weightedH1_of_smoothCompact hφ hg hgc
  apply weightedMassResolvent_tendsto_of_center_graph hφ ht ht0 (hg2.toLp g) U
  apply Lp.ext
  have hi : (∫ x, hg2.toLp g x ∂potentialMeasure φ)=∫ x, g x ∂potentialMeasure φ :=
    integral_congr_ae hg2.coeFn_toLp
  filter_upwards [hU,CenteredL2.center_ae (potentialMeasure φ) (hg2.toLp g),hg2.coeFn_toLp]
    with x hx hy hz
  rw [hx,hy,hz,hi]

/-- The genuine L2 resolvent converges strongly to the identity along every
positive parameter family tending to zero. Density and L2 contraction are proved prerequisites. -/
theorem weightedMassResolvent_tendsto_zero (hφ : Continuous φ)
    {α : Type*} {l : Filter α} {t : α → ℝ} (ht : ∀ a, 0 < t a)
    (ht0 : Tendsto t l (𝓝 0)) (g : Lp ℝ 2 (potentialMeasure φ)) :
    Tendsto (fun a => weightedMassResolvent φ (ht a) g) l (𝓝 g) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨v,hv,hvg⟩ := Metric.mem_closure_iff.1 (dense_smoothCompactL2 hφ g) (ε/3) (by positivity)
  obtain ⟨f,hf,hfc,hf2,rfl⟩ := hv
  have hl := weightedMassResolvent_tendsto_smoothCompact hφ ht ht0 (hf.of_le (by simp)) hfc hf2
  have he := (Metric.tendsto_nhds.1 hl) (ε/3) (by positivity)
  filter_upwards [he] with a ha
  have hcontract : dist (weightedMassResolvent φ (ht a) g)
      (weightedMassResolvent φ (ht a) (hf2.toLp f)) ≤ dist g (hf2.toLp f) := by
    simpa only [dist_eq_norm,← map_sub] using
      weightedMassResolvent_norm_le hφ (ht a) (g-hf2.toLp f)
  have htri := dist_triangle (weightedMassResolvent φ (ht a) g)
    (weightedMassResolvent φ (ht a) (hf2.toLp f)) g
  have htri2 := dist_triangle (weightedMassResolvent φ (ht a) (hf2.toLp f)) (hf2.toLp f) g
  rw [dist_comm g (hf2.toLp f)] at hcontract hvg
  linarith

/-- The actual two-step resolvent also converges strongly to the identity. -/
theorem weightedMassResolvent_square_tendsto_zero (hφ : Continuous φ)
    {α : Type*} {l : Filter α} {t : α → ℝ} (ht : ∀ a, 0 < t a)
    (ht0 : Tendsto t l (𝓝 0)) (g : Lp ℝ 2 (potentialMeasure φ)) :
    Tendsto (fun a => weightedMassResolvent φ (ht a) (weightedMassResolvent φ (ht a) g)) l
      (𝓝 g) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have he := (Metric.tendsto_nhds.1 (weightedMassResolvent_tendsto_zero hφ ht ht0 g))
    (ε/2) (by positivity)
  filter_upwards [he] with a ha
  have hcontract : dist (weightedMassResolvent φ (ht a) (weightedMassResolvent φ (ht a) g))
      (weightedMassResolvent φ (ht a) g) ≤ dist (weightedMassResolvent φ (ht a) g) g := by
    simpa only [dist_eq_norm,← map_sub] using
      weightedMassResolvent_norm_le hφ (ht a) (weightedMassResolvent φ (ht a) g-g)
  have htri := dist_triangle (weightedMassResolvent φ (ht a) (weightedMassResolvent φ (ht a) g))
    (weightedMassResolvent φ (ht a) g) g
  linarith

end KLS
end
