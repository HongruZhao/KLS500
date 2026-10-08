import KLS.LocalStrongConvexFromHessian

open MeasureTheory Set Filter Matrix Metric InnerProductSpace
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Strong convexity passes through an actual pointwise limit with one fixed
lower coefficient. -/
theorem strongConvexOn_of_pointwise_limit
    {u : Space n → ℝ} {uSeq : ℕ → Space n → ℝ} {S : Set (Space n)} {μ : ℝ}
    (hc : ∀ k, StrongConvexOn S μ (uSeq k))
    (hlim : ∀ x, Tendsto (fun k => uSeq k x) atTop (𝓝 (u x))) :
    StrongConvexOn S μ u := by
  refine ⟨(hc 0).1,?_⟩
  intro x hx y hy a b ha hb hab
  exact le_of_tendsto_of_tendsto (hlim (a • x+b • y))
    ((((hlim x).const_smul a).add ((hlim y).const_smul b)).sub_const
      (a*b*(μ/2*‖x-y‖^2)))
    (Eventually.of_forall fun k => (hc k).2 hx hy ha hb hab)

/-- The original weak moment potential is strongly convex on each compact
convex set. The positive local coefficient comes from actual mollified Hessian
bounds and the actual continuous log-density on its radius-two enlargement. -/
theorem weak_moment_strongConvexOn_compact
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsCompact S) (hSc : Convex ℝ S) :
    ∃ μ : ℝ, 0 < μ ∧ StrongConvexOn S μ u := by
  obtain ⟨B,μ,Λ,_,hμ,_,hell⟩ := weak_moment_mollified_hessian_uniformly_elliptic_on_compact
    hLip hc hV hVc hκ hstrong hK hKc hpush hS
  refine ⟨μ,hμ,strongConvexOn_of_pointwise_limit (uSeq := fun k => mollify k u) (fun k => ?_) (fun x => ?_)⟩
  · apply strongConvexOn_of_hessian_lower_on hSc
      ((mollify_contDiff hLip.continuous.locallyIntegrable k).of_le (by simp))
    exact fun x hx v => (hell k x hx).2.2 v |>.1
  · exact mollify_tendsto_at_moving_points hLip.continuous tendsto_const_nhds tendsto_id

end KLS
end
