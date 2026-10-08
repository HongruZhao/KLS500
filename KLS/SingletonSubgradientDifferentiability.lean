import KLS.ConvexSubgradient

/-!
# Singleton subgradients give continuous first derivatives

For a globally Lipschitz convex function, the closed support-plane graph has
compact bounded pieces. A singleton fiber therefore controls all nearby
subgradients. The two support inequalities give the Fréchet remainder bound.
The uniqueness hypotheses here concern subgradients, not support contacts.
-/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

/-- All nearby support slopes approach a singleton fiber of the closed
subgradient graph. -/
theorem eventually_subgradient_norm_sub_lt_of_unique
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    {x p : Space n} (hunique : ∀ q ∈ convexSubgradient u x, q = p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∀ q ∈ convexSubgradient u y, ‖q - p‖ < ε := by
  let G : Set (Space n × Space n) :=
    ((closedBall x 1 ×ˢ closedBall 0 (L : ℝ)) ∩
      {z | z.2 ∈ convexSubgradient u z.1}) ∩ {z | ε ≤ ‖z.2 - p‖}
  have hG : IsCompact G :=
    (((isCompact_closedBall x 1).prod (isCompact_closedBall (0 : Space n) (L : ℝ))).inter_right
      (isClosed_convexSubgradient_graph hLip.continuous)).inter_right
      (isClosed_le continuous_const ((continuous_snd.sub continuous_const).norm))
  have hxnot : x ∉ Prod.fst '' G := by
    rintro ⟨⟨y, q⟩, hyq, heq⟩
    change y = x at heq
    subst y
    have hqp := hunique q hyq.1.2
    have hbad : ε ≤ ‖q - p‖ := hyq.2
    rw [hqp, sub_self, norm_zero] at hbad
    exact (not_le_of_gt hε) hbad
  have havoid : (Prod.fst '' G)ᶜ ∈ 𝓝 x :=
    (hG.image continuous_fst).isClosed.isOpen_compl.mem_nhds hxnot
  filter_upwards [havoid, closedBall_mem_nhds x zero_lt_one] with y hyavoid hyball
  intro q hq
  by_contra hnot
  apply hyavoid
  refine ⟨(y, q), ⟨⟨⟨hyball, ?_⟩, hq⟩, le_of_not_gt hnot⟩, rfl⟩
  simpa only [mem_closedBall, dist_zero_right] using norm_le_of_mem_convexSubgradient hLip hq

/-- A unique ordinary support slope is the actual Fréchet derivative. -/
theorem hasFDerivAt_of_unique_convexSubgradient
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) {x p : Space n}
    (hp : p ∈ convexSubgradient u x)
    (hunique : ∀ q ∈ convexSubgradient u x, q = p) :
    HasFDerivAt u (innerSL ℝ p) x := by
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [eventually_subgradient_norm_sub_lt_of_unique hLip hunique hε] with y hy
  obtain ⟨q, hq⟩ := convexSubgradient_nonempty hLip.continuous hc y
  have hnorm := hy q hq
  have hlow : 0 ≤ u y - u x - inner ℝ p (y - x) := by linarith [hp y]
  have hback := hq x
  have hdiff : x - y = -(y - x) := by abel
  rw [hdiff, inner_neg_right] at hback
  calc
    ‖u y - u x - (innerSL ℝ p) (y - x)‖ = u y - u x - inner ℝ p (y - x) := by
      change |u y - u x - inner ℝ p (y - x)| = _
      exact abs_of_nonneg hlow
    _ ≤ inner ℝ (q - p) (y - x) := by rw [inner_sub_left]; linarith
    _ ≤ ‖q - p‖ * ‖y - x‖ := real_inner_le_norm _ _
    _ ≤ ε * ‖y - x‖ := mul_le_mul_of_nonneg_right hnorm.le (norm_nonneg _)

theorem differentiableAt_of_subsingleton_convexSubgradient
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) {x : Space n}
    (hsingle : (convexSubgradient u x).Subsingleton) : DifferentiableAt ℝ u x := by
  obtain ⟨p, hp⟩ := convexSubgradient_nonempty hLip.continuous hc x
  exact (hasFDerivAt_of_unique_convexSubgradient hLip hc hp
    (fun _ hq => hsingle hq hp)).differentiableAt

/-- Singleton subgradients everywhere imply continuity of the actual
gradient, with no derivative continuity assumed. -/
theorem continuous_gradient_of_subsingleton_convexSubgradient
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u)
    (hsingle : ∀ x, (convexSubgradient u x).Subsingleton) : Continuous (gradient u) := by
  have hd : Differentiable ℝ u :=
    fun x => differentiableAt_of_subsingleton_convexSubgradient hLip hc (hsingle x)
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hxg := gradient_mem_convexSubgradient hc (hd x)
  filter_upwards [eventually_subgradient_norm_sub_lt_of_unique hLip
    (fun _ hq => hsingle x hq hxg) hε] with y hy
  simpa only [dist_eq_norm] using hy (gradient u y) (gradient_mem_convexSubgradient hc (hd y))

/-- A globally Lipschitz convex function with singleton subgradients is C1. -/
theorem contDiff_one_of_subsingleton_convexSubgradient
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u)
    (hsingle : ∀ x, (convexSubgradient u x).Subsingleton) : ContDiff ℝ 1 u := by
  have hd : Differentiable ℝ u :=
    fun x => differentiableAt_of_subsingleton_convexSubgradient hLip hc (hsingle x)
  have hg := continuous_gradient_of_subsingleton_convexSubgradient hLip hc hsingle
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x => innerSL ℝ (gradient u x), ?_, ?_⟩
  · exact (innerSL ℝ).continuous.comp hg
  · intro x
    have hxg := gradient_mem_convexSubgradient hc (hd x)
    exact hasFDerivAt_of_unique_convexSubgradient hLip hc hxg (fun _ hq => hsingle x hq hxg)

end KLS
end

#print axioms KLS.eventually_subgradient_norm_sub_lt_of_unique
#print axioms KLS.hasFDerivAt_of_unique_convexSubgradient
#print axioms KLS.differentiableAt_of_subsingleton_convexSubgradient
#print axioms KLS.continuous_gradient_of_subsingleton_convexSubgradient
#print axioms KLS.contDiff_one_of_subsingleton_convexSubgradient
