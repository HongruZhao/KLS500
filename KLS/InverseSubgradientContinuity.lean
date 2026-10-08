import KLS.MomentCenteredSections
import KLS.SubgradientTransport

/-! Interior slopes have locally bounded inverse support points. Strict
convexity then gives continuity of those inverse points through the closed
primal support graph, without differentiability of the primal potential. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem exists_local_bound_inverse_convexSubgradient
    (u : Space n → ℝ) {p : Space n} (hp : p ∈ interior (momentLegendreDomain u)) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ q : Space n, ‖q - p‖ ≤ r →
      ∀ x : Space n, q ∈ convexSubgradient u x → ‖x‖ ≤ M := by
  obtain ⟨r₀, M₀, hr₀, hgrowth⟩ := exists_linear_lower_bound_tiltedPotential u hp
  let r : ℝ := r₀ / 2
  let B : ℝ := |u 0| + |M₀| + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨r, B / r, hr, div_pos hB hr, ?_⟩
  intro q hq x hx
  have hxzero := hx 0
  simp only [zero_sub, inner_neg_right] at hxzero
  have hinner : inner ℝ (q - p) x ≤ r * ‖x‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
  rw [inner_sub_left] at hinner
  have hg := hgrowth x
  dsimp [tiltedPotential] at hg
  apply (le_div_iff₀ hr).mpr
  have hrdef : r₀ = 2 * r := by dsimp [r]; ring
  rw [hrdef] at hg
  dsimp [B]
  nlinarith [le_abs_self (u 0), le_abs_self M₀]

/-- An interior inverse support point that is unique attracts all inverse
support points for nearby slopes. -/
theorem eventually_inverse_subgradient_norm_sub_lt_of_unique
    {u : Space n → ℝ} (hu : Continuous u)
    {p x : Space n} (hp : p ∈ interior (momentLegendreDomain u))
    (hunique : ∀ y : Space n, p ∈ convexSubgradient u y → y = x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝 p, ∀ y : Space n, q ∈ convexSubgradient u y → ‖y - x‖ < ε := by
  obtain ⟨r, M, hr, hM, hbound⟩ := exists_local_bound_inverse_convexSubgradient u hp
  let G : Set (Space n × Space n) :=
    ((closedBall p r ×ˢ closedBall 0 M) ∩
      {z | z.1 ∈ convexSubgradient u z.2}) ∩ {z | ε ≤ ‖z.2 - x‖}
  have hgraph : IsClosed {z : Space n × Space n | z.1 ∈ convexSubgradient u z.2} :=
    (isClosed_convexSubgradient_graph hu).preimage (continuous_snd.prodMk continuous_fst)
  have hG : IsCompact G :=
    (((isCompact_closedBall p r).prod (isCompact_closedBall (0 : Space n) M)).inter_right
      hgraph).inter_right
      (isClosed_le continuous_const ((continuous_snd.sub continuous_const).norm))
  have hpnot : p ∉ Prod.fst '' G := by
    rintro ⟨⟨q, y⟩, hqy, heq⟩
    change q = p at heq
    subst q
    have hyx := hunique y hqy.1.2
    have hbad : ε ≤ ‖y - x‖ := hqy.2
    rw [hyx, sub_self, norm_zero] at hbad
    exact (not_le_of_gt hε) hbad
  have havoid : (Prod.fst '' G)ᶜ ∈ 𝓝 p :=
    (hG.image continuous_fst).isClosed.isOpen_compl.mem_nhds hpnot
  filter_upwards [havoid, closedBall_mem_nhds p hr] with q hqavoid hqball
  intro y hy
  by_contra hnot
  apply hqavoid
  refine ⟨(q, y), ⟨⟨⟨hqball, ?_⟩, hy⟩, le_of_not_gt hnot⟩, rfl⟩
  have hqr : ‖q - p‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hqball
  simpa only [mem_closedBall, dist_zero_right] using hbound q hqr y hy

theorem eventually_inverse_subgradient_norm_sub_lt_of_strictConvexOn
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {p x : Space n} (hp : p ∈ interior (momentLegendreDomain u))
    (hx : p ∈ convexSubgradient u x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝 p, ∀ y : Space n, q ∈ convexSubgradient u y → ‖y - x‖ < ε :=
  eventually_inverse_subgradient_norm_sub_lt_of_unique hu hp
    (fun _ hy => eq_of_common_convexSubgradient hc hy hx) hε

end KLS
end

#print axioms KLS.exists_local_bound_inverse_convexSubgradient
#print axioms KLS.eventually_inverse_subgradient_norm_sub_lt_of_unique
#print axioms KLS.eventually_inverse_subgradient_norm_sub_lt_of_strictConvexOn
