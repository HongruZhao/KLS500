import KLS.RelativeFenchelSubgradient
import KLS.InverseSubgradientContinuity

/-!
# C1 regularity of the finite conjugate on its true interior

Primal strict convexity makes every attained inverse support point unique.
The closed inverse support graph and its local boundedness give the actual
Fréchet derivative of the conjugate and continuity of its gradient. No
differentiability of the primal potential is used.
-/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem hasFDerivAt_finiteLegendrePotential_of_strictConvexOn
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {p x : Space n} (hp : p ∈ interior (momentLegendreDomain u))
    (hx : p ∈ convexSubgradient u x) :
    HasFDerivAt (finiteLegendrePotential u) (innerSL ℝ x) p := by
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [eventually_inverse_subgradient_norm_sub_lt_of_strictConvexOn hu hc hp hx hε,
    isOpen_interior.mem_nhds hp] with q hnear hqD
  obtain ⟨y, hy⟩ := exists_mem_convexSubgradient_of_mem_interior_momentLegendreDomain hu hqD
  have hnorm := hnear y hy
  have hpx := (mem_convexSubgradientOn_finiteLegendrePotential_iff hu hc.convexOn p x).mpr hx
  have hqy := (mem_convexSubgradientOn_finiteLegendrePotential_iff hu hc.convexOn q y).mpr hy
  have hforward := hpx.2 q (interior_subset hqD)
  have hback := hqy.2 p (interior_subset hp)
  have hdiff : p - q = -(q - p) := by abel
  rw [hdiff, inner_neg_right] at hback
  have hlow : 0 ≤ finiteLegendrePotential u q - finiteLegendrePotential u p -
      inner ℝ x (q - p) := by linarith
  calc
    ‖finiteLegendrePotential u q - finiteLegendrePotential u p - (innerSL ℝ x) (q - p)‖ =
        finiteLegendrePotential u q - finiteLegendrePotential u p - inner ℝ x (q - p) := by
      change |finiteLegendrePotential u q - finiteLegendrePotential u p - inner ℝ x (q - p)| = _
      exact abs_of_nonneg hlow
    _ ≤ inner ℝ (y - x) (q - p) := by rw [inner_sub_left]; linarith
    _ ≤ ‖y - x‖ * ‖q - p‖ := real_inner_le_norm _ _
    _ ≤ ε * ‖q - p‖ := mul_le_mul_of_nonneg_right hnorm.le (norm_nonneg _)

theorem differentiableAt_finiteLegendrePotential_of_strictConvexOn
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {p : Space n} (hp : p ∈ interior (momentLegendreDomain u)) :
    DifferentiableAt ℝ (finiteLegendrePotential u) p := by
  obtain ⟨x, hx⟩ := exists_mem_convexSubgradient_of_mem_interior_momentLegendreDomain hu hp
  exact (hasFDerivAt_finiteLegendrePotential_of_strictConvexOn hu hc hp hx).differentiableAt

/-- Every finite interior contact has the original point as the actual
conjugate gradient. -/
theorem gradient_finiteLegendrePotential_eq_of_mem_convexSubgradient
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {p x : Space n} (hp : p ∈ interior (momentLegendreDomain u))
    (hx : p ∈ convexSubgradient u x) : gradient (finiteLegendrePotential u) p = x := by
  exact (eq_gradient_of_support_on_interior hp
    (hasFDerivAt_finiteLegendrePotential_of_strictConvexOn hu hc hp hx).differentiableAt
    ((mem_convexSubgradientOn_finiteLegendrePotential_iff hu hc.convexOn p x).mpr hx).2).symm

theorem mem_convexSubgradient_gradient_finiteLegendrePotential
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {p : Space n} (hp : p ∈ interior (momentLegendreDomain u)) :
    p ∈ convexSubgradient u (gradient (finiteLegendrePotential u) p) := by
  obtain ⟨x, hx⟩ := exists_mem_convexSubgradient_of_mem_interior_momentLegendreDomain hu hp
  rw [gradient_finiteLegendrePotential_eq_of_mem_convexSubgradient hu hc hp hx]
  exact hx

theorem convexSubgradientOn_finiteLegendrePotential_eq_singleton
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {p : Space n} (hp : p ∈ interior (momentLegendreDomain u)) :
    convexSubgradientOn (finiteLegendrePotential u) (momentLegendreDomain u) p =
      {gradient (finiteLegendrePotential u) p} := by
  ext x
  rw [mem_convexSubgradientOn_finiteLegendrePotential_iff hu hc.convexOn, mem_singleton_iff]
  constructor
  · intro hx
    exact (gradient_finiteLegendrePotential_eq_of_mem_convexSubgradient hu hc hp hx).symm
  · intro hx
    rw [hx]
    exact mem_convexSubgradient_gradient_finiteLegendrePotential hu hc hp

theorem continuousAt_gradient_finiteLegendrePotential_of_strictConvexOn
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {p : Space n} (hp : p ∈ interior (momentLegendreDomain u)) :
    ContinuousAt (gradient (finiteLegendrePotential u)) p := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hx := mem_convexSubgradient_gradient_finiteLegendrePotential hu hc hp
  filter_upwards [eventually_inverse_subgradient_norm_sub_lt_of_strictConvexOn hu hc hp hx hε,
    isOpen_interior.mem_nhds hp] with q hnear hqD
  simpa only [dist_eq_norm] using hnear (gradient (finiteLegendrePotential u) q)
    (mem_convexSubgradient_gradient_finiteLegendrePotential hu hc hqD)

theorem continuousOn_gradient_finiteLegendrePotential_of_strictConvexOn
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u) :
    ContinuousOn (gradient (finiteLegendrePotential u)) (interior (momentLegendreDomain u)) :=
  fun _ hp => (continuousAt_gradient_finiteLegendrePotential_of_strictConvexOn hu hc hp).continuousWithinAt

/-- The conjugate is C1 on the genuine finite-domain interior. This theorem
does not assert strict convexity of the conjugate or C1 of the primal. -/
theorem contDiffOn_one_finiteLegendrePotential_of_strictConvexOn
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u) :
    ContDiffOn ℝ 1 (finiteLegendrePotential u) (interior (momentLegendreDomain u)) := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := 0) isOpen_interior.uniqueDiffOn).mpr
  refine ⟨by simp, fun p => innerSL ℝ (gradient (finiteLegendrePotential u) p), ?_, ?_⟩
  · apply contDiffOn_zero.mpr
    exact (innerSL ℝ).continuous.comp_continuousOn
      (continuousOn_gradient_finiteLegendrePotential_of_strictConvexOn hu hc)
  · intro p hp
    exact (hasFDerivAt_finiteLegendrePotential_of_strictConvexOn hu hc hp
      (mem_convexSubgradient_gradient_finiteLegendrePotential hu hc hp)).hasFDerivWithinAt

end KLS
end

#print axioms KLS.hasFDerivAt_finiteLegendrePotential_of_strictConvexOn
#print axioms KLS.gradient_finiteLegendrePotential_eq_of_mem_convexSubgradient
#print axioms KLS.continuousOn_gradient_finiteLegendrePotential_of_strictConvexOn
#print axioms KLS.contDiffOn_one_finiteLegendrePotential_of_strictConvexOn
