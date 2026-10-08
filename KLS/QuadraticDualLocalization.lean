import KLS.NormalizedTransportCost
import KLS.FiniteConjugateC1

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Uniform quadratic closeness on an outer ball forces all sufficiently
central slopes to have actual supporting contacts inside that ball. -/
theorem exists_interior_contact_of_quadratic_closeness
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    {x₀ p₀ : Space n} {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ δ)
    {p : Space n} (hp : p ∈ closedBall p₀ (R / 4)) :
    ∃ x ∈ interior (closedBall x₀ R), p ∈ convexSubgradient u x := by
  let v : Space n → ℝ := fun x => u x₀ + R ^ 2 / 16 + inner ℝ p (x-x₀)
  have hcenter := hclose x₀ (mem_closedBall_self hR.le)
  simp only [centeredQuadratic_center] at hcenter
  have hpR : ‖p-p₀‖ ≤ R / 4 := hp
  have hb : ∀ x ∈ frontier (closedBall x₀ R), v x ≤ u x := by
    intro x hx
    have hxR : ‖x-x₀‖ = R := frontier_closedBall_subset_sphere hx
    have hxK : x ∈ closedBall x₀ R := by change ‖x-x₀‖ ≤ R; exact hxR.le
    have he := hclose x hxK
    simp only [centeredQuadratic, matrixAction_one_apply, real_inner_self_eq_norm_sq, hxR] at he
    have hi : inner ℝ (p-p₀) (x-x₀) ≤ R ^ 2 / 4 := calc
      _ ≤ ‖p-p₀‖ * ‖x-x₀‖ := real_inner_le_norm _ _
      _ ≤ (R / 4) * R := by rw [hxR]; exact mul_le_mul_of_nonneg_right hpR hR.le
      _ = R ^ 2 / 4 := by ring
    rw [inner_sub_left] at hi
    have hz := (abs_le.mp he).1
    have hc0 := (abs_le.mp hcenter).2
    dsimp [v]
    nlinarith [sq_nonneg R]
  have hpv : p ∈ convexSubgradient v x₀ := by
    intro y
    simp only [v, sub_self, inner_zero_right, add_zero]
    exact le_rfl
  obtain ⟨x, hx, _, hpx⟩ := exists_subgradient_contact_in_strict_comparison
    (isCompact_closedBall x₀ R) hu hc hb (mem_closedBall_self hR.le)
    (show u x₀ < v x₀ by simp only [v, sub_self, inner_zero_right, add_zero]; nlinarith)
    hpv
  exact ⟨x, hx, hpx⟩

/-- The genuine finite conjugate domain contains a quantitative inner ball,
with no assumed gradient surjectivity. -/
theorem ball_subset_interior_momentLegendreDomain_of_quadratic_closeness
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    {x₀ p₀ : Space n} {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ δ) :
    ball p₀ (R / 4) ⊆ interior (momentLegendreDomain u) := by
  apply isOpen_ball.subset_interior_iff.mpr
  intro p hp
  obtain ⟨x, _, hx⟩ := exists_interior_contact_of_quadratic_closeness hu hc hR hδ hclose
    (ball_subset_closedBall hp)
  exact mem_momentLegendreDomain_of_support_any_normalization hx

/-- Under strict convexity every preimage of a central slope is localized;
this applies in particular to the actual inverse gradient of the conjugate. -/
theorem mem_interior_closedBall_of_central_subgradient
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {x₀ p₀ : Space n} {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ δ)
    {x p : Space n} (hp : p ∈ closedBall p₀ (R / 4))
    (hpx : p ∈ convexSubgradient u x) : x ∈ interior (closedBall x₀ R) := by
  obtain ⟨y, hy, hpy⟩ := exists_interior_contact_of_quadratic_closeness hu hc.convexOn hR hδ hclose hp
  exact (eq_of_common_convexSubgradient hc hpx hpy) ▸ hy

lemma gradient_finiteLegendrePotential_mem_interior_closedBall_of_quadratic_closeness
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {x₀ p₀ : Space n} {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ δ)
    {p : Space n} (hp : p ∈ ball p₀ (R / 4)) :
    gradient (finiteLegendrePotential u) p ∈ interior (closedBall x₀ R) := by
  apply mem_interior_closedBall_of_central_subgradient hu hc hR hδ hclose (ball_subset_closedBall hp)
  exact mem_convexSubgradient_gradient_finiteLegendrePotential hu hc
    (ball_subset_interior_momentLegendreDomain_of_quadratic_closeness hu hc.convexOn hR hδ hclose hp)

end KLS
end
