import KLS.QuadraticDualLocalization

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The exact conjugate of the reference identity quadratic. -/
def centeredDualQuadratic (x₀ p₀ : Space n) (c : ℝ) (p : Space n) : ℝ :=
  inner ℝ p x₀ - c + ‖p-p₀‖ ^ 2 / 2

lemma centeredQuadratic_fenchel_gap (x₀ p₀ : Space n) (c : ℝ) (x p : Space n) :
    centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x +
      centeredDualQuadratic x₀ p₀ c p - inner ℝ p x = ‖(x-x₀)-(p-p₀)‖ ^ 2 / 2 := by
  simp only [centeredQuadratic, centeredDualQuadratic, matrixAction_one_apply,
    real_inner_self_eq_norm_sq, norm_sub_sq_real, inner_sub_right, inner_sub_left]
  rw [real_inner_comm x p, real_inner_comm x p₀, real_inner_comm x₀ p,
    real_inner_comm x₀ p₀, real_inner_comm x₀ x]
  ring

/-- Actual primal supporting contacts localized by the outer-ball comparison
give two-sided bounds on the finite conjugate itself. -/
theorem abs_finiteLegendrePotential_sub_dualQuadratic_le
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    {x₀ p₀ : Space n} {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ δ)
    {p : Space n} (hp : p ∈ closedBall p₀ (R / 4)) :
    |finiteLegendrePotential u p - centeredDualQuadratic x₀ p₀ c p| ≤ δ := by
  obtain ⟨x, hx, hpx⟩ := exists_interior_contact_of_quadratic_closeness hu hc hR hδ hclose hp
  have hxclose := hclose x (interior_subset hx)
  have hgap := centeredQuadratic_fenchel_gap x₀ p₀ c x p
  have hFenchel := finiteLegendrePotential_eq_of_mem_convexSubgradient hpx
  have hpD := mem_momentLegendreDomain_of_support_any_normalization hpx
  let y : Space n := x₀ + (p-p₀)
  have hy : y ∈ closedBall x₀ R := by
    change ‖y-x₀‖ ≤ R
    have hh : y-x₀ = p-p₀ := by dsimp [y]; abel
    rw [hh]
    exact le_trans hp (by linarith)
  have hyclose := hclose y hy
  have hyoung := finiteLegendrePotential_young u hpD y
  have hgapY := centeredQuadratic_fenchel_gap x₀ p₀ c y p
  have hdiff : (y-x₀)-(p-p₀) = 0 := by dsimp [y]; abel
  rw [hdiff, norm_zero, zero_pow (by decide), zero_div] at hgapY
  apply abs_le.mpr
  constructor
  · have hyupper := (abs_le.mp hyclose).2
    linarith
  · have hxlower := (abs_le.mp hxclose).1
    nlinarith [sq_nonneg ‖(x-x₀)-(p-p₀)‖]

/-- For the actual finite conjugate, the normalized dual error is taken with
the opposite sign so that its transport identity agrees with the primal. -/
def normalizedDualQuadraticError (u : Space n → ℝ) (x₀ p₀ : Space n) (c ε : ℝ)
    (p : Space n) : ℝ := (centeredDualQuadratic x₀ p₀ c p - finiteLegendrePotential u p) / ε

lemma abs_normalizedDualQuadraticError_le
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    {x₀ p₀ : Space n} {c R ε M : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hsmall : ε * M ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ ε * M)
    {p : Space n} (hp : p ∈ closedBall p₀ (R / 4)) :
    |normalizedDualQuadraticError u x₀ p₀ c ε p| ≤ M := by
  have hh := abs_finiteLegendrePotential_sub_dualQuadratic_le hu hc hR hsmall hclose hp
  rw [abs_sub_comm] at hh
  rw [normalizedDualQuadraticError, abs_div, abs_of_pos hε]
  exact (div_le_iff₀ hε).mpr (by simpa only [mul_comm] using hh)

/-- Exact Fenchel equality for the true gradient gives the pointwise bridge
between the primal and dual normalized errors and the actual energy density. -/
theorem normalizedDualQuadraticError_gradient_identity
    {u : Space n → ℝ} (hu : ContDiff ℝ 1 u) (hc : ConvexOn ℝ univ u)
    (x₀ p₀ : Space n) (c : ℝ) {ε : ℝ} (hε : ε ≠ 0) (x : Space n) :
    normalizedDualQuadraticError u x₀ p₀ c ε (gradient u x) =
      normalizedQuadraticError u x₀ p₀ c ε x +
        ε / 2 * ‖gradient (normalizedQuadraticError u x₀ p₀ c ε) x‖ ^ 2 := by
  have hFenchel := finiteLegendrePotential_eq_of_mem_convexSubgradient
    (gradient_mem_convexSubgradient hc (hu.differentiable (by norm_num) x))
  have hgap := centeredQuadratic_fenchel_gap x₀ p₀ c x (gradient u x)
  have hd := gradient_sub_affine_eq_scaled_normalized_gradient hu x₀ p₀ c hε x
  have hd' : (x-x₀)-(gradient u x-p₀) =
      -(ε • gradient (normalizedQuadraticError u x₀ p₀ c ε) x) := by rw [← hd]; abel
  rw [hd', norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hgap
  dsimp only [normalizedDualQuadraticError, normalizedQuadraticError]
  rw [hFenchel]
  field_simp
  linarith

end KLS
end
