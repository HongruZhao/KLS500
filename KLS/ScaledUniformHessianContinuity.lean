import KLS.ScaledGeometricRemainder

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

lemma scaled_geometric_quadraticCentralDifference_error
    {u : Space n → ℝ} {H : Space n → Matrix (Fin n) (Fin n) ℝ}
    {p : Space n → Space n} {S : Set (Space n)} {D σ r β : ℝ}
    (hσ : 0 < σ) (hr : 0 < r)
    (hb : ∀ c ∈ S, ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ σ * r ^ j / 2 →
      |u y - centeredQuadratic (H c) c (p c) (u c) y| ≤ D * β ^ j * r ^ (2 * j))
    (j : ℕ) {c v : Space n} (hc : c ∈ S) (hv : ‖v‖ ≤ 2) :
    |quadraticCentralDifference u (σ * r ^ j / 4) v c - inner ℝ v (matrixAction (H c) v)| ≤
      (32 * D / σ ^ 2) * β ^ j := by
  have hh : 0 < σ * r ^ j / 4 := by positivity
  have hp : ‖(c + (σ * r ^ j / 4) • v) - c‖ ≤ σ * r ^ j / 2 := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    nlinarith
  have hm : ‖(c - (σ * r ^ j / 4) • v) - c‖ ≤ σ * r ^ j / 2 := by
    rw [show c - (σ * r ^ j / 4) • v - c = -((σ * r ^ j / 4) • v) by abel, norm_neg]
    simpa only [add_sub_cancel_left] using hp
  have he := quadraticCentralDifference_error_le hh.ne' (hb c hc j _ hp) (hb c hc j _ hm)
  apply he.trans_eq
  rw [show r ^ (2 * j) = (r ^ j) ^ 2 by rw [← pow_mul, Nat.mul_comm]]
  field_simp
  ring

theorem continuousOn_quadratic_form_of_scaled_geometric_taylor
    {u : Space n → ℝ} (hu : Continuous u)
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {p : Space n → Space n}
    {S : Set (Space n)} {D σ r β : ℝ}
    (hσ : 0 < σ) (hr : 0 < r) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ c ∈ S, ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ σ * r ^ j / 2 →
      |u y - centeredQuadratic (H c) c (p c) (u c) y| ≤ D * β ^ j * r ^ (2 * j))
    {v : Space n} (hv : ‖v‖ ≤ 2) :
    ContinuousOn (fun c => inner ℝ v (matrixAction (H c) v)) S := by
  have hlim : Tendsto (fun j : ℕ => (32 * D / σ ^ 2) * β ^ j) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβone)
  have huni : TendstoUniformlyOn (fun j => quadraticCentralDifference u (σ * r ^ j / 4) v)
      (fun c => inner ℝ v (matrixAction (H c) v)) atTop S := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with j hj
    intro c hc
    rw [Real.dist_eq, abs_sub_comm]
    exact (scaled_geometric_quadraticCentralDifference_error hσ hr hb j hc hv).trans_lt hj
  exact huni.continuousOn (Eventually.of_forall (fun j =>
    (continuous_quadraticCentralDifference hu (σ * r ^ j / 4) v).continuousOn)).frequently

theorem continuousOn_hessian_of_uniform_scaled_geometric_taylor
    {u : Space n → ℝ} (hu : Continuous u)
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {p : Space n → Space n}
    {S : Set (Space n)} {D σ r β : ℝ}
    (hH : ∀ c ∈ S, (H c).IsSymm)
    (hσ : 0 < σ) (hr : 0 < r) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ c ∈ S, ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ σ * r ^ j / 2 →
      |u y - centeredQuadratic (H c) c (p c) (u c) y| ≤ D * β ^ j * r ^ (2 * j)) :
    ContinuousOn H S := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hnorm (k : Fin n) : ‖(EuclideanSpace.single k 1 : Space n)‖ = 1 := by
    simp only [PiLp.norm_single, norm_one]
  have hi := continuousOn_quadratic_form_of_scaled_geometric_taylor hu hσ hr hβ hβone hb
    (v := EuclideanSpace.single i 1) (by rw [hnorm]; norm_num)
  have hj := continuousOn_quadratic_form_of_scaled_geometric_taylor hu hσ hr hβ hβone hb
    (v := EuclideanSpace.single j 1) (by rw [hnorm]; norm_num)
  have hij := continuousOn_quadratic_form_of_scaled_geometric_taylor hu hσ hr hβ hβone hb
    (v := EuclideanSpace.single i 1 + EuclideanSpace.single j 1)
    ((norm_add_le _ _).trans (by rw [hnorm, hnorm]; norm_num))
  apply (((hij.sub hi).sub hj).div_const 2).congr
  intro c hc
  exact matrix_entry_quadratic_polarization (hH c hc) i j

theorem contDiffOn_two_of_uniform_scaled_geometric_taylor
    {u : Space n → ℝ} (hu : Differentiable ℝ u) (huc : ConvexOn ℝ univ u)
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {S : Set (Space n)} {D σ r β : ℝ}
    (hS : IsOpen S) (hH : ∀ c ∈ S, (H c).IsSymm)
    (hD : 0 ≤ D) (hσ : 0 < σ) (hr : 0 < r) (hrone : r < 1) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ c ∈ S, ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ σ * r ^ j / 2 →
      |u y - centeredQuadratic (H c) c (gradient u c) (u c) y| ≤ D * β ^ j * r ^ (2 * j)) :
    ContDiffOn ℝ 2 u S := by
  have hcontinuous := continuousOn_hessian_of_uniform_scaled_geometric_taylor hu.continuous hH hσ hr hβ hβone hb
  apply contDiffOn_two_of_continuous_gradient_derivative hu hS hcontinuous
  intro c hc
  exact hasFDerivAt_gradient_of_scaled_geometric_taylor hu huc (hH c hc)
    hD hσ hr hrone hβ hβone (hb c hc)

end KLS
end
