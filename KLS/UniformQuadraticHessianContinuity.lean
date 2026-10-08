import KLS.QuadraticCentralDifference

open Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

theorem continuousOn_quadratic_form_of_uniform_geometric_taylor
    {u : Space n → ℝ} (hu : Continuous u)
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {p : Space n → Space n}
    {S : Set (Space n)} {D r β : ℝ}
    (hr : 0 < r) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ c ∈ S, ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ r ^ j / 2 →
      |u y - centeredQuadratic (H c) c (p c) (u c) y| ≤ D * β ^ j * r ^ (2 * j))
    {v : Space n} (hv : ‖v‖ ≤ 2) :
    ContinuousOn (fun c => inner ℝ v (matrixAction (H c) v)) S := by
  have hlim : Tendsto (fun j : ℕ => 32 * D * β ^ j) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβone)
  have huni : TendstoUniformlyOn (fun j => quadraticCentralDifference u (r ^ j / 4) v)
      (fun c => inner ℝ v (matrixAction (H c) v)) atTop S := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with j hj
    intro c hc
    rw [Real.dist_eq, abs_sub_comm]
    exact (geometric_quadraticCentralDifference_error hr hb j hc hv).trans_lt hj
  exact huni.continuousOn (Eventually.of_forall (fun j =>
    (continuous_quadraticCentralDifference hu (r ^ j / 4) v).continuousOn)).frequently

lemma matrix_entry_quadratic_polarization
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (i j : Fin n) :
    A i j = (inner ℝ (EuclideanSpace.single i 1 + EuclideanSpace.single j 1)
        (matrixAction A (EuclideanSpace.single i 1 + EuclideanSpace.single j 1)) -
      inner ℝ (EuclideanSpace.single i 1) (matrixAction A (EuclideanSpace.single i 1)) -
      inner ℝ (EuclideanSpace.single j 1) (matrixAction A (EuclideanSpace.single j 1))) / 2 := by
  have he (k l : Fin n) : inner ℝ (EuclideanSpace.single k 1)
      (matrixAction A (EuclideanSpace.single l 1)) = A k l := by
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul, matrixAction_apply,
      PiLp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [map_add, inner_add_left, inner_add_right, he]
  rw [hA.apply j i]
  ring

/-- The symmetric quadratic coefficient field is continuous whenever one
continuous function has uniform geometric quadratic approximations about
every center in the set. No continuity of the chosen coefficients is assumed. -/
theorem continuousOn_hessian_of_uniform_geometric_taylor
    {u : Space n → ℝ} (hu : Continuous u)
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {p : Space n → Space n}
    {S : Set (Space n)} {D r β : ℝ}
    (hH : ∀ c ∈ S, (H c).IsSymm)
    (hr : 0 < r) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ c ∈ S, ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ r ^ j / 2 →
      |u y - centeredQuadratic (H c) c (p c) (u c) y| ≤ D * β ^ j * r ^ (2 * j)) :
    ContinuousOn H S := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hnorm (k : Fin n) : ‖(EuclideanSpace.single k 1 : Space n)‖ = 1 := by
    simp only [PiLp.norm_single, norm_one]
  have hi := continuousOn_quadratic_form_of_uniform_geometric_taylor hu hr hβ hβone hb
    (v := EuclideanSpace.single i 1) (by rw [hnorm]; norm_num)
  have hj := continuousOn_quadratic_form_of_uniform_geometric_taylor hu hr hβ hβone hb
    (v := EuclideanSpace.single j 1) (by rw [hnorm]; norm_num)
  have hij := continuousOn_quadratic_form_of_uniform_geometric_taylor hu hr hβ hβone hb
    (v := EuclideanSpace.single i 1 + EuclideanSpace.single j 1)
    ((norm_add_le _ _).trans (by rw [hnorm, hnorm]; norm_num))
  apply (((hij.sub hi).sub hj).div_const 2).congr
  intro c hc
  exact matrix_entry_quadratic_polarization (hH c hc) i j

end KLS
end
