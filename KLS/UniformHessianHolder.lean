import KLS.CentralDifferenceHolderBound

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Quantitative Holder control of every Hessian quadratic form. -/
theorem quadratic_form_holder_of_scaled_geometric_taylor
    {u : Space n → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {p : Space n → Space n}
    {S : Set (Space n)} {D σ r β θ γ : ℝ}
    (hD : 0 ≤ D) (hσ : 0 < σ) (hr : 0 < r) (hrone : r < 1)
    (hβ : 0 ≤ β) (hβθ : β ≤ θ) (hθ : 0 < θ) (hθone : θ < 1)
    (hγ : 0 < γ) (hscale : (θ * r ^ 2) ^ γ = θ)
    (hb : ∀ c ∈ S, ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ σ * r ^ j / 2 →
      |u y - centeredQuadratic (H c) c (p c) (u c) y| ≤ D * β ^ j * r ^ (2 * j))
    {c d v : Space n} (hc : c ∈ S) (hd : d ∈ S) (hv : ‖v‖ ≤ 2)
    (hcd : ‖c - d‖ ≤ 1) :
    |inner ℝ v (matrixAction (H c) v) - inner ℝ v (matrixAction (H d) v)| ≤
      (64 * (D + L) / σ ^ 2 / θ) * ‖c - d‖ ^ γ := by
  by_cases heq : c = d
  · subst d
    simp only [sub_self, abs_zero, norm_zero, Real.zero_rpow hγ.ne']
    simp
  have hs : 0 < θ * r ^ 2 := by positivity
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hsone : θ * r ^ 2 < 1 :=
    (mul_lt_of_lt_one_right hθ hr2).trans hθone
  have hmod : ∀ j : ℕ, ∀ c ∈ S, ∀ d ∈ S, dist c d ≤ (θ * r ^ 2) ^ j →
      |inner ℝ v (matrixAction (H c) v) - inner ℝ v (matrixAction (H d) v)| ≤
        (64 * (D + L) / σ ^ 2) * θ ^ j := by
    intro j c hc d hd hdist
    exact quadratic_form_geometric_modulus hu hD hσ hr hβ hβθ hθ hb j hc hd hv
      (by simpa only [dist_eq_norm] using hdist)
  have hh := holder_bound_of_geometric_modulus (show 0 ≤ 64 * (D + L) / σ ^ 2 by positivity)
    hs hsone hθ hγ hscale hmod hc hd (dist_pos.mpr heq)
    (by simpa only [dist_eq_norm] using hcd)
  simpa only [dist_eq_norm] using hh

/-- Polarization converts the uniform scalar bounds into a matrix-norm
Holder bound, with no regularity assumption on the matrix field. -/
theorem hessian_holder_of_uniform_scaled_geometric_taylor
    {u : Space n → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {p : Space n → Space n}
    {S : Set (Space n)} {D σ r β θ γ : ℝ}
    (hH : ∀ c ∈ S, (H c).IsSymm)
    (hD : 0 ≤ D) (hσ : 0 < σ) (hr : 0 < r) (hrone : r < 1)
    (hβ : 0 ≤ β) (hβθ : β ≤ θ) (hθ : 0 < θ) (hθone : θ < 1)
    (hγ : 0 < γ) (hscale : (θ * r ^ 2) ^ γ = θ)
    (hb : ∀ c ∈ S, ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ σ * r ^ j / 2 →
      |u y - centeredQuadratic (H c) c (p c) (u c) y| ≤ D * β ^ j * r ^ (2 * j))
    {c d : Space n} (hc : c ∈ S) (hd : d ∈ S) (hcd : ‖c - d‖ ≤ 1) :
    ‖H c - H d‖ ≤ (96 * (D + L) / σ ^ 2 / θ) * ‖c - d‖ ^ γ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  let ei : Space n := EuclideanSpace.single i 1
  let ej : Space n := EuclideanSpace.single j 1
  have hni : ‖ei‖ = 1 := by simp only [ei, PiLp.norm_single, norm_one]
  have hnj : ‖ej‖ = 1 := by simp only [ej, PiLp.norm_single, norm_one]
  let q := fun v c => inner ℝ v (matrixAction (H c) v)
  let B := (64 * (D + L) / σ ^ 2 / θ) * ‖c - d‖ ^ γ
  have hi : |q ei c - q ei d| ≤ B :=
    quadratic_form_holder_of_scaled_geometric_taylor hu hD hσ hr hrone hβ hβθ hθ hθone
      hγ hscale hb hc hd (by rw [hni]; norm_num) hcd
  have hj : |q ej c - q ej d| ≤ B :=
    quadratic_form_holder_of_scaled_geometric_taylor hu hD hσ hr hrone hβ hβθ hθ hθone
      hγ hscale hb hc hd (by rw [hnj]; norm_num) hcd
  have hij : |q (ei + ej) c - q (ei + ej) d| ≤ B :=
    quadratic_form_holder_of_scaled_geometric_taylor hu hD hσ hr hrone hβ hβθ hθ hθone
      hγ hscale hb hc hd ((norm_add_le _ _).trans (by rw [hni, hnj]; norm_num)) hcd
  have heq : H c i j - H d i j =
      ((q (ei + ej) c - q (ei + ej) d) - (q ei c - q ei d) - (q ej c - q ej d)) / 2 := by
    have hpc := matrix_entry_quadratic_polarization (hH c hc) i j
    have hpd := matrix_entry_quadratic_polarization (hH d hd) i j
    dsimp [q, ei, ej]
    linarith
  simp only [Matrix.sub_apply, Real.norm_eq_abs]
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hab : |(q (ei + ej) c - q (ei + ej) d) - (q ei c - q ei d) - (q ej c - q ej d)| ≤
      |q (ei + ej) c - q (ei + ej) d| + |q ei c - q ei d| + |q ej c - q ej d| :=
    (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
  calc
    _ ≤ (|q (ei + ej) c - q (ei + ej) d| + |q ei c - q ei d| + |q ej c - q ej d|) / 2 :=
      div_le_div_of_nonneg_right hab (by norm_num)
    _ ≤ (B + B + B) / 2 := div_le_div_of_nonneg_right (add_le_add (add_le_add hij hi) hj) (by norm_num)
    _ = (96 * (D + L) / σ ^ 2 / θ) * ‖c - d‖ ^ γ := by dsimp [B]; ring

end KLS
end
