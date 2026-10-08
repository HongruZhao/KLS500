import KLS.GeneralCenteredWeightedData

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

lemma unit_quadratic_recenter (a : ℝ) (c x : Space n) :
    centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 a x =
      centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) c c
        (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 a c) x := by
  have hh := centeredQuadratic_support_identity (Matrix.isSymm_one (n := Fin n)) 0 0 a c x
  simp only [sub_zero, matrixAction_one_apply, zero_add] at hh
  change _ = centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 a c +
    inner ℝ c (x - c) + (1 / 2 : ℝ) * inner ℝ (x - c) (matrixAction 1 (x - c))
  rw [matrixAction_one_apply]
  linarith

lemma abs_centered_quadratic_hessian_difference_le
    (A B : Matrix (Fin n) (Fin n) ℝ) (c p : Space n) (a : ℝ) (x : Space n) :
    |centeredQuadratic A c p a x - centeredQuadratic B c p a x| ≤
      (1 / 2 : ℝ) * ‖matrixAction (A - B)‖ * ‖x - c‖ ^ 2 := by
  have hh := centeredQuadratic_coefficient_difference_le A B p p a a (x - c)
  simpa only [centeredQuadratic, sub_zero, sub_self, norm_zero, abs_zero, zero_mul, zero_add] using hh

lemma recentered_half_ball_subset_unit {c x : Space n}
    (hc : ‖c‖ ≤ 1 / 4) (hx : ‖x - c‖ ≤ 1 / 2) : ‖x‖ ≤ 1 := by
  have hh : ‖x‖ ≤ ‖x - c‖ + ‖c‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - c) c
  linarith

/-- A single near-unit-quadratic datum supplies a quantitative near-quadratic
initializer about every point of the inner ball, for every calibrated
matrix within epsilon squared of the identity. -/
theorem recentered_quadratic_flatness
    (d₀ : NormalizedWeightedMomentData n 1 1) (hε : d₀.epsilon ≤ 1)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : ‖matrixAction (A - 1)‖ ≤ d₀.epsilon ^ 2)
    {c : Space n} (hc : ‖c‖ ≤ 1 / 4) :
    ∀ x ∈ closedBall c (1 / 2),
      |d₀.u x - centeredQuadratic A c c
        (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d₀.c c) x| ≤ 2 * d₀.epsilon := by
  intro x hx
  have hxn : ‖x - c‖ ≤ 1 / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hx
  have hxunit : x ∈ closedBall (0 : Space n) 1 := by
    rw [mem_closedBall_zero_iff]
    exact recentered_half_ball_subset_unit hc hxn
  have hbase := normalized_weighted_quadratic_bound d₀ hxunit
  have hquad := abs_centered_quadratic_hessian_difference_le A 1 c c
    (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d₀.c c) x
  have hbound : (1 / 2 : ℝ) * ‖matrixAction (A - 1)‖ * ‖x - c‖ ^ 2 ≤ d₀.epsilon ^ 2 / 8 := by
    calc
      _ ≤ (1 / 2 : ℝ) * d₀.epsilon ^ 2 * (1 / 2 : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  have hquad' := hquad.trans hbound
  rw [← unit_quadratic_recenter, abs_sub_comm] at hquad'
  have htriangle := abs_sub_le (d₀.u x)
    (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d₀.c x)
    (centeredQuadratic A c c (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d₀.c c) x)
  have heps := d₀.epsilon_pos
  nlinarith

end KLS
end
