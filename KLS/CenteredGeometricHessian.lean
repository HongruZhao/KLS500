import KLS.UniformQuadraticHessianContinuity

open Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma gradient_comp_translation (u : Space n → ℝ) (c x : Space n) :
    gradient (fun y => u (c + y)) x = gradient u (c + x) := by
  simp only [gradient, fderiv_comp_add_left]

/-- The pointwise derivative theorem transfers to every specified center.
The geometric approximation is of the same actual function in its original
coordinates. -/
theorem hasFDerivAt_gradient_of_centered_geometric_taylor
    {u : Space n → ℝ} (hu : Differentiable ℝ u) (huc : ConvexOn ℝ univ u)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) {c : Space n} {D r β : ℝ}
    (hD : 0 ≤ D) (hr : 0 < r) (hrone : r < 1) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ r ^ j / 2 →
      |u y - centeredQuadratic H c (gradient u c) (u c) y| ≤ D * β ^ j * r ^ (2 * j)) :
    HasFDerivAt (gradient u) (matrixAction H) c := by
  let v : Space n → ℝ := fun y => u (c + y)
  have hv : Differentiable ℝ v := hu.comp (differentiable_id.const_add c)
  have hvc : ConvexOn ℝ univ v := by
    simpa only [preimage_univ, Function.comp_def] using huc.translate_right c
  have hbound : ∀ (j : ℕ) (y : Space n), ‖y‖ ≤ r ^ j / 2 →
      |v y - centeredQuadratic H 0 (gradient v 0) (v 0) y| ≤ D * β ^ j * r ^ (2 * j) := by
    intro j y hy
    have hh := hb j (c + y) (by simpa only [add_sub_cancel_left] using hy)
    simpa only [v, gradient_comp_translation, add_zero, centeredQuadratic, sub_zero,
      add_sub_cancel_left] using hh
  have hrem := geometric_remainder_isLittleO hD hr hrone hβ hβone hbound
  have hd := convex_hasFDerivAt_gradient_of_quadratic_peano hv hvc hH hrem
  have heq : gradient v = fun y => gradient u (c + y) := funext (gradient_comp_translation u c)
  rw [heq] at hd
  simpa only [add_zero] using (hasFDerivAt_comp_add_left c).mp hd

/-- A uniform neighborhood family gives actual second derivatives and a
continuous actual coordinate Hessian. Continuity is proved from central
differences, independently of any regularity of a chosen coefficient field. -/
theorem continuousOn_actual_hessian_of_uniform_geometric_taylor
    {u : Space n → ℝ} (hu : Differentiable ℝ u) (huc : ConvexOn ℝ univ u)
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {S : Set (Space n)} {D r β : ℝ}
    (hH : ∀ c ∈ S, (H c).IsSymm)
    (hD : 0 ≤ D) (hr : 0 < r) (hrone : r < 1) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ c ∈ S, ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ r ^ j / 2 →
      |u y - centeredQuadratic (H c) c (gradient u c) (u c) y| ≤ D * β ^ j * r ^ (2 * j)) :
    (∀ c ∈ S, coordinateHessian u c = H c ∧
      HasFDerivAt (gradient u) (matrixAction (H c)) c) ∧
      ContinuousOn (coordinateHessian u) S := by
  have hd (c : Space n) (hc : c ∈ S) := hasFDerivAt_gradient_of_centered_geometric_taylor
    hu huc (hH c hc) hD hr hrone hβ hβone (hb c hc)
  have heq (c : Space n) (hc : c ∈ S) := coordinateHessian_eq_of_hasFDerivAt_gradient (hH c hc) (hd c hc)
  refine ⟨fun c hc => ⟨heq c hc, hd c hc⟩, ?_⟩
  exact (continuousOn_hessian_of_uniform_geometric_taylor hu.continuous hH hr hβ hβone hb).congr heq

end KLS
end
