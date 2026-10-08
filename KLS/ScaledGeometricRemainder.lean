import KLS.QuadraticWhiteningReconstruction

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

theorem scaled_geometric_second_order_remainder
    {f : Space n → ℝ} {D σ r β : ℝ} (hD : 0 ≤ D) (hσ : 0 < σ)
    (hr : 0 < r) (hrone : r < 1) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ (j : ℕ) (x : Space n), ‖x‖ ≤ σ * r ^ j / 2 →
      |f x| ≤ D * β ^ j * r ^ (2 * j)) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : Space n, ‖x‖ < δ → |f x| ≤ η * ‖x‖ ^ 2 := by
  have hscaled : ∀ (j : ℕ) (y : Space n), ‖y‖ ≤ r ^ j / 2 →
      |f (σ • y)| ≤ D * β ^ j * r ^ (2 * j) := by
    intro j y hy
    apply hb
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    have hh := mul_le_mul_of_nonneg_left hy hσ.le
    exact hh.trans_eq (by ring)
  intro η hη
  obtain ⟨δ, hδ, hsmall⟩ := geometric_second_order_remainder hD hr hrone hβ hβone hscaled
    (η * σ ^ 2) (mul_pos hη (sq_pos_of_pos hσ))
  refine ⟨σ * δ, mul_pos hσ hδ, ?_⟩
  intro x hx
  have hnorm : ‖σ⁻¹ • x‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ)]
    apply (mul_lt_mul_iff_right₀ hσ).mp
    simpa only [← mul_assoc, mul_inv_cancel₀ hσ.ne', one_mul] using hx
  have hh := hsmall (σ⁻¹ • x) hnorm
  rw [smul_smul, mul_inv_cancel₀ hσ.ne', one_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hσ)] at hh
  apply hh.trans_eq
  field_simp

/-- Scaled original-coordinate geometric estimates identify the actual
constant and slope, without assuming differentiability of the original data. -/
theorem value_gradient_of_scaled_geometric_taylor
    {u : Space n → ℝ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosSemidef)
    {c p : Space n} {a D σ r β : ℝ} (hD : 0 ≤ D) (hσ : 0 < σ)
    (hr : 0 < r) (hrone : r < 1) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ (j : ℕ) (x : Space n), ‖x - c‖ ≤ σ * r ^ j / 2 →
      |u x - centeredQuadratic H c p a x| ≤ D * β ^ j * r ^ (2 * j)) :
    a = u c ∧ p = gradient u c := by
  let v : Space n → ℝ := fun y => u (c + y)
  have hbound : ∀ (j : ℕ) (y : Space n), ‖y‖ ≤ σ * r ^ j / 2 →
      |v y - centeredQuadratic H 0 p a y| ≤ D * β ^ j * r ^ (2 * j) := by
    intro j y hy
    have hh := hb j (c + y) (by simpa only [add_sub_cancel_left] using hy)
    simpa only [v, centeredQuadratic, sub_zero, add_sub_cancel_left] using hh
  have hsmall := scaled_geometric_second_order_remainder hD hσ hr hrone hβ hβone hbound
  have hh := value_gradient_of_quadratic_remainder hH hsmall
  simpa only [v, gradient_comp_translation, add_zero] using hh

theorem hasFDerivAt_gradient_of_scaled_geometric_taylor
    {u : Space n → ℝ} (hu : Differentiable ℝ u) (huc : ConvexOn ℝ univ u)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) {c : Space n} {D σ r β : ℝ}
    (hD : 0 ≤ D) (hσ : 0 < σ) (hr : 0 < r) (hrone : r < 1) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ σ * r ^ j / 2 →
      |u y - centeredQuadratic H c (gradient u c) (u c) y| ≤ D * β ^ j * r ^ (2 * j)) :
    HasFDerivAt (gradient u) (matrixAction H) c := by
  let v : Space n → ℝ := fun y => u (c + y)
  have hv : Differentiable ℝ v := hu.comp (differentiable_id.const_add c)
  have hvc : ConvexOn ℝ univ v := by
    simpa only [preimage_univ, Function.comp_def] using huc.translate_right c
  have hbound : ∀ (j : ℕ) (y : Space n), ‖y‖ ≤ σ * r ^ j / 2 →
      |v y - centeredQuadratic H 0 (gradient v 0) (v 0) y| ≤ D * β ^ j * r ^ (2 * j) := by
    intro j y hy
    have hh := hb j (c + y) (by simpa only [add_sub_cancel_left] using hy)
    simpa only [v, gradient_comp_translation, add_zero, centeredQuadratic, sub_zero,
      add_sub_cancel_left] using hh
  have hsmall := scaled_geometric_second_order_remainder hD hσ hr hrone hβ hβone hbound
  have hd := convex_hasFDerivAt_gradient_of_second_order_small hv hvc hH hsmall
  have heq : gradient v = fun y => gradient u (c + y) := funext (gradient_comp_translation u c)
  rw [heq] at hd
  simpa only [add_zero] using (hasFDerivAt_comp_add_left c).mp hd

end KLS
end
