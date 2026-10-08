import KLS.GeometricHolderInterpolation

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Central differences of the actual Lipschitz potential are Lipschitz
in their center, with the explicitly displayed scale loss. -/
lemma quadraticCentralDifference_center_bound {u : Space n → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) {h : ℝ} (hh : h ≠ 0) (v c d : Space n) :
    |quadraticCentralDifference u h v c - quadraticCentralDifference u h v d| ≤
      (4 * L / h ^ 2) * ‖c - d‖ := by
  have hp : |u (c + h • v) - u (d + h • v)| ≤ L * ‖c - d‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, add_sub_add_right_eq_sub] using
      hu.dist_le_mul (c + h • v) (d + h • v)
  have hm : |u (c - h • v) - u (d - h • v)| ≤ L * ‖c - d‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, sub_sub_sub_cancel_right] using
      hu.dist_le_mul (c - h • v) (d - h • v)
  have hc : |u c - u d| ≤ L * ‖c - d‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using hu.dist_le_mul c d
  have heq : quadraticCentralDifference u h v c - quadraticCentralDifference u h v d =
      ((u (c + h • v) - u (d + h • v)) +
        (u (c - h • v) - u (d - h • v)) - 2 * (u c - u d)) / h ^ 2 := by
    unfold quadraticCentralDifference
    ring
  rw [heq, abs_div, abs_of_pos (sq_pos_of_ne_zero hh)]
  calc
    _ ≤ (|u (c + h • v) - u (d + h • v)| +
        |u (c - h • v) - u (d - h • v)| + 2 * |u c - u d|) / h ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg h)
      exact (abs_sub _ _).trans (by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
        exact abs_add_le _ _)
    _ ≤ (4 * L / h ^ 2) * ‖c - d‖ := by
      have htotal := add_le_add (add_le_add hp hm) (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))
      have h' := div_le_div_of_nonneg_right htotal (sq_nonneg h)
      convert h' using 1; ring

/-- At the balanced distance scale, the quadratic form of the Hessian
has a geometric modulus proved from actual central differences. -/
theorem quadratic_form_geometric_modulus
    {u : Space n → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {p : Space n → Space n}
    {S : Set (Space n)} {D σ r β θ : ℝ}
    (hD : 0 ≤ D) (hσ : 0 < σ) (hr : 0 < r)
    (hβ : 0 ≤ β) (hβθ : β ≤ θ) (hθ : 0 < θ)
    (hb : ∀ c ∈ S, ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ σ * r ^ j / 2 →
      |u y - centeredQuadratic (H c) c (p c) (u c) y| ≤ D * β ^ j * r ^ (2 * j))
    (j : ℕ) {c d v : Space n} (hc : c ∈ S) (hd : d ∈ S) (hv : ‖v‖ ≤ 2)
    (hcd : ‖c - d‖ ≤ (θ * r ^ 2) ^ j) :
    |inner ℝ v (matrixAction (H c) v) - inner ℝ v (matrixAction (H d) v)| ≤
      (64 * (D + L) / σ ^ 2) * θ ^ j := by
  have hh : 0 < σ * r ^ j / 4 := by positivity
  have hec := scaled_geometric_quadraticCentralDifference_error hσ hr hb j hc hv
  have hed := scaled_geometric_quadraticCentralDifference_error hσ hr hb j hd hv
  have hem := quadraticCentralDifference_center_bound hu hh.ne' v c d
  have hβpow : β ^ j ≤ θ ^ j := pow_le_pow_left₀ hβ hβθ j
  have hmiddle : (4 * L / (σ * r ^ j / 4) ^ 2) * ‖c - d‖ ≤
      (64 * L / σ ^ 2) * θ ^ j := by
    calc
      _ ≤ (4 * L / (σ * r ^ j / 4) ^ 2) * (θ * r ^ 2) ^ j :=
        mul_le_mul_of_nonneg_left hcd (by positivity)
      _ = (64 * L / σ ^ 2) * θ ^ j := by
        rw [mul_pow, ← pow_mul, show 2 * j = j * 2 by omega, pow_mul]
        field_simp
        ring
  have hec' : |inner ℝ v (matrixAction (H c) v) - quadraticCentralDifference u (σ * r ^ j / 4) v c| ≤
      (32 * D / σ ^ 2) * θ ^ j := by
    rw [abs_sub_comm]
    exact hec.trans (mul_le_mul_of_nonneg_left hβpow (by positivity))
  have hed' := hed.trans (mul_le_mul_of_nonneg_left hβpow (show 0 ≤ 32 * D / σ ^ 2 by positivity))
  have he := (abs_sub_le (inner ℝ v (matrixAction (H c) v))
    (quadraticCentralDifference u (σ * r ^ j / 4) v c)
    (inner ℝ v (matrixAction (H d) v))).trans
    (add_le_add hec' ((abs_sub_le _ (quadraticCentralDifference u (σ * r ^ j / 4) v d) _).trans
      (add_le_add (hem.trans hmiddle) hed')))
  exact he.trans_eq (by ring)

end KLS
end
