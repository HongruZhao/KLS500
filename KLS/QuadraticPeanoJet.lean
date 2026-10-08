import KLS.GeometricSecondOrderRemainder

open Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma value_zero_of_second_order_small
    {f : Space n → ℝ}
    (hf : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : Space n, ‖x‖ < δ → |f x| ≤ η * ‖x‖ ^ 2) : f 0 = 0 := by
  obtain ⟨δ, hδ, hb⟩ := hf 1 (by norm_num)
  have hh := hb 0 (by simpa only [norm_zero] using hδ)
  have hz : |f 0| ≤ 0 := by simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero] using hh
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

lemma hasGradientAt_zero_of_second_order_small
    {f : Space n → ℝ}
    (hf : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : Space n, ‖x‖ < δ → |f x| ≤ η * ‖x‖ ^ 2) :
    HasGradientAt f (0 : Space n) 0 := by
  have hz := value_zero_of_second_order_small hf
  apply hasGradientAt_iff_isLittleO.mpr
  apply Asymptotics.IsLittleO.of_bound
  intro η hη
  obtain ⟨δ, hδ, hb⟩ := hf 1 (by norm_num)
  filter_upwards [Metric.ball_mem_nhds (0 : Space n) (lt_min hδ hη)] with x hx
  have hx' : ‖x‖ < min δ η := by simpa only [mem_ball_zero_iff] using hx
  have hh := hb x (hx'.trans_le (min_le_left _ _))
  simp only [one_mul] at hh
  have hnorm : ‖x‖ ^ 2 ≤ η * ‖x‖ := by
    have hhx := hx'.le.trans (min_le_right _ _)
    nlinarith [norm_nonneg x]
  simpa only [hz, sub_zero, inner_zero_left, Real.norm_eq_abs] using hh.trans hnorm

/-- A genuine second-order scalar remainder identifies the constant and
linear coefficients with the actual function value and its actual gradient. -/
theorem value_gradient_of_quadratic_remainder
    {u : Space n → ℝ} {H : Matrix (Fin n) (Fin n) ℝ} {p : Space n} {a : ℝ}
    (hH : H.PosSemidef)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : Space n, ‖x‖ < δ →
        |u x - centeredQuadratic H 0 p a x| ≤ η * ‖x‖ ^ 2) :
    a = u 0 ∧ p = gradient u 0 := by
  have hz := value_zero_of_second_order_small hsmall
  have ha : a = u 0 := by
    have hh : u 0 - a = 0 := by simpa only [centeredQuadratic_center] using hz
    exact (sub_eq_zero.mp hh).symm
  have hf := (hasGradientAt_zero_of_second_order_small hsmall).hasFDerivAt
  have hq := ((differentiable_centeredQuadratic H 0 p a) 0).hasGradientAt
  rw [gradient_centeredQuadratic hH, sub_self, map_zero, add_zero] at hq
  have hsum := hf.add hq.hasFDerivAt
  change HasFDerivAt (fun x => (u x - centeredQuadratic H 0 p a x) +
    centeredQuadratic H 0 p a x) _ _ at hsum
  have heq : (fun x => (u x - centeredQuadratic H 0 p a x) + centeredQuadratic H 0 p a x) = u := by
    funext x
    ring
  simp only [map_zero, zero_add, heq] at hsum
  have hp : gradient u 0 = p := (hasGradientAt_iff_hasFDerivAt.mpr hsum).gradient
  exact ⟨ha, hp.symm⟩

/-- The complete perturbative weighted theorem with its genuine value and
gradient in the second-order Peano polynomial. The matrix is positive definite
and has determinant one. Differentiability of the gradient is a separate claim. -/
theorem weighted_exists_quadratic_peano_jet (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∃ Δ : ℝ, 0 < Δ ∧
      ∀ d₀ : NormalizedWeightedMomentData n 1 1, d₀.epsilon < Δ →
      (∀ x ∈ closedBall (0 : Space n) 1,
        |weightedDataDensity d₀ x - 1| ≤ d₀.epsilon ^ 2 * ‖x‖ ^ α) →
      ∃ H : Matrix (Fin n) (Fin n) ℝ, H.PosDef ∧ H.det = 1 ∧
        (fun x => d₀.u x - centeredQuadratic H 0 (gradient d₀.u 0) (d₀.u 0) x)
          =o[𝓝 (0 : Space n)] (fun x => ‖x‖ ^ 2) := by
  obtain ⟨ρ, β, C, Δ, hρ, hρsmall, hβhalf, hβone, hC, hΔ, hquad⟩ :=
    weighted_exists_limiting_quadratic hn hα
  refine ⟨Δ, hΔ, ?_⟩
  intro d₀ hd hholder
  obtain ⟨H, p, a, hHpos, hHdet, hb⟩ := hquad d₀ hd hholder
  have hD : 0 ≤ C * d₀.epsilon := mul_nonneg hC.le d₀.epsilon_pos.le
  have hr : 0 < ρ / 2 := by positivity
  have hrone : ρ / 2 < 1 := by linarith
  have hβ : 0 ≤ β := by linarith
  have hsmall := geometric_second_order_remainder hD hr hrone hβ hβone hb
  obtain ⟨ha, hp⟩ := value_gradient_of_quadratic_remainder hHpos.posSemidef hsmall
  have hrem := geometric_remainder_isLittleO hD hr hrone hβ hβone hb
  rw [ha, hp] at hrem
  exact ⟨H, hHpos, hHdet, hrem⟩

end KLS
end
