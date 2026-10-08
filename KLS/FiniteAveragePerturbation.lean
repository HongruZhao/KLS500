import KLS.FiniteIsometryAverageAlgebra

/-! A proved perturbation estimate for recovering an arbitrary vector from
an average, using a nearby vector that satisfies a block-recovery estimate. -/

open scoped BigOperators
noncomputable section
namespace KLS

theorem norm_sq_le_of_near_average_recovery {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Group G] [Fintype G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E) {c : ℝ} (hc : 1 ≤ c)
    (hy : ‖y‖ ≤ c * ‖finiteIsometryAverage ρ y‖) :
    ‖x‖ ^ 2 ≤ 2 * c ^ 2 * ‖finiteIsometryAverage ρ x‖ ^ 2 + 8 * c ^ 2 * ‖x - y‖ ^ 2 := by
  let S := finiteIsometryAverageLinearMap ρ
  have hSy : ‖S y‖ ≤ ‖S x‖ + ‖x - y‖ := by
    calc
      _ ≤ ‖S y - S x‖ + ‖S x‖ := norm_le_norm_sub_add _ _
      _ = ‖S (y - x)‖ + ‖S x‖ := by rw [map_sub]
      _ ≤ ‖y - x‖ + ‖S x‖ := add_le_add (norm_finiteIsometryAverage_le ρ (y - x)) le_rfl
      _ = _ := by rw [norm_sub_rev]; ring
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hx : ‖x‖ ≤ c * ‖S x‖ + 2 * c * ‖x - y‖ := by
    have htri := norm_le_norm_sub_add x y
    have hmul := mul_le_mul_of_nonneg_left hSy hc0
    have he := mul_le_mul_of_nonneg_right hc (norm_nonneg (x - y))
    change ‖y‖ ≤ c * ‖S y‖ at hy
    nlinarith
  have hright : 0 ≤ c * ‖S x‖ + 2 * c * ‖x - y‖ := by positivity
  have hsq := (sq_le_sq₀ (norm_nonneg x) hright).mpr hx
  have htwo : (c * ‖S x‖ + 2 * c * ‖x - y‖) ^ 2 ≤
      2 * c ^ 2 * ‖S x‖ ^ 2 + 8 * c ^ 2 * ‖x - y‖ ^ 2 := by
    nlinarith [sq_nonneg (c * ‖S x‖ - 2 * c * ‖x - y‖)]
  exact hsq.trans htwo

end KLS
end

#print axioms KLS.norm_sq_le_of_near_average_recovery
