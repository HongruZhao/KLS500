import SpectralReductionRankTaylor

/-! A freely chosen positive Young parameter in genuine block recovery. -/
open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

theorem add_sq_le_young (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (a + b) ^ 2 ≤ (1 + ε) * a ^ 2 + (1 + ε⁻¹) * b ^ 2 := by
  have hid : ε * ((1 + ε) * a ^ 2 + (1 + ε⁻¹) * b ^ 2 - (a+b)^2) = (ε*a-b)^2 := by
    field_simp
    ring
  have hh := sq_nonneg (ε*a-b)
  rw [← hid] at hh
  nlinarith

theorem norm_sq_le_of_near_average_recovery_young {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Group G] [Fintype G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E) {c : ℝ} (hc : 0 ≤ c)
    {ε : ℝ} (hε : 0 < ε)
    (hy : ‖y‖ ≤ c * ‖finiteIsometryAverage ρ y‖) :
    ‖x‖ ^ 2 ≤ (1 + ε) * c ^ 2 * ‖finiteIsometryAverage ρ x‖ ^ 2 +
      (1 + ε⁻¹) * (1 + c) ^ 2 * ‖x - y‖ ^ 2 := by
  let S := finiteIsometryAverageLinearMap ρ
  have hSy : ‖S y‖ ≤ ‖S x‖ + ‖x - y‖ := by
    calc
      _ ≤ ‖S y - S x‖ + ‖S x‖ := norm_le_norm_sub_add _ _
      _ = ‖S (y - x)‖ + ‖S x‖ := by rw [map_sub]
      _ ≤ ‖y - x‖ + ‖S x‖ := add_le_add (norm_finiteIsometryAverage_le ρ (y - x)) le_rfl
      _ = _ := by rw [norm_sub_rev]; ring
  have hx : ‖x‖ ≤ c * ‖S x‖ + (1 + c) * ‖x - y‖ := by
    have htri := norm_le_norm_sub_add x y
    have hmul := mul_le_mul_of_nonneg_left hSy hc
    change ‖y‖ ≤ c * ‖S y‖ at hy
    nlinarith
  have hright : 0 ≤ c * ‖S x‖ + (1 + c) * ‖x - y‖ := by positivity
  have hsq := (sq_le_sq₀ (norm_nonneg x) hright).mpr hx
  have htwo : (c * ‖S x‖ + (1 + c) * ‖x - y‖) ^ 2 ≤
      (1 + ε) * c ^ 2 * ‖S x‖ ^ 2 + (1 + ε⁻¹) * (1 + c) ^ 2 * ‖x - y‖ ^ 2 := by
    convert add_sq_le_young (c * ‖S x‖) ((1 + c) * ‖x-y‖) hε using 1 <;> ring
  exact hsq.trans htwo

variable {n : ℕ} {φ : Space n → ℝ} {ι : Type*} [Fintype ι]
  {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem weightedL2TaylorTensor_norm_sq_le_partial_and_error_young
    {β : ℕ → ℝ} (hβ : WeightedCoordinateTaylorCoefficientBound φ β)
    {ε : ℝ} (hε : 0 < ε)
    (r d q : ℕ) (hd : 1 ≤ d) (hq : q + 1 = 2 * d)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2TaylorTensor φ d g‖ ^ 2 ≤
      (1 + ε) * ((2 * d).choose d : ℝ) ^ 2 * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1))
        (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
      (1 + ε⁻¹) * (1 + ((2 * d).choose d : ℝ)) ^ 2 * β d * ‖g - finiteIsometryAverage
        (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g‖ ^ 2 := by
  let ρ := realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1)
  let S := finiteIsometryAverage (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g
  have hc : (0 : ℝ) ≤ ((2 * d).choose d : ℝ) := Nat.cast_nonneg _
  have hy := norm_weightedL2BlockTaylor_symmetrized_choose_le hφ hκ hlower r d q hq g
  have hrec := norm_sq_le_of_near_average_recovery_young ρ
    (weightedL2BlockTaylor φ r d q g) (weightedL2BlockTaylor φ r d q S) hc hε hy
  rw [norm_weightedL2BlockTaylor] at hrec
  have hdiff := weightedL2BlockTaylor_sub_norm_sq_le_coefficient hφ hκ hlower hβ r d q hd g S
  calc
    _ ≤ (1 + ε) * ((2 * d).choose d : ℝ) ^ 2 * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        (1 + ε⁻¹) * (1 + ((2 * d).choose d : ℝ)) ^ 2 * ‖weightedL2BlockTaylor φ r d q g - weightedL2BlockTaylor φ r d q S‖ ^ 2 := hrec
    _ ≤ (1 + ε) * ((2 * d).choose d : ℝ) ^ 2 * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        (1 + ε⁻¹) * (1 + ((2 * d).choose d : ℝ)) ^ 2 * (β d * ‖g - S‖ ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiff (by positivity))
    _ = _ := by ring


end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedL2TaylorTensor_norm_sq_le_partial_and_error_young
