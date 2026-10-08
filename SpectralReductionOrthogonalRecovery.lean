import SpectralReductionYoungRecovery
import FiniteAverageHilbertVariance

/-! Actual block Taylor averaging is an orthogonal projection in the tensor
Hilbert space. Its Pythagorean identity improves the perturbation constant. -/
open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

theorem norm_sq_le_of_orthogonal_recovery_young {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Group G] [Fintype G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E) {c : ℝ} (hc : 0 ≤ c)
    {ε : ℝ} (hε : 0 < ε)
    (hy : ‖y‖ ≤ c * ‖finiteIsometryAverage ρ y‖)
    (horth : inner ℝ x y = ‖y‖ ^ 2) :
    ‖x‖ ^ 2 ≤ (1 + ε) * c ^ 2 * ‖finiteIsometryAverage ρ x‖ ^ 2 +
      (1 + (1 + ε⁻¹) * c ^ 2) * ‖x - y‖ ^ 2 := by
  let P := finiteIsometryAverageLinearMap ρ
  have hPy : ‖P y‖ ≤ ‖P x‖ + ‖x-y‖ := by
    calc
      _ ≤ ‖P y - P x‖ + ‖P x‖ := norm_le_norm_sub_add _ _
      _ = ‖P (y-x)‖ + ‖P x‖ := by rw [map_sub]
      _ ≤ ‖y-x‖ + ‖P x‖ := add_le_add (norm_finiteIsometryAverage_le ρ (y-x)) le_rfl
      _ = _ := by rw [norm_sub_rev]; ring
  have hysq : ‖y‖^2 ≤ c^2 * ‖P y‖^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg y) (mul_nonneg hc (norm_nonneg (P y)))).mpr hy
    nlinarith
  have hPysq := (sq_le_sq₀ (norm_nonneg (P y)) (by positivity : 0 ≤ ‖P x‖+‖x-y‖)).mpr hPy
  have hbound := hysq.trans (mul_le_mul_of_nonneg_left
    (hPysq.trans (add_sq_le_young ‖P x‖ ‖x-y‖ hε)) (sq_nonneg c))
  have hnorm : ‖x‖^2 = ‖y‖^2 + ‖x-y‖^2 := by rw [norm_sub_sq_real, horth]; ring
  change ‖x‖^2 ≤ (1+ε)*c^2*‖P x‖^2 + (1+(1+ε⁻¹)*c^2)*‖x-y‖^2
  nlinarith

variable {n : ℕ} {φ : Space n → ℝ} {ι : Type*} [Fintype ι]
  {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem weightedL2BlockTaylor_suffix_average (r d q : ℕ)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r+q))) :
    weightedL2BlockTaylor φ r d q (finiteIsometryAverage
      (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g) =
    finiteIsometryAverage
      ((realCoordinatePermutationAction n (d+q+1) (WeightedIterationIndex n ι r)).comp
        (suffixFinPermHom d (q+1))) (weightedL2BlockTaylor φ r d q g) := by
  let L : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r+q)) →ₗ[ℝ]
      EuclideanSpace ℝ ((Fin (d+q+1) → Fin n) × WeightedIterationIndex n ι r) :=
    { toFun := weightedL2BlockTaylor φ r d q
      map_add' := by intro x y; simp [weightedL2BlockTaylor, weightedL2TaylorTensor_add hφ hκ hlower]
      map_smul' := by intro c x; simp [weightedL2BlockTaylor, weightedL2TaylorTensor_smul hφ hκ hlower] }
  change L (finiteIsometryAverage _ g) = finiteIsometryAverage _ (L g)
  rw [finiteIsometryAverage, finiteIsometryAverage, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact (weightedL2BlockTaylor_suffix_action r d q g σ).symm

theorem weightedL2TaylorTensor_norm_sq_le_partial_and_error_orthogonalYoung
    {β : ℕ → ℝ} (hβ : WeightedCoordinateTaylorCoefficientBound φ β)
    {ε : ℝ} (hε : 0 < ε)
    (r d q : ℕ) (hd : 1 ≤ d) (hq : q + 1 = 2 * d)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2TaylorTensor φ d g‖ ^ 2 ≤
      (1 + ε) * ((2 * d).choose d : ℝ) ^ 2 * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1))
        (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
      (1 + (1 + ε⁻¹) * ((2 * d).choose d : ℝ) ^ 2) * β d * ‖g - finiteIsometryAverage
        (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g‖ ^ 2 := by
  let ρ := realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1)
  let S := finiteIsometryAverage (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g
  have hc : (0 : ℝ) ≤ ((2 * d).choose d : ℝ) := Nat.cast_nonneg _
  have hy := norm_weightedL2BlockTaylor_symmetrized_choose_le hφ hκ hlower r d q hq g
  have horth : inner ℝ (weightedL2BlockTaylor φ r d q g) (weightedL2BlockTaylor φ r d q S) =
      ‖weightedL2BlockTaylor φ r d q S‖^2 := by
    change inner ℝ (weightedL2BlockTaylor φ r d q g)
      (weightedL2BlockTaylor φ r d q (finiteIsometryAverage _ g)) = _
    rw [weightedL2BlockTaylor_suffix_average hφ hκ hlower]
    exact inner_finiteIsometryAverage_self _ _
  have hrec := norm_sq_le_of_orthogonal_recovery_young ρ
    (weightedL2BlockTaylor φ r d q g) (weightedL2BlockTaylor φ r d q S) hc hε hy horth
  rw [norm_weightedL2BlockTaylor] at hrec
  have hdiff := weightedL2BlockTaylor_sub_norm_sq_le_coefficient hφ hκ hlower hβ r d q hd g S
  calc
    _ ≤ (1 + ε) * ((2 * d).choose d : ℝ) ^ 2 * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        (1 + (1 + ε⁻¹) * ((2 * d).choose d : ℝ) ^ 2) * ‖weightedL2BlockTaylor φ r d q g - weightedL2BlockTaylor φ r d q S‖ ^ 2 := hrec
    _ ≤ (1 + ε) * ((2 * d).choose d : ℝ) ^ 2 * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        (1 + (1 + ε⁻¹) * ((2 * d).choose d : ℝ) ^ 2) * (β d * ‖g - S‖ ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiff (by positivity))
    _ = _ := by ring


end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedL2TaylorTensor_norm_sq_le_partial_and_error_orthogonalYoung
