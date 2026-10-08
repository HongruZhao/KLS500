import KLS.WeightedTaylorBlockRecovery

/-! Exact central-binomial block recovery and an uninflated perturbation
estimate. All tensors and subgroup symmetries are the actual BKL objects. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

theorem norm_le_choose_mul_prefixAverage {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d q : ℕ) (hq : q = 2 * d)
    (ρ : Equiv.Perm (Fin (d + q)) →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (hA : ∀ σ : Equiv.Perm (Fin d), ρ (prefixFinPermHom (by omega : d ≤ d + q) σ) x = x)
    (hC : ∀ σ : Equiv.Perm (Fin q), ρ (suffixFinPermHom d q σ) x = x) :
    ‖x‖ ≤ ((2 * d).choose d : ℝ) * ‖finiteIsometryAverage
      (ρ.comp (prefixFinPermHom (by omega : 2 * d ≤ d + q))) x‖ := by
  have hA' (σ : Equiv.Perm (finPrefixSet d (d + q))) : ρ (Equiv.Perm.ofSubtype σ) x = x := by
    obtain ⟨τ, rfl⟩ := (finPrefixSetEquiv (by omega : d ≤ d + q)).permCongrHom.surjective σ
    rw [ofSubtype_finPrefixSetEquiv]
    exact hA τ
  have hC' (σ : Equiv.Perm {i : Fin (d + q) // i ∉ finPrefixSet d (d + q)}) :
      ρ (Equiv.Perm.ofSubtype σ) x = x := by
    obtain ⟨τ, rfl⟩ := (finPrefixComplementEquiv d q).permCongrHom.surjective σ
    exact hC τ
  have hn := norm_le_choose_mul_blockAverage ρ x Finset.univ
    (finPrefixSet d (d + q)) (finPrefixSet (2 * d) (d + q)) d
    (by simp; omega) (finPrefixSet_card (by omega)) (finPrefixSet_card (by omega))
    (finPrefixSet_mono (by omega)) (Finset.subset_univ _) (fixed_of_two_block_symmetry ρ x _ hA' hC')
  rwa [finitePrefixSet_average (by omega)] at hn


theorem norm_sq_le_of_near_average_recovery_exact {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Group G] [Fintype G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E) {c : ℝ} (hc : 0 ≤ c)
    (hy : ‖y‖ ≤ c * ‖finiteIsometryAverage ρ y‖) :
    ‖x‖ ^ 2 ≤ 2 * c ^ 2 * ‖finiteIsometryAverage ρ x‖ ^ 2 +
      2 * (1 + c) ^ 2 * ‖x - y‖ ^ 2 := by
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
      2 * c ^ 2 * ‖S x‖ ^ 2 + 2 * (1 + c) ^ 2 * ‖x - y‖ ^ 2 := by
    nlinarith [sq_nonneg (c * ‖S x‖ - (1 + c) * ‖x - y‖)]
  exact hsq.trans htwo

variable {n : ℕ} {φ : Space n → ℝ} {ι : Type*} [Fintype ι]
  {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem norm_weightedL2BlockTaylor_symmetrized_choose_le (r d q : ℕ) (hq : q + 1 = 2 * d)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2BlockTaylor φ r d q (finiteIsometryAverage
      (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g)‖ ≤
      ((2 * d).choose d : ℝ) * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1))
        (weightedL2BlockTaylor φ r d q (finiteIsometryAverage
          (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g))‖ := by
  apply norm_le_choose_mul_prefixAverage d (q + 1) hq
    (realCoordinatePermutationAction n (d + q + 1) (WeightedIterationIndex n ι r))
  · intro σ
    exact weightedL2BlockTaylor_taylor_fixed hφ hκ hlower r d q _ σ
  · intro σ
    calc
      _ = weightedL2BlockTaylor φ r d q
          (weightedGradientPermutationAction (potentialMeasure φ) n ι r q σ
            (finiteIsometryAverage (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g)) :=
        weightedL2BlockTaylor_suffix_action r d q _ σ
      _ = _ := congrArg (weightedL2BlockTaylor φ r d q)
        (finiteIsometryAverage_fixed (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g σ)


theorem weightedL2TaylorTensor_norm_sq_le_partial_and_error_choose
    {R : ℝ} (hR : WeightedCoordinateTaylorBound φ R)
    (r d q : ℕ) (hd : 1 ≤ d) (hq : q + 1 = 2 * d)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2TaylorTensor φ d g‖ ^ 2 ≤
      2 * ((2 * d).choose d : ℝ) ^ 2 * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1))
        (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
      2 * (1 + ((2 * d).choose d : ℝ)) ^ 2 * R ^ (2 * d) * ‖g - finiteIsometryAverage
        (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g‖ ^ 2 := by
  let ρ := realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1)
  let S := finiteIsometryAverage (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g
  have hc : (0 : ℝ) ≤ ((2 * d).choose d : ℝ) := Nat.cast_nonneg _
  have hy := norm_weightedL2BlockTaylor_symmetrized_choose_le hφ hκ hlower r d q hq g
  have hrec := norm_sq_le_of_near_average_recovery_exact ρ
    (weightedL2BlockTaylor φ r d q g) (weightedL2BlockTaylor φ r d q S) hc hy
  rw [norm_weightedL2BlockTaylor] at hrec
  have hdiff := weightedL2BlockTaylor_sub_norm_sq_le hφ hκ hlower hR r d q hd g S
  calc
    _ ≤ 2 * ((2 * d).choose d : ℝ) ^ 2 * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        2 * (1 + ((2 * d).choose d : ℝ)) ^ 2 * ‖weightedL2BlockTaylor φ r d q g - weightedL2BlockTaylor φ r d q S‖ ^ 2 := hrec
    _ ≤ 2 * ((2 * d).choose d : ℝ) ^ 2 * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        2 * (1 + ((2 * d).choose d : ℝ)) ^ 2 * (R ^ (2 * d) * ‖g - S‖ ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiff (by positivity))
    _ = _ := by ring


end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.norm_le_choose_mul_prefixAverage
#print axioms KLS.ConstantReduction.norm_sq_le_of_near_average_recovery_exact
#print axioms KLS.ConstantReduction.norm_weightedL2BlockTaylor_symmetrized_choose_le
#print axioms KLS.ConstantReduction.weightedL2TaylorTensor_norm_sq_le_partial_and_error_choose
