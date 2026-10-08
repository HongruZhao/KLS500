import SpectralReductionLongBlock
import SpectralReductionProjectionRecovery

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

theorem norm_sq_le_triple_choose_prefixAverage {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d q : ℕ) (hq : q = 3 * d)
    (ρ : Equiv.Perm (Fin (d + q)) →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (hA : ∀ σ : Equiv.Perm (Fin d), ρ (prefixFinPermHom (by omega : d ≤ d + q) σ) x = x)
    (hC : ∀ σ : Equiv.Perm (Fin q), ρ (suffixFinPermHom d q σ) x = x) :
    ‖x‖^2 ≤ ((3 * d).choose d : ℝ) * ‖finiteIsometryAverage
      (ρ.comp (prefixFinPermHom (by omega : 2 * d ≤ d + q))) x‖^2 := by
  have hA' (σ : Equiv.Perm (finPrefixSet d (d + q))) : ρ (Equiv.Perm.ofSubtype σ) x = x := by
    obtain ⟨τ, rfl⟩ := (finPrefixSetEquiv (by omega : d ≤ d + q)).permCongrHom.surjective σ
    rw [ofSubtype_finPrefixSetEquiv]
    exact hA τ
  have hC' (σ : Equiv.Perm {i : Fin (d + q) // i ∉ finPrefixSet d (d + q)}) :
      ρ (Equiv.Perm.ofSubtype σ) x = x := by
    obtain ⟨τ, rfl⟩ := (finPrefixComplementEquiv d q).permCongrHom.surjective σ
    exact hC τ
  have hn := norm_sq_le_triple_choose_blockAverage ρ x Finset.univ
    (finPrefixSet d (d + q)) (finPrefixSet (2 * d) (d + q)) d
    (by simp; omega) (finPrefixSet_card (by omega)) (finPrefixSet_card (by omega))
    (finPrefixSet_mono (by omega)) (Finset.subset_univ _) (fixed_of_two_block_symmetry ρ x _ hA' hC')
  rwa [finitePrefixSet_average (by omega)] at hn


variable {n : ℕ} {φ : Space n → ℝ} {ι : Type*} [Fintype ι]
  {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem norm_sq_weightedL2BlockTaylor_symmetrized_triple_choose_le (r d q : ℕ) (hq : q + 1 = 3 * d)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2BlockTaylor φ r d q (finiteIsometryAverage
      (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g)‖^2 ≤
      ((3 * d).choose d : ℝ) * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1))
        (weightedL2BlockTaylor φ r d q (finiteIsometryAverage
          (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g))‖^2 := by
  apply norm_sq_le_triple_choose_prefixAverage d (q + 1) hq
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



end KLS.ConstantReduction
end
