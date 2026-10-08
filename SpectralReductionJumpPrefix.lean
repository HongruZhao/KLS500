import SpectralReductionJumpBlock
import SpectralReductionLongRecovery

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

def jumpRecoverySquared (d k q : ℕ) : ℝ :=
  (q.choose k : ℝ)*((d+k).choose d : ℝ)/((q-d).choose k : ℝ)

theorem jumpRecoverySquared_gt_one {d k q : ℕ} (hd : 1≤d) (hk : 1≤k) (hq : d+k≤q) :
    1<jumpRecoverySquared d k q := by
  have hden : (0 : ℝ)<((q-d).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : k≤q-d)
  have hm : ((q-d).choose k : ℝ)≤(q.choose k : ℝ) := by
    exact_mod_cast Nat.choose_le_choose k (Nat.sub_le _ _)
  have hb : (2 : ℝ)≤((d+k).choose d : ℝ) := by
    have hh := Nat.choose_le_choose d (by omega : d+1≤d+k)
    rw [Nat.choose_succ_self_right] at hh
    exact_mod_cast (show 2≤(d+k).choose d by omega)
  have hh : ((d+k).choose d : ℝ)≤jumpRecoverySquared d k q := by
    unfold jumpRecoverySquared
    apply (le_div_iff₀ hden).mpr
    have hp := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg ((d+k).choose d))
    simpa only [mul_comm] using hp
  linarith

theorem norm_sq_le_jump_coefficient_prefixAverage {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d k q : ℕ) (hq : d+k≤q)
    (ρ : Equiv.Perm (Fin (d+q)) →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (hA : ∀ σ : Equiv.Perm (Fin d), ρ (prefixFinPermHom (by omega : d≤d+q) σ) x=x)
    (hC : ∀ σ : Equiv.Perm (Fin q), ρ (suffixFinPermHom d q σ) x=x) :
    ‖x‖^2≤jumpRecoverySquared d k q*‖finiteIsometryAverage
      (ρ.comp (prefixFinPermHom (by omega : d+k≤d+q))) x‖^2 := by
  have hA' (σ : Equiv.Perm (finPrefixSet d (d+q))) : ρ (Equiv.Perm.ofSubtype σ) x=x := by
    obtain ⟨τ,rfl⟩ := (finPrefixSetEquiv (by omega : d≤d+q)).permCongrHom.surjective σ
    rw [ofSubtype_finPrefixSetEquiv]
    exact hA τ
  have hC' (σ : Equiv.Perm {i : Fin (d+q) // i∉finPrefixSet d (d+q)}) :
      ρ (Equiv.Perm.ofSubtype σ) x=x := by
    obtain ⟨τ,rfl⟩ := (finPrefixComplementEquiv d q).permCongrHom.surjective σ
    exact hC τ
  have hn := norm_sq_mul_choose_le_jump_blockAverage ρ x Finset.univ
    (finPrefixSet d (d+q)) (finPrefixSet (d+k) (d+q)) d k (q-d)
    (by simp; omega) (by omega) (finPrefixSet_card (by omega)) (finPrefixSet_card (by omega))
    (finPrefixSet_mono (by omega)) (Finset.subset_univ _) (fixed_of_two_block_symmetry ρ x _ hA' hC')
  rw [finitePrefixSet_average (by omega), show d+(q-d)=q by omega] at hn
  have hden : (0 : ℝ)<((q-d).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : k≤q-d)
  unfold jumpRecoverySquared
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hn)

variable {n : ℕ} {φ : Space n → ℝ} {ι : Type*} [Fintype ι]
  {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem norm_sq_weightedL2BlockTaylor_symmetrized_jump_le (r d k q : ℕ) (hq : d+k≤q+1)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2BlockTaylor φ r d q (finiteIsometryAverage
      (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g)‖^2 ≤
      jumpRecoverySquared d k (q+1) * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : d+k ≤ d + q + 1))
        (weightedL2BlockTaylor φ r d q (finiteIsometryAverage
          (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g))‖^2 := by
  apply norm_sq_le_jump_coefficient_prefixAverage d k (q+1) hq
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
