import KLS.FinitePrefixBlockRecovery

/-! The actual Taylor tensor of a symmetrized weighted L2 family has the two
literal block symmetries required by BKL Lemma 2.2. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
set_option backward.isDefEq.respectTransparency false

theorem realCoordinatePermutationAction_apply (n p : ℕ) (ι : Type*) [Fintype ι]
    (σ : Equiv.Perm (Fin p)) (T : EuclideanSpace ℝ ((Fin p → Fin n) × ι))
    (a : Fin p → Fin n) (i : ι) :
    realCoordinatePermutationAction n p ι σ T (a, i) = T (a ∘ σ, i) := rfl

theorem finBlockTuple_suffix_left {J : Type*} (d q : ℕ)
    (a : Fin (d + q) → J) (σ : Equiv.Perm (Fin q)) :
    finBlockTuple (a ∘ suffixFinPermHom d q σ) 0 d (by omega) = finBlockTuple a 0 d (by omega) := by
  funext j
  simp only [finBlockTuple, Function.comp_apply, Nat.zero_add]
  change a (suffixFinPermHom d q σ (Fin.castAdd q j)) = a (Fin.castAdd q j)
  rw [suffixFinPermHom_apply_castAdd]

theorem finBlockTuple_suffix_right {J : Type*} (d q : ℕ)
    (a : Fin (d + q) → J) (σ : Equiv.Perm (Fin q)) :
    finBlockTuple (a ∘ suffixFinPermHom d q σ) d q (by omega) = finBlockTuple a d q (by omega) ∘ σ := by
  funext j
  change a (suffixFinPermHom d q σ (Fin.natAdd d j)) = a (Fin.natAdd d (σ j))
  rw [suffixFinPermHom_apply_natAdd]

theorem weightedGradientPermutationAction_apply {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (ι : Type*) [Fintype ι] (r q : ℕ)
    (σ : Equiv.Perm (Fin (q + 1)))
    (g : CenteredL2.Family μ (Fin n × WeightedIterationIndex n ι (r + q)))
    (a : Fin (q + 1) → Fin n) (i : WeightedIterationIndex n ι r) :
    weightedGradientPermutationAction μ n ι r q σ g ((tensorPrefixEquiv n ι r (q + 1)).symm (a, i)) =
      g ((tensorPrefixEquiv n ι r (q + 1)).symm (a ∘ σ, i)) := by
  change g ((tensorPrefixPermutationHom n ι r (q + 1) σ).symm
    ((tensorPrefixEquiv n ι r (q + 1)).symm (a, i))) = _
  have he : (tensorPrefixPermutationHom n ι r (q + 1) σ).symm =
      tensorPrefixPermutationHom n ι r (q + 1) σ.symm := (map_inv _ σ).symm
  rw [he, tensorPrefixPermutationHom_apply, Equiv.apply_symm_apply]
  rfl

variable {n : ℕ} {φ : Space n → ℝ} {ι : Type*} [Fintype ι]

def weightedL2BlockTaylor (φ : Space n → ℝ) (r d q : ℕ)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    EuclideanSpace ℝ ((Fin (d + q + 1) → Fin n) × WeightedIterationIndex n ι r) :=
  finiteScalarReindex (mergeTaylorBlockEquiv n ι r d q (d + q) rfl) (weightedL2TaylorTensor φ d g)

@[simp] theorem weightedL2BlockTaylor_apply (r d q : ℕ)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q)))
    (a : Fin (d + q + 1) → Fin n) (i : WeightedIterationIndex n ι r) :
    weightedL2BlockTaylor φ r d q g (a, i) =
      exponentialTiltCoordinateTaylor φ
        (g ((tensorPrefixEquiv n ι r (q + 1)).symm (finBlockTuple a d (q + 1) (by omega), i)))
          d (finBlockTuple a 0 d (by omega)) := by
  rw [weightedL2BlockTaylor, finiteScalarReindex_apply, mergeTaylorBlockEquiv_symm_apply]
  rfl

theorem norm_weightedL2BlockTaylor (r d q : ℕ)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2BlockTaylor φ r d q g‖ = ‖weightedL2TaylorTensor φ d g‖ := by
  rw [weightedL2BlockTaylor, LinearIsometryEquiv.norm_map]

theorem weightedL2BlockTaylor_suffix_action (r d q : ℕ)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q)))
    (σ : Equiv.Perm (Fin (q + 1))) :
    realCoordinatePermutationAction n (d + q + 1) (WeightedIterationIndex n ι r)
      (suffixFinPermHom d (q + 1) σ) (weightedL2BlockTaylor φ r d q g) =
        weightedL2BlockTaylor φ r d q (weightedGradientPermutationAction (potentialMeasure φ) n ι r q σ g) := by
  apply PiLp.ext
  rintro ⟨a, i⟩
  have hl := finBlockTuple_suffix_left d (q + 1) a σ
  have hr := finBlockTuple_suffix_right d (q + 1) a σ
  have hg := weightedGradientPermutationAction_apply (potentialMeasure φ) n ι r q σ g
    (finBlockTuple a d (q + 1) (by omega)) i
  rw [realCoordinatePermutationAction_apply, weightedL2BlockTaylor_apply, weightedL2BlockTaylor_apply]
  calc
    _ = exponentialTiltCoordinateTaylor φ
        (g ((tensorPrefixEquiv n ι r (q + 1)).symm
          (finBlockTuple a d (q + 1) (by omega) ∘ σ, i))) d (finBlockTuple a 0 d (by omega)) :=
      congrArg₂ (fun b c => exponentialTiltCoordinateTaylor φ
        (g ((tensorPrefixEquiv n ι r (q + 1)).symm (b, i))) d c) hr hl
    _ = _ := congrArg (fun f : Lp ℝ 2 (potentialMeasure φ) =>
      exponentialTiltCoordinateTaylor φ f d (finBlockTuple a 0 d (by omega))) hg.symm

variable {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem weightedL2BlockTaylor_taylor_fixed (r d q : ℕ)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q)))
    (σ : Equiv.Perm (Fin d)) :
    realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : d ≤ d + q + 1) σ
      (weightedL2BlockTaylor φ r d q g) = weightedL2BlockTaylor φ r d q g := by
  apply PiLp.ext
  rintro ⟨a, i⟩
  rw [realTensorPrefixAction_apply, weightedL2BlockTaylor_apply, weightedL2BlockTaylor_apply,
    finBlockTuple_prefix_permutation a (le_refl d), finBlockTuple_suffix_permutation a _ _ (le_refl d)]
  exact exponentialTiltCoordinateTaylor_comp_perm hφ hκ hlower (Lp.memLp _) d
    (finBlockTuple a 0 d (by omega)) σ

/-- The actual Taylor tensor of the actual derivative-prefix average meets
both block symmetry conditions. The output average moves exactly 2d slots. -/
theorem norm_weightedL2BlockTaylor_symmetrized_le (r d q : ℕ) (hq : q + 1 = 2 * d)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2BlockTaylor φ r d q (finiteIsometryAverage
      (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g)‖ ≤
      (4 : ℝ) ^ d * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1))
        (weightedL2BlockTaylor φ r d q (finiteIsometryAverage
          (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g))‖ := by
  apply norm_le_four_pow_mul_prefixAverage d (q + 1) hq
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

end KLS
end

#print axioms KLS.weightedL2BlockTaylor_suffix_action
#print axioms KLS.norm_weightedL2BlockTaylor_symmetrized_le
