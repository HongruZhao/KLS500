import KLS.WeightedIterationTaylorBlockRecursion

/-! Repeated partial symmetrization of the actual Taylor tensors, on one
fixed coordinate carrier. This is the literal product identity BKL (56). -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

theorem finiteIsometryAverage_eq_of_forall_fixed {E G : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [Group G] [Fintype G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (hx : ∀ g, ρ g x = x) :
    finiteIsometryAverage ρ x = x := by
  unfold finiteIsometryAverage
  simp_rw [hx]
  have hN : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem realTensorPrefixAction_apply (n p : ℕ) (ι : Type*) [Fintype ι]
    {m : ℕ} (h : m ≤ p) (σ : Equiv.Perm (Fin m))
    (T : EuclideanSpace ℝ ((Fin p → Fin n) × ι)) (a : Fin p → Fin n) (i : ι) :
    realTensorPrefixAction n p ι h σ T (a, i) = T (a ∘ prefixFinPermHom h σ, i) := rfl

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)

theorem weightedIterationBlockTaylor_taylor_fixed (r d q m : ℕ) (h : d + q = m)
    (σ : Equiv.Perm (Fin d)) :
    realTensorPrefixAction n (m + 1) (WeightedIterationIndex n ι r) (by omega : d ≤ m + 1) σ
      (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r d q m h) =
        weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r d q m h := by
  apply PiLp.ext
  rintro ⟨a, i⟩
  rw [realTensorPrefixAction_apply, weightedIterationBlockTaylor_apply, weightedIterationBlockTaylor_apply,
    finBlockTuple_prefix_permutation a (le_refl d),
    finBlockTuple_suffix_permutation a _ _ (le_refl d)]
  exact exponentialTiltCoordinateTaylor_comp_perm (hφ.of_le (by simp)) hκ hlower
    (Lp.memLp _) d (finBlockTuple a 0 d (by omega)) σ

variable (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
  (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))

include hF hV hL

/-- Exact repeated version of Corollary 3.7. The actual normalization product
includes every intermediate step and also handles zero scales. -/
theorem weightedIterationBlockTaylor_repeated (r d q m : ℕ) (h : d + q = m)
    (hd : d ≠ 0) :
    finiteIsometryAverage
      (realTensorPrefixAction n (m + 1) (WeightedIterationIndex n ι r) (by omega : m ≤ m + 1))
      (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r d q m h) =
      (∏ j ∈ Finset.range q, weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + j))) •
          weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r m 0 m (by omega) := by
  induction q generalizing d with
  | zero =>
    have he : d = m := by omega
    subst d
    simp only [Finset.range_zero, Finset.prod_empty, one_smul]
    exact finiteIsometryAverage_eq_of_forall_fixed _ _
      (weightedIterationBlockTaylor_taylor_fixed hφ hκ hlower U r m 0 m h)
  | succ q ih =>
    let S := finiteIsometryAverageLinearMap
      (realTensorPrefixAction n (m + 1) (WeightedIterationIndex n ι r) (by omega : m ≤ m + 1))
    change S _ = _
    calc
      _ = S (finiteIsometryAverage
          (realTensorPrefixAction n (m + 1) (WeightedIterationIndex n ι r) (by omega : d + 1 ≤ m + 1))
          (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r d (q + 1) m h)) := by
        exact (realTensorPrefixAverage_absorb n (m + 1) (WeightedIterationIndex n ι r)
          (by omega : d + 1 ≤ m) (by omega : m ≤ m + 1) _).symm
      _ = S (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + q)) •
            weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r (d + 1) q m (by omega)) := by
        rw [weightedIterationBlockTaylor_step hφ hκ hlower U F hF hV hL r d q m h hd]
      _ = weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + q)) •
            S (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r (d + 1) q m (by omega)) :=
        S.map_smul _ _
      _ = weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + q)) •
            ((∏ j ∈ Finset.range q, weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
              (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + j))) •
                weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r m 0 m (by omega)) := by
        rw [show S (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r (d + 1) q m (by omega)) = _
          from ih (d + 1) (by omega) (by omega)]
      _ = _ := by rw [smul_smul, Finset.prod_range_succ, mul_comm]

end KLS
end

#print axioms KLS.weightedIterationBlockTaylor_taylor_fixed
#print axioms KLS.weightedIterationBlockTaylor_repeated
