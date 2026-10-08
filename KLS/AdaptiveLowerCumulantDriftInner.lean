import KLS.AdaptiveCumulantDrift

/-! Identification of the finite whitening sum with the inverse-covariance contraction in (72). -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {n m : ℕ} {μ : Measure (Space n)}

/-- Riesz vector of the actual cumulant with all listed slots fixed. -/
def listCumulantVector (μ : Measure (Space n)) (vs : List (Space n)) : Space n :=
  (InnerProductSpace.toDual ℝ (Space n)).symm (listCumulantHead μ vs)

theorem listCumulant_cons_eq_inner (v : Space n) (vs : List (Space n)) :
    listCumulant μ (v :: vs) = inner ℝ (listCumulantVector μ vs) v := by
  rw [listCumulant_cons]
  exact InnerProductSpace.toDual_symm_apply.symm

namespace AdaptiveLocalization
open KLS.StandardLocalization
variable [IsProbabilityMeasure μ]

theorem sum_inner_inverseSqrt_eq_inverseCovariance (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) (u v : Space n) :
    (∑ k : Fin n, inner ℝ u (inverseSqrtDirection μ z k) *
      inner ℝ v (inverseSqrtDirection μ z k)) =
      inner ℝ u (matrixAction (inverseCovariance μ (decodeState z)) v) := by
  have hi (x : Space n) (k : Fin n) : inner ℝ x (inverseSqrtDirection μ z k) =
      ((inverseSqrtCovariance μ (decodeState z)).transpose *ᵥ (fun i => x i)) k := by
    rw [real_inner_comm, inner_inverseSqrtDirection]
    rfl
  simp_rw [hi]
  change ((inverseSqrtCovariance μ (decodeState z)).transpose *ᵥ (fun i => u i)) ⬝ᵥ
    ((inverseSqrtCovariance μ (decodeState z)).transpose *ᵥ (fun i => v i)) = _
  rw [← dotProduct_gram_mulVec, inverseSqrtCovariance_mul_transpose hμ hfull]
  rw [inner_eq_coordinate_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Literal vector form of the paper's L_m, including A^{-1} and the representative
subset containing the distinguished first argument. -/
theorem lowerCumulantDrift_eq_inverseCovariance_inner (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (h : Fin m → Space n)
    (z : Fin (n+n*n) → ℝ) (i₀ : Fin m) :
    lowerCumulantDrift μ h z i₀ = ∑ S : Finset (Fin m),
      if i₀ ∈ S ∧ 2 ≤ S.card ∧ S.card ≤ m-2 then
        inner ℝ (listCumulantVector (law μ (decodeState z).1 (decodeState z).2)
          (maskedDirections h (fun i => decide (i ∈ S))))
          (matrixAction (inverseCovariance μ (decodeState z))
            (listCumulantVector (law μ (decodeState z).1 (decodeState z).2)
              (maskedDirections h (fun i => decide (i ∈ Sᶜ))))) else 0 := by
  unfold lowerCumulantDrift
  apply Finset.sum_congr rfl
  intro S _
  split_ifs
  · simp only [listCumulant_cons_eq_inner]
    exact sum_inner_inverseSqrt_eq_inverseCovariance hμ hfull z _ _
  · rfl

/-- The actual tensors appearing in every retained lower term have orders 3,...,m-1. -/
theorem lowerCumulantDrift_orders (h : Fin m → Space n) (S : Finset (Fin m))
    (hS : 2 ≤ S.card ∧ S.card ≤ m-2) :
    (3 ≤ (maskedDirections h (fun i => decide (i ∈ S))).length+1 ∧
      (maskedDirections h (fun i => decide (i ∈ S))).length+1 ≤ m-1) ∧
    (3 ≤ (maskedDirections h (fun i => decide (i ∈ Sᶜ))).length+1 ∧
      (maskedDirections h (fun i => decide (i ∈ Sᶜ))).length+1 ≤ m-1) := by
  have hs (A : Finset (Fin m)) : maskSet (fun i => decide (i ∈ A)) = A := by ext i; simp
  simp only [maskedDirections_length, hs]
  have hc : S.card + Sᶜ.card = m := by simp
  omega

end AdaptiveLocalization
end KLS
end
#print axioms KLS.AdaptiveLocalization.lowerCumulantDrift_eq_inverseCovariance_inner
