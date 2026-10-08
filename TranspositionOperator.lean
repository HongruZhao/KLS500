import TranspositionLocalGap
import TranspositionAverageBound

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type*} [Fintype I] [DecidableEq I]

def completeTranspositionOperator (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) : E →ₗ[ℝ] E :=
  ∑ i : I, ∑ j : I, (LinearMap.id - (ρ (Equiv.swap i j)).toLinearMap)

theorem completeTranspositionOperator_apply (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    completeTranspositionOperator ρ x = ∑ i : I, ∑ j : I, edgeDifference ρ x i j := by
  simp only [completeTranspositionOperator,LinearMap.sum_apply,LinearMap.sub_apply,
    LinearMap.id_apply,edgeDifference]
  rfl

theorem completeTranspositionOperator_symmetric (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) :
    (completeTranspositionOperator ρ).IsSymmetric := by
  intro x y
  simp only [completeTranspositionOperator_apply,sum_inner,inner_sum,edgeDifference,
    inner_sub_left,inner_sub_right,inner_transposition_action]

theorem completeTranspositionDefect_eq_operator (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    completeTranspositionDefect ρ x = 2 * inner ℝ x (completeTranspositionOperator ρ x) := by
  change (∑ i : I, ∑ j : I, ‖edgeDifference ρ x i j‖^2) = _
  simp_rw [edgeDifference_norm_sq]
  simp only [completeTranspositionOperator_apply,inner_sum,Finset.mul_sum]

theorem completeTranspositionOperator_nonneg (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    0 ≤ inner ℝ x (completeTranspositionOperator ρ x) := by
  have ht : 0 ≤ completeTranspositionDefect ρ x := by
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [completeTranspositionDefect_eq_operator] at ht
  linarith

theorem completeTranspositionOperator_kernel_fixed {n : ℕ} (hn : 0<n)
    (ρ : Equiv.Perm (Fin n) →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (hx : completeTranspositionOperator ρ x = 0) : x = finiteIsometryAverage ρ x := by
  have hw := permutationAverage_completeTransposition_bound n ρ x
  rw [completeTranspositionDefect_eq_operator,hx,inner_zero_right,mul_zero] at hw
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hz : ‖x-finiteIsometryAverage ρ x‖^2 = 0 := by nlinarith [sq_nonneg ‖x-finiteIsometryAverage ρ x‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

end KLS.ConstantReduction
end
