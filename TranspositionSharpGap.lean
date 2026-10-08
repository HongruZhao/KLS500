import TranspositionStarCoverage
import OptFiniteOrbitGap

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact complete-transposition spectral gap, with ordered pairs. -/
theorem permutationAverage_completeTransposition_sharp {n : ℕ} (hn : 0<n)
    (ρ : Equiv.Perm (Fin n) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    (4*(n : ℝ))*‖x-finiteIsometryAverage ρ x‖^2 ≤ completeTranspositionDefect ρ x := by
  have hsquare (z : E) : (2*(n : ℝ))*inner ℝ z (completeTranspositionOperator ρ z) ≤
      ‖completeTranspositionOperator ρ z‖^2 := by
    simpa only [Fintype.card_fin] using completeTranspositionOperator_square_gap ρ z
  have hstable (u z : E) (hz : z ∈ finiteOrbitSpan ρ u) :
      completeTranspositionOperator ρ z ∈ finiteOrbitSpan ρ u := by
    rw [completeTranspositionOperator_apply]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    exact (finiteOrbitSpan ρ u).sub_mem hz (action_preserves_finiteOrbitSpan ρ u (Equiv.swap i j) hz)
  have hkill (u : E) : completeTranspositionOperator ρ (finiteIsometryAverage ρ u) = 0 := by
    simp only [completeTranspositionOperator_apply,edgeDifference,finiteIsometryAverage_fixed,
      sub_self,Finset.sum_const_zero]
  have hg := finite_action_gap_of_positive_square ρ (completeTranspositionOperator ρ)
    (completeTranspositionOperator_symmetric ρ) (2*(n : ℝ))
    (completeTranspositionOperator_nonneg ρ) hsquare hstable hkill
    (fun z hz => completeTranspositionOperator_kernel_fixed hn ρ z hz) x
  rw [completeTranspositionDefect_eq_operator]
  linarith

end KLS.ConstantReduction
end
