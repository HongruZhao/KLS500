import KLS.FiniteIsometryAverageAlgebra

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first nontrivial permutation average is exactly the midpoint of the
identity and the adjacent swap. -/
theorem finiteIsometryAverage_finTwo_eq
    (ρ : Equiv.Perm (Fin 2) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    finiteIsometryAverage ρ x = (1/2 : ℝ) • (x + ρ (adjacentFinSwap 1 0) x) := by
  classical
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ adjacentFinSwap 1 0 := by
    intro heq
    have h := congrArg (fun σ : Equiv.Perm (Fin 2) => σ 0) heq
    norm_num [adjacentFinSwap] at h
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, adjacentFinSwap 1 0} := by
    exact (Finset.eq_univ_of_card {1, adjacentFinSwap 1 0}
      (by simp [hne, Fintype.card_perm])).symm
  simp [finiteIsometryAverage, hu, hne, Fintype.card_perm, one_div]

/-- The squared distance to this actual average is exactly one quarter of
the adjacent defect. This holds in any real normed space. -/
theorem norm_sub_finiteIsometryAverage_finTwo_sq
    (ρ : Equiv.Perm (Fin 2) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x - finiteIsometryAverage ρ x‖ ^ 2 =
      (1/4 : ℝ) * ‖x - ρ (adjacentFinSwap 1 0) x‖ ^ 2 := by
  rw [finiteIsometryAverage_finTwo_eq]
  have heq : x - (1/2 : ℝ) • (x + ρ (adjacentFinSwap 1 0) x) =
      (1/2 : ℝ) • (x - ρ (adjacentFinSwap 1 0) x) := by module
  rw [heq, norm_smul]
  norm_num
  ring

end KLS.ConstantReduction
end
