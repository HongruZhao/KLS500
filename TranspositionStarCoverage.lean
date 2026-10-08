import TranspositionDisjoint
import TranspositionOperator
import TranspositionTripleSum

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type*} [DecidableEq I]

theorem edgeDifference_inner_star_cover
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) (i j k l : I) :
    (if k=i then inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x k l) else 0) +
    (if l=i then inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x k l) else 0) +
    (if k=j then inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x k l) else 0) +
    (if l=j then inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x k l) else 0) -
    (if k=i ∧ l=j then ‖edgeDifference ρ x i j‖^2 else 0) -
    (if k=j ∧ l=i then ‖edgeDifference ρ x i j‖^2 else 0) ≤
      inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x k l) := by
  by_cases hij : i=j
  · subst j
    simp
  by_cases hki : k=i <;> by_cases hli : l=i <;> by_cases hkj : k=j <;> by_cases hlj : l=j
  all_goals simp_all [edgeDifference_symm]
  exact edgeDifference_inner_nonneg_disjoint ρ x i j k l (Ne.symm hki) (Ne.symm hli) (Ne.symm hkj) (Ne.symm hlj)

variable [Fintype I]

theorem completeTranspositionOperator_star_cover
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    4*completeTranspositionStarGram ρ x - 2*completeTranspositionDefect ρ x ≤
      ‖completeTranspositionOperator ρ x‖^2 := by
  have h1 : (∑ i : I, ∑ j : I, ∑ k : I, ∑ l : I,
      if k=i then inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x k l) else 0) =
      completeTranspositionStarGram ρ x := by
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp [completeTranspositionStarGram]
  have h2 : (∑ i : I, ∑ j : I, ∑ k : I, ∑ l : I,
      if l=i then inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x k l) else 0) =
      completeTranspositionStarGram ρ x := by
    simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
    unfold completeTranspositionStarGram
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [edgeDifference_symm ρ x k i]
  have h3 : (∑ i : I, ∑ j : I, ∑ k : I, ∑ l : I,
      if k=j then inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x k l) else 0) =
      completeTranspositionStarGram ρ x := by
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
    simpa only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte] using
      completeTranspositionStarGram_second ρ x
  have h4 : (∑ i : I, ∑ j : I, ∑ k : I, ∑ l : I,
      if l=j then inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x k l) else 0) =
      completeTranspositionStarGram ρ x := by
    simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
    convert completeTranspositionStarGram_second ρ x using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [edgeDifference_symm ρ x k j]
  have h5 : (∑ i : I, ∑ j : I, ∑ k : I, ∑ l : I,
      if k=i ∧ l=j then ‖edgeDifference ρ x i j‖^2 else 0) = completeTranspositionDefect ρ x := by
    simp only [ite_and]
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp [completeTranspositionDefect,edgeDifference]
  have h6 : (∑ i : I, ∑ j : I, ∑ k : I, ∑ l : I,
      if k=j ∧ l=i then ‖edgeDifference ρ x i j‖^2 else 0) = completeTranspositionDefect ρ x := by
    simp only [ite_and]
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp [completeTranspositionDefect,edgeDifference]
  have hR : (∑ i : I, ∑ j : I, ∑ k : I, ∑ l : I,
      inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x k l)) =
      ‖completeTranspositionOperator ρ x‖^2 := by
    rw [←real_inner_self_eq_norm_sq,completeTranspositionOperator_apply]
    simp only [sum_inner,inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    exact real_inner_comm _ _
  have hs := Finset.sum_le_sum (s:=Finset.univ) fun i _ =>
    Finset.sum_le_sum (s:=Finset.univ) fun j _ =>
      Finset.sum_le_sum (s:=Finset.univ) fun k _ =>
        Finset.sum_le_sum (s:=Finset.univ) fun l _ => edgeDifference_inner_star_cover ρ x i j k l
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hs
  rw [h1,h2,h3,h4,h5,h6,hR] at hs
  linarith

theorem completeTranspositionOperator_square_gap
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    (2*(Fintype.card I : ℝ))*inner ℝ x (completeTranspositionOperator ρ x) ≤
      ‖completeTranspositionOperator ρ x‖^2 := by
  have hs := completeTranspositionStarGram_bound ρ x
  have hc := completeTranspositionOperator_star_cover ρ x
  rw [completeTranspositionDefect_eq_operator] at hs hc
  nlinarith

end KLS.ConstantReduction
end
