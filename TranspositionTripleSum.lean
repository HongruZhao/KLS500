import TranspositionOperator

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type*} [DecidableEq I]

theorem edgeDifference_triple_cross_all (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) (i j k : I) :
    ‖edgeDifference ρ x i j‖^2 + ‖edgeDifference ρ x i k‖^2 + ‖edgeDifference ρ x j k‖^2 +
      2*(if i=j then ‖edgeDifference ρ x i k‖^2 else 0) +
      2*(if i=k then ‖edgeDifference ρ x i j‖^2 else 0) +
      2*(if j=k then ‖edgeDifference ρ x i j‖^2 else 0) ≤
      4*(inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x i k) +
        inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x j k) +
        inner ℝ (edgeDifference ρ x i k) (edgeDifference ρ x j k)) := by
  by_cases hij : i=j
  · subst j
    simp
    ring_nf
    exact le_rfl
  by_cases hik : i=k
  · subst k
    simp [hij,Ne.symm hij,edgeDifference_symm ρ x j i]
    ring_nf
    exact le_rfl
  by_cases hjk : j=k
  · subst k
    simp [hij]
    ring_nf
    exact le_rfl
  simpa only [hij,hik,hjk,↓reduceIte,mul_zero,add_zero] using
    edgeDifference_triple_cross ρ x i j k hij hik hjk

variable [Fintype I]

def completeTranspositionStarGram (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) : ℝ :=
  ∑ i : I, ∑ j : I, ∑ k : I,
    inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x i k)

theorem completeTranspositionStarGram_second (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    (∑ i : I, ∑ j : I, ∑ k : I,
      inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x j k)) = completeTranspositionStarGram ρ x := by
  calc
    _ = ∑ i : I, ∑ j : I, ∑ k : I,
        inner ℝ (edgeDifference ρ x j i) (edgeDifference ρ x j k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [edgeDifference_symm ρ x i j]
    _ = _ := by rw [Finset.sum_comm]; rfl

theorem completeTranspositionStarGram_third (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    (∑ i : I, ∑ j : I, ∑ k : I,
      inner ℝ (edgeDifference ρ x i k) (edgeDifference ρ x j k)) = completeTranspositionStarGram ρ x := by
  calc
    _ = ∑ i : I, ∑ j : I, ∑ k : I,
        inner ℝ (edgeDifference ρ x k i) (edgeDifference ρ x k j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [edgeDifference_symm ρ x i k,edgeDifference_symm ρ x j k]
    _ = ∑ i : I, ∑ k : I, ∑ j : I,
        inner ℝ (edgeDifference ρ x k i) (edgeDifference ρ x k j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]; rfl

theorem completeTranspositionStarGram_bound (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ((Fintype.card I : ℝ)+2)*completeTranspositionDefect ρ x ≤
      4*completeTranspositionStarGram ρ x := by
  have ht : completeTranspositionDefect ρ x =
      ∑ i : I, ∑ j : I, ‖edgeDifference ρ x i j‖^2 := rfl
  have h1 : (∑ i : I, ∑ j : I, ∑ k : I, ‖edgeDifference ρ x i j‖^2) =
      (Fintype.card I : ℝ)*completeTranspositionDefect ρ x := by
    rw [ht]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.mul_sum]
  have h2 : (∑ i : I, ∑ j : I, ∑ k : I, ‖edgeDifference ρ x i k‖^2) =
      (Fintype.card I : ℝ)*completeTranspositionDefect ρ x := by
    calc
      _ = ∑ i : I, ∑ k : I, ∑ j : I, ‖edgeDifference ρ x i k‖^2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := h1
  have h3 : (∑ i : I, ∑ j : I, ∑ k : I, ‖edgeDifference ρ x j k‖^2) =
      (Fintype.card I : ℝ)*completeTranspositionDefect ρ x := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,ht]
  have h4 : (∑ i : I, ∑ j : I, ∑ k : I,
      if i=j then ‖edgeDifference ρ x i k‖^2 else 0) = completeTranspositionDefect ρ x := by
    rw [ht]
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp
  have h5 : (∑ i : I, ∑ j : I, ∑ k : I,
      if i=k then ‖edgeDifference ρ x i j‖^2 else 0) = completeTranspositionDefect ρ x := by
    rw [ht]
    simp
  have h6 : (∑ i : I, ∑ j : I, ∑ k : I,
      if j=k then ‖edgeDifference ρ x i j‖^2 else 0) = completeTranspositionDefect ρ x := by
    rw [ht]
    simp
  have hs := Finset.sum_le_sum (s:=Finset.univ) fun i _ =>
    Finset.sum_le_sum (s:=Finset.univ) fun j _ =>
      Finset.sum_le_sum (s:=Finset.univ) fun k _ => edgeDifference_triple_cross_all ρ x i j k
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hs
  rw [h1,h2,h3,h4,h5,h6,completeTranspositionStarGram_second,
    completeTranspositionStarGram_third] at hs
  change (Fintype.card I : ℝ)*completeTranspositionDefect ρ x+
    (Fintype.card I : ℝ)*completeTranspositionDefect ρ x+
    (Fintype.card I : ℝ)*completeTranspositionDefect ρ x+
    2*completeTranspositionDefect ρ x+2*completeTranspositionDefect ρ x+
    2*completeTranspositionDefect ρ x ≤
    4*(completeTranspositionStarGram ρ x+completeTranspositionStarGram ρ x+
      completeTranspositionStarGram ρ x) at hs
  linarith

end KLS.ConstantReduction
end
