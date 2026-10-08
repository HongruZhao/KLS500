import TranspositionTripleGap

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type*} [DecidableEq I]

def edgeDifference (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) (i j : I) : E :=
  x - ρ (Equiv.swap i j) x

theorem edgeDifference_symm (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) (i j : I) :
    edgeDifference ρ x i j = edgeDifference ρ x j i := by
  simp only [edgeDifference,Equiv.swap_comm]

@[simp] theorem edgeDifference_self (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) (i : I) :
    edgeDifference ρ x i i = 0 := by
  rw [edgeDifference,Equiv.swap_self]
  change x - ρ 1 x = 0
  rw [map_one]
  exact sub_self x

theorem edgeDifference_norm_sq (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) (i j : I) :
    ‖edgeDifference ρ x i j‖^2 = 2 * inner ℝ x (edgeDifference ρ x i j) := by
  simp only [edgeDifference,norm_sub_sq_real,LinearIsometryEquiv.norm_map,
    inner_sub_right,real_inner_self_eq_norm_sq]
  ring

theorem viaEmbeddingHom_swap {J : Type*} [DecidableEq J]
    (ι : J ↪ I) (i j : J) :
    Equiv.Perm.viaEmbeddingHom ι (Equiv.swap i j) = Equiv.swap (ι i) (ι j) := by
  classical
  ext x
  change (Equiv.swap i j).viaEmbedding ι x = _
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨y,rfl⟩ := hx
    rw [Equiv.Perm.viaEmbedding_apply]
    exact ι.injective.map_swap i j y
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx]
    apply (Equiv.swap_apply_of_ne_of_ne ?_ ?_).symm
    · intro h
      apply hx
      exact ⟨i,h.symm⟩
    · intro h
      apply hx
      exact ⟨j,h.symm⟩

theorem tripleTranspositionLaplacian_gap_embedding
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) (ι : Fin 3 ↪ I) :
    3 * inner ℝ x (edgeDifference ρ x (ι 0) (ι 1) +
        edgeDifference ρ x (ι 0) (ι 2) + edgeDifference ρ x (ι 1) (ι 2)) ≤
      ‖edgeDifference ρ x (ι 0) (ι 1) +
        edgeDifference ρ x (ι 0) (ι 2) + edgeDifference ρ x (ι 1) (ι 2)‖^2 := by
  have hh := tripleTranspositionLaplacian_gap_square (ρ.comp (Equiv.Perm.viaEmbeddingHom ι)) x
  have he : tripleTranspositionLaplacian (ρ.comp (Equiv.Perm.viaEmbeddingHom ι)) x =
      edgeDifference ρ x (ι 0) (ι 1) + edgeDifference ρ x (ι 0) (ι 2) +
        edgeDifference ρ x (ι 1) (ι 2) := by
    simp only [tripleTranspositionLaplacian,edgeDifference,MonoidHom.comp_apply,viaEmbeddingHom_swap]
    module
  simpa only [he] using hh

theorem edgeDifference_triple_cross (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (i j k : I) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ‖edgeDifference ρ x i j‖^2 + ‖edgeDifference ρ x i k‖^2 + ‖edgeDifference ρ x j k‖^2 ≤
      4*(inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x i k) +
        inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x j k) +
        inner ℝ (edgeDifference ρ x i k) (edgeDifference ρ x j k)) := by
  let ι : Fin 3 ↪ I := ⟨![i,j,k], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all⟩
  have hh := tripleTranspositionLaplacian_gap_embedding ρ x ι
  change 3 * inner ℝ x (edgeDifference ρ x i j + edgeDifference ρ x i k + edgeDifference ρ x j k) ≤
    ‖edgeDifference ρ x i j + edgeDifference ρ x i k + edgeDifference ρ x j k‖^2 at hh
  rw [norm_add_sq_real,norm_add_sq_real,inner_add_left,inner_add_right,inner_add_right] at hh
  have h1 := edgeDifference_norm_sq ρ x i j
  have h2 := edgeDifference_norm_sq ρ x i k
  have h3 := edgeDifference_norm_sq ρ x j k
  linarith

end KLS.ConstantReduction
end
