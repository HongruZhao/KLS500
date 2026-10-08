import TranspositionSignedAverage

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def realPermutationSign (I : Type*) [Fintype I] [DecidableEq I] : Equiv.Perm I →* ℝ :=
  ((Int.castRingHom ℝ).toMonoidHom.comp (Units.coeHom ℤ)).comp Equiv.Perm.sign

theorem realPermutationSign_square {I : Type*} [Fintype I] [DecidableEq I] (g : Equiv.Perm I) :
    realPermutationSign I g * realPermutationSign I g = 1 := by
  have hh := congrArg (fun u : ℤˣ => ((u : ℤ) : ℝ)) (Int.units_mul_self (Equiv.Perm.sign g))
  simpa only [realPermutationSign,MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass,Units.coeHom_apply,Int.coe_castRingHom,Units.val_mul,Int.cast_mul,
    Units.val_one,Int.cast_one] using hh

def tripleTranspositionLaplacian
    (ρ : Equiv.Perm (Fin 3) →* (E ≃ₗᵢ[ℝ] E)) (x : E) : E :=
  (3 : ℝ) • x - ρ (Equiv.swap 0 1) x - ρ (Equiv.swap 0 2) x - ρ (Equiv.swap 1 2) x

theorem triple_sign_sum
    (ρ : Equiv.Perm (Fin 3) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    characterIsometrySum (realPermutationSign (Fin 3)) ρ x =
      x - ρ (Equiv.swap 0 1) x - ρ (Equiv.swap 0 2) x - ρ (Equiv.swap 1 2) x +
        ρ ((Equiv.swap 0 1)*(Equiv.swap 1 2)) x +
        ρ ((Equiv.swap 1 2)*(Equiv.swap 0 1)) x := by
  classical
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        (Equiv.swap 0 1)*(Equiv.swap 1 2), (Equiv.swap 1 2)*(Equiv.swap 0 1)} := by decide
  have hone : (1 : E ≃ₗᵢ[ℝ] E) x = x := rfl
  unfold characterIsometrySum
  rw [huniv]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),Finset.sum_singleton]
  norm_num [realPermutationSign,Equiv.Perm.sign_swap,Equiv.Perm.sign_mul,
    Finset.sum_insert, hone, show (0 : Fin 3)≠1 by decide, show (0 : Fin 3)≠2 by decide,
    show (1 : Fin 3)≠2 by decide]
  module

theorem inner_transposition_action {I : Type*} [DecidableEq I]
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x y : E) (i j : I) :
    inner ℝ (ρ (Equiv.swap i j) x) y = inner ℝ x (ρ (Equiv.swap i j) y) := by
  have hh := (ρ (Equiv.swap i j)).inner_map_map x (ρ (Equiv.swap i j) y)
  have hinv : ρ (Equiv.swap i j) (ρ (Equiv.swap i j) y) = y := by
    change (ρ (Equiv.swap i j) * ρ (Equiv.swap i j)) y = y
    rw [←map_mul,Equiv.swap_mul_self,map_one]
    rfl
  rw [hinv] at hh
  exact hh

theorem tripleTranspositionLaplacian_selfadjoint
    (ρ : Equiv.Perm (Fin 3) →* (E ≃ₗᵢ[ℝ] E)) (x y : E) :
    inner ℝ (tripleTranspositionLaplacian ρ x) y =
      inner ℝ x (tripleTranspositionLaplacian ρ y) := by
  simp only [tripleTranspositionLaplacian,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right,conj_trivial,inner_transposition_action]

theorem tripleTranspositionLaplacian_square
    (ρ : Equiv.Perm (Fin 3) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    tripleTranspositionLaplacian ρ (tripleTranspositionLaplacian ρ x) =
      (3 : ℝ) • tripleTranspositionLaplacian ρ x +
        (3 : ℝ) • characterIsometrySum (realPermutationSign (Fin 3)) ρ x := by
  have hmul (g h : Equiv.Perm (Fin 3)) : ρ g (ρ h x) = ρ (g*h) x := by
    rw [map_mul]
    rfl
  have hone : (1 : E ≃ₗᵢ[ℝ] E) x = x := rfl
  rw [triple_sign_sum]
  simp only [tripleTranspositionLaplacian,map_sub,map_smul,hmul,
    Equiv.swap_mul_self,map_one,hone]
  have hab : (Equiv.swap (0 : Fin 3) 1)*(Equiv.swap 0 2) =
      (Equiv.swap 1 2)*(Equiv.swap 0 1) := by decide
  have hba : (Equiv.swap (0 : Fin 3) 2)*(Equiv.swap 0 1) =
      (Equiv.swap 0 1)*(Equiv.swap 1 2) := by decide
  have hbc : (Equiv.swap (0 : Fin 3) 2)*(Equiv.swap 1 2) =
      (Equiv.swap 1 2)*(Equiv.swap 0 1) := by decide
  have hcb : (Equiv.swap (1 : Fin 3) 2)*(Equiv.swap 0 2) =
      (Equiv.swap 0 1)*(Equiv.swap 1 2) := by decide
  rw [hab,hba,hbc,hcb]
  module

theorem tripleTranspositionLaplacian_gap_square
    (ρ : Equiv.Perm (Fin 3) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    3 * inner ℝ x (tripleTranspositionLaplacian ρ x) ≤
      ‖tripleTranspositionLaplacian ρ x‖^2 := by
  have hp := characterIsometrySum_inner_nonneg (realPermutationSign (Fin 3))
    realPermutationSign_square ρ x
  have hid : ‖tripleTranspositionLaplacian ρ x‖^2 =
      3 * inner ℝ x (tripleTranspositionLaplacian ρ x) +
        3 * inner ℝ x (characterIsometrySum (realPermutationSign (Fin 3)) ρ x) := by
    rw [←real_inner_self_eq_norm_sq,tripleTranspositionLaplacian_selfadjoint,
      tripleTranspositionLaplacian_square,inner_add_right,inner_smul_right,inner_smul_right]
  linarith

end KLS.ConstantReduction
end
