import TranspositionAverageAlgebra

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem permutationAverage_subgroup_residual_eq_star {n : ℕ}
    (ρ : Equiv.Perm (Fin (n+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖finiteIsometryAverage (ρ.comp (finSuccLiftHom n)) x - finiteIsometryAverage ρ x‖ ^ 2 =
      (2*(n+1 : ℝ))⁻¹ * ∑ i : Fin (n+1),
        ‖finiteIsometryAverage (ρ.comp (finSuccLiftHom n)) x -
          ρ (Equiv.swap 0 i) (finiteIsometryAverage (ρ.comp (finSuccLiftHom n)) x)‖ ^ 2 := by
  classical
  let y := finiteIsometryAverage (ρ.comp (finSuccLiftHom n)) x
  let z := finiteIsometryAverage ρ x
  have hN : (n+1 : ℝ) ≠ 0 := by positivity
  have hinner : inner ℝ y z = ‖z‖ ^ 2 := by
    have hh := inner_finiteIsometryAverage_self ρ y
    rw [finiteIsometryAverage_absorb] at hh
    exact hh
  have hpair : (∑ i : Fin (n+1), inner ℝ y (ρ (Equiv.swap 0 i) y)) =
      (n+1 : ℝ) * ‖z‖ ^ 2 := by
    have hh := congrArg (fun v : E => inner ℝ y v)
      (permutationAverage_eq_star_average ρ x)
    change inner ℝ y z = inner ℝ y ((n+1 : ℝ)⁻¹ • ∑ i : Fin (n+1), ρ (Equiv.swap 0 i) y) at hh
    rw [inner_smul_right, inner_sum, hinner] at hh
    field_simp at hh
    nlinarith
  change ‖y-z‖ ^ 2 = (2*(n+1 : ℝ))⁻¹ * ∑ i : Fin (n+1), ‖y-ρ (Equiv.swap 0 i) y‖ ^ 2
  simp_rw [norm_sub_sq_real, LinearIsometryEquiv.norm_map]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [hinner, hpair]
  field_simp
  ring

end KLS.ConstantReduction
end
