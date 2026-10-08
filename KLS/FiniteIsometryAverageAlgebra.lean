import KLS.FiniteGroupSymmetrization

/-! Linearity, contraction, and subgroup absorption for the literal average
of a finite group acting by real linear isometries. -/

open scoped BigOperators
noncomputable section
namespace KLS
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [Group G] [Fintype G]

def finiteIsometryAverageLinearMap (ρ : G →* (E ≃ₗᵢ[ℝ] E)) : E →ₗ[ℝ] E where
  toFun := finiteIsometryAverage ρ
  map_add' x y := by simp [finiteIsometryAverage, map_add, Finset.sum_add_distrib, smul_add]
  map_smul' c x := by
    simp only [finiteIsometryAverage, map_smul, ← Finset.smul_sum]
    exact smul_comm _ _ _

theorem norm_finiteIsometryAverage_le (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖finiteIsometryAverage ρ x‖ ≤ ‖x‖ := by
  have hN : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hNp : 0 ≤ (Fintype.card G : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [finiteIsometryAverage, norm_smul, Real.norm_eq_abs, abs_of_nonneg hNp]
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖ρ g x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hNp
    _ = ‖x‖ := by
      simp only [LinearIsometryEquiv.norm_map, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

theorem finiteIsometryAverage_right_invariant (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (g : G) :
    finiteIsometryAverage ρ (ρ g x) = finiteIsometryAverage ρ x := by
  unfold finiteIsometryAverage
  congr 1
  have hm (h : G) : ρ h (ρ g x) = ρ (h * g) x := by rw [map_mul]; rfl
  simp_rw [hm]
  exact Equiv.sum_comp (Equiv.mulRight g) (fun h => ρ h x)

/-- Averaging over the full group absorbs any preceding average through a
group homomorphism, without an unstated compatibility assumption. -/
theorem finiteIsometryAverage_absorb {H : Type*} [Group H] [Fintype H]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (e : H →* G) (x : E) :
    finiteIsometryAverage ρ (finiteIsometryAverage (ρ.comp e) x) = finiteIsometryAverage ρ x := by
  change finiteIsometryAverageLinearMap ρ (finiteIsometryAverage (ρ.comp e) x) = _
  rw [finiteIsometryAverage, map_smul, map_sum]
  have he (h : H) : finiteIsometryAverageLinearMap ρ ((ρ.comp e) h x) = finiteIsometryAverage ρ x :=
    finiteIsometryAverage_right_invariant ρ x (e h)
  simp_rw [he]
  have hN : (Fintype.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ hN, one_smul]

end KLS
end

#print axioms KLS.finiteIsometryAverageLinearMap
#print axioms KLS.norm_finiteIsometryAverage_le
#print axioms KLS.finiteIsometryAverage_absorb
