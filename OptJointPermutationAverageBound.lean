import OptInsertionJointWords

/-! Exact joint insertion moments give individual coefficients in the
actual Hilbert permutation-average estimate. -/
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

def meanInsertionDefectWeight (q i : ℕ) : ℝ :=
  insertionJointMoment q (q-1-i)/2

theorem insertionDigitCount_nonneg (q i : ℕ) : 0 ≤ insertionDigitCount q i := by
  unfold insertionDigitCount
  positivity

theorem insertionDigitJoint_nonneg (q i : ℕ) : 0 ≤ insertionDigitJoint q i := by
  unfold insertionDigitJoint
  positivity

theorem insertionMeanCount_nonneg (q i : ℕ) : 0 ≤ insertionMeanCount q i := by
  induction q generalizing i with
  | zero => simp [insertionMeanCount]
  | succ q ih =>
    simp only [insertionMeanCount]
    apply add_nonneg (insertionDigitCount_nonneg _ _)
    split_ifs
    · exact le_rfl
    · exact ih _

theorem insertionJointMoment_nonneg (q i : ℕ) : 0 ≤ insertionJointMoment q i := by
  induction q generalizing i with
  | zero => simp [insertionJointMoment]
  | succ q ih =>
    simp only [insertionJointMoment]
    have hd := insertionDigitCount_nonneg (q+1) i
    have hj := insertionDigitJoint_nonneg (q+1) i
    have hc := insertionMeanCount_nonneg q (i-1)
    have hp := ih (i-1)
    split_ifs <;> positivity

theorem meanInsertionDefectWeight_nonneg (q i : ℕ) :
    0 ≤ meanInsertionDefectWeight q i := by
  exact div_nonneg (insertionJointMoment_nonneg _ _) (by norm_num)

theorem norm_sub_permutationAverage_sq_le_joint_individual {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x-finiteIsometryAverage ρ x‖^2 ≤
      ∑ i : Fin q, meanInsertionDefectWeight q i*‖x-ρ (adjacentFinSwap q i) x‖^2 := by
  classical
  obtain ⟨W, hW, _, _, hjoint⟩ := exists_adjacentFinSwapWords_joint_moments q
  let C := (Fin.revPerm : Equiv.Perm (Fin (q+1))).permCongrHom
  have hCC (σ : Equiv.Perm (Fin (q+1))) : C (C σ) = σ := by
    apply Equiv.ext
    intro j
    change (Fin.revPerm.permCongr (Fin.revPerm.permCongr σ)) j = σ j
    simp only [Equiv.permCongr_apply, Fin.revPerm_apply, Fin.revPerm_symm, Fin.rev_rev]
  let eC : Equiv.Perm (Fin (q+1)) ≃ Equiv.Perm (Fin (q+1)) := ⟨C,C,hCC,hCC⟩
  let V (σ : Equiv.Perm (Fin (q+1))) := (W (C σ)).map Fin.rev
  have hV (σ : Equiv.Perm (Fin (q+1))) : ((V σ).map (adjacentFinSwap q)).prod = σ := by
    calc
      _ = ((W (C σ)).map (fun i => C (adjacentFinSwap q i))).prod := by
        simp only [V, List.map_map, Function.comp_def, C, adjacentFinSwap_reflection]
      _ = C (((W (C σ)).map (adjacentFinSwap q)).prod) := by
        rw [map_list_prod, List.map_map]
        rfl
      _ = σ := by rw [hW, hCC]
  have hJ (i : Fin q) :
      (∑ σ, ((V σ).length : ℝ)*((V σ).count i : ℝ)) =
        (Fintype.card (Equiv.Perm (Fin (q+1))) : ℝ)*insertionJointMoment q i.rev := by
    have hcount (σ : Equiv.Perm (Fin (q+1))) :
        (V σ).count i = (W (C σ)).count i.rev := by
      have hh := List.count_map_of_injective (W (C σ)) Fin.rev
        (Fin.rev_involutive.injective) i.rev
      simpa only [Fin.rev_rev] using hh
    simp only [hcount, V, List.length_map]
    change (∑ σ, ((W (eC σ)).length : ℝ)*((W (eC σ)).count i.rev : ℝ)) = _
    rw [eC.sum_comp (fun σ => ((W σ).length : ℝ)*((W σ).count i.rev : ℝ))]
    exact hjoint i.rev
  let D : Fin q → ℝ := fun i => ‖x-ρ (adjacentFinSwap q i) x‖^2
  have hpoint (σ : Equiv.Perm (Fin (q+1))) :
      ‖x-ρ σ x‖^2 ≤ ∑ i : Fin q, (((V σ).length : ℝ)*((V σ).count i : ℝ))*D i := by
    have hn : ‖x-ρ σ x‖ ≤ ((V σ).map (fun i => ‖x-ρ (adjacentFinSwap q i) x‖)).sum := by
      simpa only [hV σ] using
        (norm_sub_isometry_word_le_sum ρ (adjacentFinSwap q) x (V σ))
    have hs := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hn)).mpr hn
    have hc : (((V σ).map (fun i => ‖x-ρ (adjacentFinSwap q i) x‖)).sum)^2 ≤
        ((V σ).length : ℝ)*((V σ).map D).sum := by
      simpa [List.map_map, Function.comp_def, D] using
        (Multiset.sq_sum_le_card_mul_sum_sq
          (((V σ).map (fun i => ‖x-ρ (adjacentFinSwap q i) x‖) : List ℝ) : Multiset ℝ))
    have hh := hs.trans hc
    rw [list_sum_map_eq_sum_count, Finset.mul_sum] at hh
    simpa only [mul_assoc] using hh
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun σ _ => hpoint σ
  rw [Finset.sum_comm] at hsum
  simp_rw [← Finset.sum_mul, hJ] at hsum
  have hN : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin (q+1))) := by
    exact_mod_cast Fintype.card_pos
  rw [norm_sub_finiteIsometryAverage_sq_eq_average]
  have hh := mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hN.le))
  apply hh.trans_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (i.rev : ℕ) = q-1-(i : ℕ) := by rw [Fin.val_rev]; omega
  rw [hi]
  change (2*(Fintype.card (Equiv.Perm (Fin (q+1))) : ℝ))⁻¹*
      (((Fintype.card (Equiv.Perm (Fin (q+1))) : ℝ)*insertionJointMoment q (q-1-(i : ℕ)))*D i) =
      meanInsertionDefectWeight q i*D i
  unfold meanInsertionDefectWeight
  field_simp

end KLS.ConstantReduction
end
