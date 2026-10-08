import SpectralReductionIntervalSums

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem completeTranspositionDefect_le_adjacent_intervals {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    completeTranspositionDefect ρ x ≤
      ∑ k : Fin q, 4*(q+1 : ℝ)*((k : ℕ)+1)*(q-(k : ℕ))*
        ‖x-ρ (adjacentFinSwap q k) x‖^2 := by
  classical
  let D : Fin q → ℝ := fun k => ‖x-ρ (adjacentFinSwap q k) x‖^2
  let H : Fin (q+1) → Fin (q+1) → ℝ := fun i j =>
    if i<j then 4*(((j : ℕ)-(i : ℕ) : ℕ) : ℝ)*
      ∑ k : Fin q, if (i : ℕ)≤k ∧ (k : ℕ)<j then D k else 0 else 0
  have hp (i j : Fin (q+1)) : ‖x-ρ (Equiv.swap i j) x‖^2 ≤ H i j+H j i := by
    rcases lt_trichotomy i j with hij|hij|hij
    · have hh := transpositionDefect_le_interval_adjacentDefects ρ x i j hij
      have hnji : ¬ j < i := by omega
      simpa only [H,D,hij,hnji,↓reduceIte,add_zero] using hh
    · subst j
      have hi : ρ (Equiv.swap i i) x=x := by
        rw [Equiv.swap_self]
        change ρ 1 x=x
        simp
      rw [hi]
      simp [H]
    · have hh := transpositionDefect_le_interval_adjacentDefects ρ x j i hij
      rw [Equiv.swap_comm] at hh
      have hnij : ¬ i < j := by omega
      simpa only [H,D,hij,hnij,↓reduceIte,zero_add] using hh
  have hsum := Finset.sum_le_sum (s:=Finset.univ) fun i _ =>
    Finset.sum_le_sum (s:=Finset.univ) fun j _ => hp i j
  have hswap : (∑ i, ∑ j, H j i)=∑ i, ∑ j, H i j := Finset.sum_comm
  simp_rw [Finset.sum_add_distrib] at hsum
  rw [hswap] at hsum
  have hH (i j : Fin (q+1)) : H i j=
      ∑ k : Fin q, 4*D k*(if (i : ℕ)≤k ∧ (k : ℕ)<j then (((j : ℕ)-(i : ℕ) : ℕ) : ℝ) else 0) := by
    unfold H
    by_cases hij : i<j
    · rw [ite_eq_left hij,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
    · rw [ite_eq_right hij]
      symm
      apply Finset.sum_eq_zero
      intro k _
      rw [ite_eq_right (show ¬((i : ℕ)≤k ∧ (k : ℕ)<j) by omega)]
      ring
  have heval : (∑ i, ∑ j, H i j)=
      ∑ k : Fin q, 2*(q+1 : ℝ)*((k : ℕ)+1)*(q-(k : ℕ))*D k := by
    simp_rw [hH]
    calc
      _ = ∑ i : Fin (q+1), ∑ k : Fin q, ∑ j : Fin (q+1),
          4*D k*(if (i : ℕ)≤k ∧ (k : ℕ)<j then (((j : ℕ)-(i : ℕ) : ℕ) : ℝ) else 0) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ k : Fin q, ∑ i : Fin (q+1), ∑ j : Fin (q+1),
          4*D k*(if (i : ℕ)≤k ∧ (k : ℕ)<j then (((j : ℕ)-(i : ℕ) : ℕ) : ℝ) else 0) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        simp_rw [←Finset.mul_sum]
        rw [sum_interval_distance]
        ring
  rw [heval] at hsum
  change completeTranspositionDefect ρ x≤_ at hsum
  have he : (∑ k : Fin q, 2*(q+1 : ℝ)*((k : ℕ)+1)*(q-(k : ℕ))*D k)+
      (∑ k : Fin q, 2*(q+1 : ℝ)*((k : ℕ)+1)*(q-(k : ℕ))*D k)=
      ∑ k : Fin q, 4*(q+1 : ℝ)*((k : ℕ)+1)*(q-(k : ℕ))*D k := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hsum
  exact hsum

theorem norm_sub_permutationAverage_sq_le_complete_adjacent {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x-finiteIsometryAverage ρ x‖^2 ≤
      ∑ k : Fin q, 2*((k : ℕ)+1)*(q-(k : ℕ))*‖x-ρ (adjacentFinSwap q k) x‖^2 := by
  have hh := (permutationAverage_completeTransposition_bound (q+1) ρ x).trans
    (completeTranspositionDefect_le_adjacent_intervals ρ x)
  have he : (∑ k : Fin q, 4*(q+1 : ℝ)*((k : ℕ)+1)*(q-(k : ℕ))*‖x-ρ (adjacentFinSwap q k) x‖^2)=
      (2*(q+1 : ℝ))*(∑ k : Fin q, 2*((k : ℕ)+1)*(q-(k : ℕ))*‖x-ρ (adjacentFinSwap q k) x‖^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hh
  norm_num only [Nat.cast_add,Nat.cast_one] at hh
  exact (mul_le_mul_iff_right₀ (show (0 : ℝ)<2*(q+1) by positivity)).mp hh

theorem completeTranspositionCoefficient_nonneg (n : ℕ) : 0≤completeTranspositionCoefficient n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [completeTranspositionCoefficient]
  | one => simp [completeTranspositionCoefficient]
  | more n _ ih =>
    rw [completeTranspositionCoefficient]
    positivity

theorem norm_sub_permutationAverage_sq_le_finite_complete_adjacent {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x-finiteIsometryAverage ρ x‖^2 ≤
      ∑ k : Fin q, (4*(q+1 : ℝ)*completeTranspositionCoefficient (q+1))*
        ((k : ℕ)+1)*(q-(k : ℕ))*‖x-ρ (adjacentFinSwap q k) x‖^2 := by
  have hh := (permutationAverage_completeTransposition_finite_coefficient (q+1) ρ x).trans
    (mul_le_mul_of_nonneg_left (completeTranspositionDefect_le_adjacent_intervals ρ x)
      (completeTranspositionCoefficient_nonneg (q+1)))
  calc
    _ ≤ completeTranspositionCoefficient (q+1)*
        ∑ k : Fin q, 4*(q+1 : ℝ)*((k : ℕ)+1)*(q-(k : ℕ))*‖x-ρ (adjacentFinSwap q k) x‖^2 := hh
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

end KLS.ConstantReduction
end
