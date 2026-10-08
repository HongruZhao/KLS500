import TranspositionMovingParticlePath
import SpectralReductionIntervalSums
import TranspositionDefectAlgebra
import TranspositionSharpGap
import SpectralReductionCompleteSymmetrization

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem completeTranspositionDefect_le_moving_particle_intervals {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    completeTranspositionDefect ρ x ≤
      ∑ k : Fin q, (q+1 : ℝ)*((k : ℕ)+1)*(q-(k : ℕ))*
        ‖x-ρ (adjacentFinSwap q k) x‖^2 := by
  classical
  let D : Fin q → ℝ := fun k => ‖x-ρ (adjacentFinSwap q k) x‖^2
  let H : Fin (q+1) → Fin (q+1) → ℝ := fun i j =>
    if i<j then (((j : ℕ)-(i : ℕ) : ℕ) : ℝ)*
      ∑ k : Fin q, if (i : ℕ)≤k ∧ (k : ℕ)<j then D k else 0 else 0
  have hp (i j : Fin (q+1)) : ‖x-ρ (Equiv.swap i j) x‖^2 ≤ H i j+H j i := by
    rcases lt_trichotomy i j with hij|hij|hij
    · have hh := transpositionDefect_le_moving_particle_path ρ x i j hij.le
      have hnji : ¬ j < i := by omega
      simpa only [H,D,hij,hnji,↓reduceIte,add_zero] using hh
    · subst j
      have hi : ρ (Equiv.swap i i) x=x := by
        rw [Equiv.swap_self]
        change ρ 1 x=x
        simp
      rw [hi]
      simp [H]
    · have hh := transpositionDefect_le_moving_particle_path ρ x j i hij.le
      rw [Equiv.swap_comm] at hh
      have hnij : ¬ i < j := by omega
      simpa only [H,D,hij,hnij,↓reduceIte,zero_add] using hh
  have hsum := Finset.sum_le_sum (s:=Finset.univ) fun i _ =>
    Finset.sum_le_sum (s:=Finset.univ) fun j _ => hp i j
  have hswap : (∑ i, ∑ j, H j i)=∑ i, ∑ j, H i j := Finset.sum_comm
  simp_rw [Finset.sum_add_distrib] at hsum
  rw [hswap] at hsum
  have hH (i j : Fin (q+1)) : H i j=
      ∑ k : Fin q, D k*(if (i : ℕ)≤k ∧ (k : ℕ)<j then
        (((j : ℕ)-(i : ℕ) : ℕ) : ℝ) else 0) := by
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
  have heval : 2*(∑ i, ∑ j, H i j)=
      ∑ k : Fin q, (q+1 : ℝ)*((k : ℕ)+1)*(q-(k : ℕ))*D k := by
    simp_rw [hH]
    have hcomm : (∑ i : Fin (q+1), ∑ j : Fin (q+1), ∑ k : Fin q,
        D k*(if (i : ℕ)≤k ∧ (k : ℕ)<j then
          (((j : ℕ)-(i : ℕ) : ℕ) : ℝ) else 0)) =
        ∑ k : Fin q, ∑ i : Fin (q+1), ∑ j : Fin (q+1),
          D k*(if (i : ℕ)≤k ∧ (k : ℕ)<j then
            (((j : ℕ)-(i : ℕ) : ℕ) : ℝ) else 0) := by
      rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm),Finset.sum_comm]
    rw [hcomm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp_rw [←Finset.mul_sum]
    rw [sum_interval_distance]
    ring
  change completeTranspositionDefect ρ x≤_ at hsum
  rw [←two_mul] at hsum
  rw [heval] at hsum
  exact hsum

/-- The moving-particle bound and the proved sharp complete-transposition gap
leave one quarter of the standard interval weight. -/
theorem norm_sub_permutationAverage_sq_le_moving_particle_adjacent {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x-finiteIsometryAverage ρ x‖^2 ≤
      (1/4 : ℝ)*∑ k : Fin q, completeIntervalWeight q k*
        ‖x-ρ (adjacentFinSwap q k) x‖^2 := by
  have hh := (permutationAverage_completeTransposition_sharp (Nat.succ_pos q) ρ x).trans
    (completeTranspositionDefect_le_moving_particle_intervals ρ x)
  have he : (∑ k : Fin q, (q+1 : ℝ)*((k : ℕ)+1)*(q-(k : ℕ))*
      ‖x-ρ (adjacentFinSwap q k) x‖^2) =
      (4*(q+1 : ℝ))*((1/4 : ℝ)*∑ k : Fin q, completeIntervalWeight q k*
        ‖x-ρ (adjacentFinSwap q k) x‖^2) := by
    simp only [Finset.mul_sum,completeIntervalWeight]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hh
  norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_succ] at hh
  exact le_of_mul_le_mul_left hh (show (0 : ℝ)<4*(q+1) by positivity)

end KLS.ConstantReduction
end
