import TranspositionIntervalComparison
import TranspositionFiniteCoefficient

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

theorem sum_fin_natCast_real (n : ℕ) : (∑ i : Fin n, (i : ℝ))=(n : ℝ)*(n-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,ih,Nat.cast_add,Nat.cast_one]
    ring

theorem sum_interval_distance_rectangle (L R : ℕ) :
    (∑ i : Fin (L+R), ∑ j : Fin (L+R),
      if (i : ℕ)<L ∧ L≤(j : ℕ) then (j : ℝ)-(i : ℝ) else 0)=
      (L : ℝ)*R*(L+R)/2 := by
  simp_rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd,Fin.val_natAdd]
  have hL (i : Fin L) : ¬L≤(i : ℕ) := by omega
  have hR (i : Fin R) : ¬L+(i : ℕ)<L := by omega
  simp only [Fin.is_lt,hL,hR,Nat.le_add_right,true_and,false_and,↓reduceIte,
    Finset.sum_const_zero,zero_add,add_zero]
  simp only [Nat.cast_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum,sum_fin_natCast_real]
  ring

theorem sum_interval_distance (q : ℕ) (k : Fin q) :
    (∑ i : Fin (q+1), ∑ j : Fin (q+1),
      if (i : ℕ)≤k ∧ (k : ℕ)<j then (((j : ℕ)-(i : ℕ) : ℕ) : ℝ) else 0)=
      (q+1 : ℝ)*((k : ℕ)+1)*(q-(k : ℕ))/2 := by
  have hn : q+1=((k : ℕ)+1)+(q-(k : ℕ)) := by omega
  have he (i j : Fin (q+1)) :
      (if (i : ℕ)≤k ∧ (k : ℕ)<j then (((j : ℕ)-(i : ℕ) : ℕ) : ℝ) else 0)=
      (if (i : ℕ)<(k : ℕ)+1 ∧ (k : ℕ)+1≤j then (j : ℝ)-(i : ℝ) else 0) := by
    by_cases h : (i : ℕ)≤k ∧ (k : ℕ)<j
    · rw [ite_eq_left h,ite_eq_left (by omega)]
      exact Nat.cast_sub (by omega)
    · rw [ite_eq_right h,ite_eq_right (by omega)]
  simp_rw [he]
  have hh := sum_interval_distance_rectangle ((k : ℕ)+1) (q-(k : ℕ))
  rw [←hn] at hh
  have hk : (k : ℕ)≤q := by omega
  rw [Nat.cast_add,Nat.cast_one,Nat.cast_sub hk] at hh
  nlinarith [hh]

end KLS.ConstantReduction
end
