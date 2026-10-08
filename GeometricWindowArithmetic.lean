import WeightedFiniteTaylorWindow

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

theorem sum_fin_pow_rev (M : ℝ) (q : ℕ) :
    (∑ i : Fin q, M ^ (i.rev : ℕ)) = ∑ i : Fin q, M ^ (i : ℕ) := by
  simpa only [Fin.revPerm_apply] using Equiv.sum_comp Fin.revPerm
    (fun i : Fin q => M ^ (i : ℕ))

theorem geometric_window_identity (M : ℝ) (q : ℕ) :
    (M - 1) * (∑ i : Fin q, M ^ (i : ℕ)) = M ^ q - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => M ^ i)]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith

theorem geometric_window_le_power_div {M : ℝ} (hM : 1 < M) (q : ℕ) :
    (∑ i : Fin q, M ^ (i : ℕ)) ≤ M ^ q / (M - 1) := by
  apply (le_div_iff₀ (by linarith : 0 < M-1)).mpr
  have h := geometric_window_identity M q
  nlinarith

theorem geometric_window_le_max {M : ℝ} (hM : 1 ≤ M) (q : ℕ) :
    (∑ i : Fin q, M ^ (i : ℕ)) ≤ (q : ℝ) * M ^ (q - 1) := by
  calc
    _ ≤ ∑ _i : Fin q, M ^ (q - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_right₀ hM (by omega)
    _ = _ := by simp

end KLS.ConstantReduction
end
