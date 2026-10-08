import KLS.ThirdCumulant

/-! Explicit comparison between the port's Pi supremum norm and KLS Euclidean space. -/
open MeasureTheory
open scoped BigOperators
namespace KLS.StandardLocalization

abbrev toSpace {n : ℕ} (c : Fin n → ℝ) : Space n := WithLp.toLp 2 c
abbrev fromSpace {n : ℕ} (x : Space n) : Fin n → ℝ := WithLp.ofLp x

theorem continuous_toSpace {n : ℕ} : Continuous (toSpace (n := n)) := PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)

theorem continuous_fromSpace {n : ℕ} : Continuous (fromSpace (n := n)) := PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)

theorem norm_fromSpace_le {n : ℕ} (x : Space n) : ‖fromSpace x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  exact fun i => PiLp.norm_apply_le x i

theorem norm_toSpace_le {n : ℕ} (c : Fin n → ℝ) :
    ‖toSpace c‖ ≤ Real.sqrt (n : ℝ) * ‖c‖ := by
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i, ‖toSpace c i‖ ^ 2)
      ≤ Real.sqrt (∑ _i : Fin n, ‖c‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm c i) 2
    _ = Real.sqrt (n : ℝ) * ‖c‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (norm_nonneg c)]

theorem inner_toSpace_eq {n : ℕ} (c : Fin n → ℝ) (x : Space n) :
    inner ℝ (toSpace c) x = ∑ i, c i * x i := by
  rw [KLS.inner_eq_coordinate_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

end KLS.StandardLocalization
#print axioms KLS.StandardLocalization.norm_fromSpace_le
#print axioms KLS.StandardLocalization.norm_toSpace_le
