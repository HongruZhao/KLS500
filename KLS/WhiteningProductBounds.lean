import KLS.QuantitativeWhiteningNorm

open Matrix Set Metric InnerProductSpace
open scoped Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma norm_matrixAction_mul_le (A B : Matrix (Fin n) (Fin n) ℝ) :
    ‖matrixAction (A * B)‖ ≤ ‖matrixAction A‖ * ‖matrixAction B‖ := by
  have he : matrixAction (A * B) = (matrixAction A).comp (matrixAction B) := by
    apply ContinuousLinearMap.ext
    intro x
    exact MomentMap.matrixAction_mul_apply A B x
  rw [he]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- The actual ordered product of the successive whitening matrices. -/
def whiteningProduct (A : ℕ → Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | j + 1 => whiteningProduct A j * inverseSqrtMatrix (A j)

lemma norm_whiteningProduct_le_exp_sum
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {η : ℕ → ℝ}
    (hA : ∀ j, (A j).PosDef) (hη : ∀ j, 0 ≤ η j) (hηhalf : ∀ j, η j ≤ 1 / 2)
    (hclose : ∀ j, ‖matrixAction (A j - 1)‖ ≤ η j) (k : ℕ) :
    ‖matrixAction (whiteningProduct A k)‖ ≤ Real.exp (2 * ∑ j ∈ Finset.range k, η j) := by
  induction k with
  | zero => simpa only [whiteningProduct, Finset.range_zero, Finset.sum_empty, mul_zero, Real.exp_zero] using
      norm_matrixAction_one_le n
  | succ k ih =>
      have hb := norm_inverseSqrtMatrix_action_le (hA k) (hη k) (hηhalf k) (hclose k)
      have hexp : 1 + 2 * η k ≤ Real.exp (2 * η k) := by
        simpa only [add_comm] using Real.add_one_le_exp (2 * η k)
      calc
        _ ≤ ‖matrixAction (whiteningProduct A k)‖ * ‖matrixAction (inverseSqrtMatrix (A k))‖ :=
          norm_matrixAction_mul_le _ _
        _ ≤ Real.exp (2 * ∑ j ∈ Finset.range k, η j) * Real.exp (2 * η k) :=
          mul_le_mul ih (hb.trans hexp) (norm_nonneg _) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add, Finset.sum_range_succ]; congr 1; ring

lemma norm_whiteningProduct_inverse_le_exp_sum
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {η : ℕ → ℝ}
    (hA : ∀ j, (A j).PosDef) (hη : ∀ j, 0 ≤ η j)
    (hclose : ∀ j, ‖matrixAction (A j - 1)‖ ≤ η j) (k : ℕ) :
    ‖matrixAction ((whiteningProduct A k)⁻¹)‖ ≤ Real.exp (∑ j ∈ Finset.range k, η j) := by
  induction k with
  | zero => simpa only [whiteningProduct, inv_one, Finset.range_zero, Finset.sum_empty, Real.exp_zero] using
      norm_matrixAction_one_le n
  | succ k ih =>
      have hb := norm_inverse_inverseSqrtMatrix_action_le (hA k) (hη k) (hclose k)
      have hexp : 1 + η k ≤ Real.exp (η k) := by simpa only [add_comm] using Real.add_one_le_exp (η k)
      rw [whiteningProduct, Matrix.mul_inv_rev]
      calc
        _ ≤ ‖matrixAction ((inverseSqrtMatrix (A k))⁻¹)‖ *
            ‖matrixAction ((whiteningProduct A k)⁻¹)‖ := norm_matrixAction_mul_le _ _
        _ ≤ Real.exp (η k) * Real.exp (∑ j ∈ Finset.range k, η j) :=
          mul_le_mul (hb.trans hexp) ih (norm_nonneg _) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add, Finset.sum_range_succ]; congr 1; ring

/-- Geometrically decaying Hessian increments keep every actual normalization
product and its inverse uniformly bounded. -/
theorem whiteningProduct_uniform_bounds
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {Q ε β : ℝ}
    (hA : ∀ j, (A j).PosDef) (hQ : 0 ≤ Q) (hε : 0 ≤ ε)
    (hβ : 0 ≤ β) (hβone : β < 1) (hsmall : Q * ε ≤ 1 / 2)
    (hclose : ∀ j, ‖matrixAction (A j - 1)‖ ≤ Q * ε * β ^ j) (k : ℕ) :
    ‖matrixAction (whiteningProduct A k)‖ ≤ Real.exp (2 * Q * ε / (1 - β)) ∧
      ‖matrixAction ((whiteningProduct A k)⁻¹)‖ ≤ Real.exp (Q * ε / (1 - β)) := by
  have hge : ∀ j, 0 ≤ Q * ε * β ^ j := fun _ => by positivity
  have hhalf : ∀ j, Q * ε * β ^ j ≤ 1 / 2 := fun j =>
    (mul_le_of_le_one_right (mul_nonneg hQ hε) (pow_le_one₀ hβ hβone.le)).trans hsmall
  have hsum : (∑ j ∈ Finset.range k, Q * ε * β ^ j) ≤ Q * ε / (1 - β) := by
    rw [← Finset.mul_sum]
    have hh := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hβ hβone
    simp only [Nat.Ico_zero_eq_range, pow_zero] at hh
    have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hQ hε)
    simpa only [mul_one_div] using hm
  constructor
  · apply (norm_whiteningProduct_le_exp_sum hA hge hhalf hclose k).trans
    apply Real.exp_le_exp.mpr
    convert mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2) using 1
    ring
  · exact (norm_whiteningProduct_inverse_le_exp_sum hA hge hclose k).trans (Real.exp_le_exp.mpr hsum)

end KLS
end
