import KLS.SmoothBarrierStability
import KLS.DeterminantQuadraticRemainder

/-! Actual matrix positivity and determinant gaps for a bounded trace-zero
perturbation of the identity. These are estimates on smooth comparison
functions, not assumptions about a Hessian of the weak solution. -/
open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma elementwise_matrix_norm_le_matrixAction_norm (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖A‖ ≤ ‖matrixAction A‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
  intro i j
  have h := (PiLp.norm_apply_le (matrixAction A (EuclideanSpace.single j 1)) i).trans
    ((matrixAction A).le_opNorm (EuclideanSpace.single j 1))
  simpa [matrixAction_apply, PiLp.single_apply] using h

lemma posDef_one_add_smul_of_matrixAction_norm_le_half
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hAnorm : ‖matrixAction A‖ ≤ 1 / 2) {t : ℝ} (ht : |t| ≤ 1) :
    (1 + t • A).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_one.add
      ((Matrix.isHermitian_iff_isSymm.mpr hA).smul (IsSelfAdjoint.all t))
  intro w hw
  let x : Space n := WithLp.toLp 2 w
  have hx : x ≠ 0 := by
    intro hz
    apply hw
    ext i
    exact congrArg (fun v : Space n => v i) hz
  have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hi : |inner ℝ x (matrixAction A x)| ≤ ‖x‖ ^ 2 / 2 := by
    calc
      _ ≤ ‖x‖ * ‖matrixAction A x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖matrixAction A‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left ((matrixAction A).le_opNorm _) (norm_nonneg _)
      _ ≤ ‖x‖ * ((1 / 2) * ‖x‖) := by gcongr
      _ = _ := by ring
  have hti : |t * inner ℝ x (matrixAction A x)| ≤ ‖x‖ ^ 2 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul ht hi (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hpos : 0 < inner ℝ x (matrixAction (1 + t • A) x) := by
    rw [matrixAction_add_matrices, matrixAction_one_apply, matrixAction_smul_scalar,
      inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have hlo := (abs_le.mp hti).1
    linarith
  simpa only [x, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    dotProduct, Matrix.mulVec, matrixAction_apply, star_trivial, mul_comm] using hpos

lemma elementwise_norm_matrix_one_le (n : ℕ) :
    ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 := by
  apply (Matrix.norm_le_iff (by norm_num)).mpr
  intro i j
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

/-- For trace-zero H of bounded norm, scalar shifts of size O(epsilon²)
produce a strict determinant gap around every density within epsilon² of 1. -/
theorem determinant_gaps_of_trace_zero_perturbation
    (hn : 0 < n) {C : ℝ} (hC : 0 < C)
    (hrem : ∀ M : Matrix (Fin n) (Fin n) ℝ, ‖M‖ ≤ 1 →
      ∀ t : ℝ, |t| ≤ 1 → |(1 + t • M).det - 1 - M.trace * t| ≤ C * t ^ 2)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : ‖H‖ ≤ 1 / 2) (htr : H.trace = 0)
    {ε f : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / (2 * (C + 2)))
    (hf : |f - 1| ≤ ε ^ 2) :
    let τ := (C + 2) * ε ^ 2
    (1 + ε • H - τ • (1 : Matrix (Fin n) (Fin n) ℝ)).det < f ∧
      f < (1 + ε • H + τ • (1 : Matrix (Fin n) (Fin n) ℝ)).det := by
  dsimp only
  let a : ℝ := (C + 2) * ε
  have ha : 0 ≤ a := by positivity
  have ha2 : a ≤ 1 / 2 := by
    have hd : 0 < 2 * (C + 2) := by positivity
    have hh := (le_div_iff₀ hd).mp hεsmall
    dsimp [a]
    linarith
  have hε1 : |ε| ≤ 1 := by
    rw [abs_of_pos hε]
    have hCa : ε ≤ a := by dsimp [a]; nlinarith
    linarith
  have hnorm (s : ℝ) (hs : |s| ≤ a) :
      ‖H + s • (1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 := by
    calc
      _ ≤ ‖H‖ + ‖s • (1 : Matrix (Fin n) (Fin n) ℝ)‖ := norm_add_le _ _
      _ = ‖H‖ + |s| * ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 / 2 + a * 1 := by gcongr; exact elementwise_norm_matrix_one_le n
      _ ≤ 1 := by linarith
  have hm := hrem (H + (-a) • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hnorm (-a) (by rw [abs_neg, abs_of_nonneg ha])) ε hε1
  have hp := hrem (H + a • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hnorm a (by rw [abs_of_nonneg ha])) ε hε1
  have htrace (s : ℝ) : (H + s • (1 : Matrix (Fin n) (Fin n) ℝ)).trace = s * n := by
    simp [Matrix.trace_add, Matrix.trace_smul, htr, Matrix.trace_one]
  rw [htrace] at hm hp
  have hmatplus : 1 + ε • (H + a • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      1 + ε • H + ((C + 2) * ε ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    dsimp [a]
    ring
  have hmatminus : 1 + ε • (H + (-a) • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      1 + ε • H - ((C + 2) * ε ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    dsimp [a]
    ring
  rw [hmatplus] at hp
  rw [hmatminus] at hm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hep : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hcε : 0 ≤ (C + 2) * ε ^ 2 := by positivity
  have hnn := mul_le_mul_of_nonneg_right hn1 hcε
  have hmm := (abs_le.mp hm).2
  have hpp := (abs_le.mp hp).1
  have hflo := (abs_le.mp hf).1
  have hfhi := (abs_le.mp hf).2
  dsimp [a] at hmm hpp
  constructor <;> nlinarith

end KLS
end
