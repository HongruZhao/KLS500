import KLS.UniformRecenteredWeightedData

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

lemma centeredQuadratic_add_affine (H : Matrix (Fin n) (Fin n) ℝ)
    (c p q x : Space n) (a b : ℝ) :
    centeredQuadratic H c (p + q) (a + b) x =
      a + inner ℝ p (x - c) + centeredQuadratic H c q b x := by
  simp only [centeredQuadratic, inner_add_left]
  ring

/-- Exact error reconstruction for arbitrary-center, non-unit whitening. -/
lemma whitened_quadratic_error_identity
    {u v : Space n → ℝ} (c p : Space n) (a : ℝ) {r : ℝ} (hr : r ≠ 0)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0)
    (hv : v = quadraticallyRescaledPotential u c p a r ∘ matrixAction B)
    (H : Matrix (Fin n) (Fin n) ℝ) (q : Space n) (b : ℝ) (y : Space n) :
    u (c + r • matrixAction B y) -
      centeredQuadratic (B⁻¹.transpose * H * B⁻¹) c
        (p + r • matrixAction B⁻¹.transpose q) (a + r ^ 2 * b) (c + r • matrixAction B y) =
      r ^ 2 * (v y - centeredQuadratic H 0 q b y) := by
  have hu := quadratic_rescaling_reconstruction u c p a hr (matrixAction B y)
  have hq := centeredQuadratic_frame_scaled hB H q b r y
  have hcenter : centeredQuadratic (B⁻¹.transpose * H * B⁻¹) c
      (r • matrixAction B⁻¹.transpose q) (r ^ 2 * b) (c + r • matrixAction B y) =
      centeredQuadratic (B⁻¹.transpose * H * B⁻¹) 0
        (r • matrixAction B⁻¹.transpose q) (r ^ 2 * b) (r • matrixAction B y) := by
    simp only [centeredQuadratic, add_sub_cancel_left, sub_zero]
  rw [centeredQuadratic_add_affine, hcenter, hq, hu]
  simp only [hv, Function.comp_apply, add_sub_cancel_left, inner_smul_right]
  ring

lemma inverseSqrt_pullback_posDef_det
    {A H : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hH : H.PosDef) (hdet : H.det = 1) :
    ((inverseSqrtMatrix A)⁻¹.transpose * H * (inverseSqrtMatrix A)⁻¹).PosDef ∧
      ((inverseSqrtMatrix A)⁻¹.transpose * H * (inverseSqrtMatrix A)⁻¹).det = A.det := by
  let B := inverseSqrtMatrix A
  have hpsd : (B⁻¹.transpose * H * B⁻¹).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hH.posSemidef.conjTranspose_mul_mul_same B⁻¹
  have heq : (B⁻¹.transpose * H * B⁻¹).det = A.det := by
    have hh := congrArg Matrix.det (inverseSqrtMatrix_inverse_gram hA)
    simp only [Matrix.det_mul, Matrix.det_transpose] at hh ⊢
    rw [hdet, mul_one]
    exact hh
  exact ⟨hpsd.posDef_iff_det_ne_zero.mpr (by rw [heq]; exact hA.det_pos.ne'), heq⟩

/-- A normalized limiting quadratic yields an actual original-coordinate
quadratic with the original central density as its determinant. -/
theorem whitened_quadratic_approximation_on_ball
    {u v : Space n → ℝ} (c p : Space n) (a : ℝ)
    {A H : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hBinv : ‖matrixAction (inverseSqrtMatrix A)⁻¹‖ ≤ 2)
    (hv : v = quadraticallyRescaledPotential u c p a (1 / 4) ∘ matrixAction (inverseSqrtMatrix A))
    {q : Space n} {b D r β : ℝ}
    (hb : ∀ (j : ℕ) (y : Space n), ‖y‖ ≤ r ^ j / 2 →
      |v y - centeredQuadratic H 0 q b y| ≤ D * β ^ j * r ^ (2 * j)) :
    ∀ (j : ℕ) (x : Space n), ‖x - c‖ ≤ r ^ j / 16 →
      |u x - centeredQuadratic ((inverseSqrtMatrix A)⁻¹.transpose * H * (inverseSqrtMatrix A)⁻¹) c
        (p + (1 / 4 : ℝ) • matrixAction (inverseSqrtMatrix A)⁻¹.transpose q)
        (a + (1 / 4 : ℝ) ^ 2 * b) x| ≤ (D / 16) * β ^ j * r ^ (2 * j) := by
  intro j x hx
  let B := inverseSqrtMatrix A
  let y : Space n := (4 : ℝ) • matrixAction B⁻¹ (x - c)
  have hy : ‖y‖ ≤ r ^ j / 2 := by
    have hop := (matrixAction B⁻¹).le_opNorm (x - c)
    have hm := mul_le_mul hBinv hx (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hpoint : c + (1 / 4 : ℝ) • matrixAction B y = x := by
    simp only [y, map_smul, smul_smul]
    rw [matrixAction_cancel_inverse (inverseSqrtMatrix_det_ne_zero_of_posDef hA)]
    norm_num
  have heq := whitened_quadratic_error_identity c p a (by norm_num : (1 / 4 : ℝ) ≠ 0)
    (inverseSqrtMatrix_det_ne_zero_of_posDef hA) hv H q b y
  rw [hpoint] at heq
  rw [heq, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hh := mul_le_mul_of_nonneg_left (hb j y hy) (sq_nonneg (1 / 4 : ℝ))
  exact hh.trans_eq (by ring)

end KLS
end
