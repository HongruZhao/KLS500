import KLS.MatrixOperatorEntryBound

open Matrix Set Metric InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma centeredQuadratic_identity_add_smul (H : Matrix (Fin n) (Fin n) ℝ)
    (c p g : Space n) (d a ε : ℝ) (x : Space n) :
    centeredQuadratic (1 + ε • H) c (p + ε • g) (d + ε * a) x =
      centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) c p d x +
        ε * centeredQuadratic H c g a x := by
  simp only [centeredQuadratic, matrixAction_add_matrices, matrixAction_smul_scalar,
    inner_add_left, real_inner_smul_left, inner_add_right, inner_smul_right]
  ring

lemma abs_sub_corrected_quadratic_le {H : Matrix (Fin n) (Fin n) ℝ}
    {f : Space n → ℝ} {c p g x : Space n} {d a ε s η T : ℝ}
    (hε : 0 ≤ ε) (hs : |s| ≤ T)
    (happrox : |f x - centeredQuadratic H c g a x| ≤ η * ‖x - c‖ ^ 2) :
    |centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) c p d x + ε * f x -
      centeredQuadratic (1 + ε • H + s • (1 : Matrix (Fin n) (Fin n) ℝ))
        c (p + ε • g) (d + ε * a) x| ≤ (ε * η + T / 2) * ‖x - c‖ ^ 2 := by
  have hshift := centeredQuadratic_add_scalar_one_difference (1 + ε • H) s
    c (p + ε • g) (d + ε * a) x
  rw [centeredQuadratic_identity_add_smul] at hshift
  have he : centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) c p d x + ε * f x -
      centeredQuadratic (1 + ε • H + s • (1 : Matrix (Fin n) (Fin n) ℝ))
        c (p + ε • g) (d + ε * a) x =
      ε * (f x - centeredQuadratic H c g a x) - s / 2 * ‖x-c‖ ^ 2 := by
    linarith
  rw [he]
  calc
    _ ≤ |ε * (f x - centeredQuadratic H c g a x)| + |s / 2 * ‖x-c‖ ^ 2| := abs_sub _ _
    _ = ε * |f x - centeredQuadratic H c g a x| + |s| / 2 * ‖x-c‖ ^ 2 := by
      rw [abs_mul, abs_of_nonneg hε, abs_mul, abs_div, abs_sq]
      norm_num
    _ ≤ ε * (η * ‖x-c‖ ^ 2) + T / 2 * ‖x-c‖ ^ 2 := by gcongr
    _ = (ε * η + T / 2) * ‖x-c‖ ^ 2 := by ring

/-- A genuine determinant-one positive-definite quadratic approximating the
identity quadratic plus the original viscosity-harmonic correction. -/
theorem IsViscosityHarmonicOn.exists_det_one_quadratic_approximation
    (hn : 0 < n) {U : Set (Space n)} {f : Space n → ℝ} (hf : IsViscosityHarmonicOn U f)
    (hU : IsOpen U) {c : Space n} {R B η ε : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hball : closedBall c R ⊆ U) (hb : ∀ y ∈ closedBall c R, f y ^ 2 ≤ B)
    (hε : 0 < ε)
    (hεsmall : 2 * harmonicTaylorHessianBound n R B * ε ≤
      1 / (2 * nonlinearComparisonConstant n)) (p : Space n) (d : ℝ) :
    ∃ s : ℝ, |s| ≤ 4 * nonlinearComparisonConstant n *
        harmonicTaylorHessianBound n R B ^ 2 * ε ^ 2 ∧
      (1 + ε • coordinateHessian f c + s • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
      (1 + ε • coordinateHessian f c + s • (1 : Matrix (Fin n) (Fin n) ℝ)).det = 1 ∧
      ∀ x ∈ closedBall c (harmonicApproximationRadius n R B η),
        |centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) c p d x + ε * f x -
          centeredQuadratic (1 + ε • coordinateHessian f c + s • (1 : Matrix (Fin n) (Fin n) ℝ))
            c (p + ε • gradient f c) (d + ε * f c) x| ≤
          (ε * η + 2 * nonlinearComparisonConstant n *
            harmonicTaylorHessianBound n R B ^ 2 * ε ^ 2) * ‖x-c‖ ^ 2 := by
  obtain ⟨hH,htr,happrox⟩ := hf.quadratic_approximation hU hR hη hball hb
  obtain ⟨s,hs,hpos,hdet⟩ := exists_det_one_scalar_correction_of_norm_le hn hH htr
    (harmonicTaylorHessianBound_pos n R B) (hf.norm_taylor_hessian_le hU hR hball hb)
    hε hεsmall
  refine ⟨s,hs,hpos,hdet,?_⟩
  intro x hx
  have h := abs_sub_corrected_quadratic_le (p := p) (d := d) hε.le hs (happrox x hx)
  convert h using 1
  ring


/-- With explicit smallness of epsilon, the determinant correction preserves
the prescribed quadratic improvement for the harmonic perturbation. -/
theorem IsViscosityHarmonicOn.exists_det_one_quadratic_small_error
    (hn : 0 < n) {U : Set (Space n)} {f : Space n → ℝ} (hf : IsViscosityHarmonicOn U f)
    (hU : IsOpen U) {c : Space n} {R B η ε : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hball : closedBall c R ⊆ U) (hb : ∀ y ∈ closedBall c R, f y ^ 2 ≤ B)
    (hε : 0 < ε)
    (hεsmall : 2 * harmonicTaylorHessianBound n R B * ε ≤
      1 / (2 * nonlinearComparisonConstant n))
    (hcorrection : 2 * nonlinearComparisonConstant n *
      harmonicTaylorHessianBound n R B ^ 2 * ε ≤ η) (p : Space n) (d : ℝ) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef ∧ A.det = 1 ∧
      ∀ x ∈ closedBall c (harmonicApproximationRadius n R B η),
        |centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) c p d x + ε * f x -
          centeredQuadratic A c (p + ε • gradient f c) (d + ε * f c) x| ≤
          2 * ε * η * ‖x-c‖ ^ 2 := by
  obtain ⟨s, -, hpos, hdet, hbnd⟩ := hf.exists_det_one_quadratic_approximation hn hU hR hη
    hball hb hε hεsmall p d
  refine ⟨_, hpos, hdet, ?_⟩
  intro x hx
  apply (hbnd x hx).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_right hcorrection hε.le
  nlinarith

end KLS
end
