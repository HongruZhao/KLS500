import KLS.CorrectedHarmonicQuadratic

open Matrix Set Metric InnerProductSpace
open scoped Topology ContDiff BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma norm_corrected_matrix_sub_one_le
    {H : Matrix (Fin n) (Fin n) ℝ} {ε s B D : ℝ}
    (hε : 0 ≤ ε) (hH : ‖matrixAction H‖ ≤ B) (hs : |s| ≤ D) :
    ‖matrixAction ((1 + ε • H + s • (1 : Matrix (Fin n) (Fin n) ℝ)) - 1)‖ ≤ ε * B + D := by
  have hm : (1 + ε • H + s • (1 : Matrix (Fin n) (Fin n) ℝ)) - 1 =
      ε • H + s • (1 : Matrix (Fin n) (Fin n) ℝ) := by abel
  rw [hm, matrixAction_add_eq, matrixAction_smul_eq, matrixAction_smul_eq]
  calc
    _ ≤ ‖ε • matrixAction H‖ + ‖s • matrixAction (1 : Matrix (Fin n) (Fin n) ℝ)‖ := norm_add_le _ _
    _ = ε * ‖matrixAction H‖ + |s| * ‖matrixAction (1 : Matrix (Fin n) (Fin n) ℝ)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hε]
    _ ≤ ε * B + |s| * 1 := by gcongr; exact norm_matrixAction_one_le n
    _ ≤ ε * B + D := by linarith

/-- The actual harmonic Taylor gradient has a uniform Euclidean norm bound. -/
theorem IsViscosityHarmonicOn.norm_taylor_gradient_le
    {U : Set (Space n)} {f : Space n → ℝ} (hf : IsViscosityHarmonicOn U f)
    (hU : IsOpen U) {c : Space n} {R B : ℝ} (hR : 0 < R)
    (hball : closedBall c R ⊆ U) (hb : ∀ y ∈ closedBall c R, f y ^ 2 ≤ B) :
    ‖gradient f c‖ ≤ n * Real.sqrt ((120 + 8 * n) * B / R ^ 2) := by
  have hg := (hf.taylor_coefficients_sq_le hU hR hball hb).2.1
  calc
    _ ≤ ∑ i, |gradient f c i| := norm_euclidean_le_sum_abs _
    _ ≤ ∑ _ : Fin n, Real.sqrt ((120 + 8 * n) * B / R ^ 2) :=
      Finset.sum_le_sum (fun i _ => Real.abs_le_sqrt (hg i))
    _ = _ := by simp

/-- The determinant-one correction retains a quantitative bound on its
actual Hessian increment, in addition to the quadratic approximation. -/
theorem IsViscosityHarmonicOn.exists_controlled_det_one_quadratic
    (hn : 0 < n) {U : Set (Space n)} {f : Space n → ℝ} (hf : IsViscosityHarmonicOn U f)
    (hU : IsOpen U) {c : Space n} {R B η ε : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hball : closedBall c R ⊆ U) (hb : ∀ y ∈ closedBall c R, f y ^ 2 ≤ B)
    (hε : 0 < ε) (hεone : ε ≤ 1)
    (hεsmall : 2 * harmonicTaylorHessianBound n R B * ε ≤
      1 / (2 * nonlinearComparisonConstant n))
    (hcorrection : 2 * nonlinearComparisonConstant n *
      harmonicTaylorHessianBound n R B ^ 2 * ε ≤ η) (p : Space n) (d : ℝ) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef ∧ A.det = 1 ∧
      ‖matrixAction (A - 1)‖ ≤
        ε * (harmonicTaylorHessianBound n R B +
          4 * nonlinearComparisonConstant n * harmonicTaylorHessianBound n R B ^ 2) ∧
      ∀ x ∈ closedBall c (harmonicApproximationRadius n R B η),
        |centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) c p d x + ε * f x -
          centeredQuadratic A c (p + ε • gradient f c) (d + ε * f c) x| ≤
          2 * ε * η * ‖x-c‖ ^ 2 := by
  obtain ⟨s, hs, hpos, hdet, happ⟩ := hf.exists_det_one_quadratic_approximation hn hU hR hη
    hball hb hε hεsmall p d
  refine ⟨_, hpos, hdet, ?_, ?_⟩
  · have hC : 0 ≤ 4 * nonlinearComparisonConstant n * harmonicTaylorHessianBound n R B ^ 2 := by
      positivity [nonlinearComparisonConstant_gt_two n]
    have hpow : ε ^ 2 ≤ ε := by nlinarith
    have hs' := hs.trans (mul_le_mul_of_nonneg_left hpow hC)
    have hm := norm_corrected_matrix_sub_one_le hε.le
      (hf.norm_taylor_hessian_le hU hR hball hb) hs'
    convert hm using 1
    ring
  · intro x hx
    apply (happ x hx).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have h := mul_le_mul_of_nonneg_right hcorrection hε.le
    nlinarith

end KLS
end
