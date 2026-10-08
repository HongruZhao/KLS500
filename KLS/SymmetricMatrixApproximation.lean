import KLS.SpectralQuadraticTransport
import KLS.WhitenedCutoffMoments

/-!
# Removing singular quadratic matrices by actual spectral approximation

Zero eigenvalues are replaced by 1/(k+1), leaving every nonzero eigenvalue
unchanged. The matrices remain symmetric, are invertible, and converge to
the original matrix. Actual fourth moments make quadratic variance continuous.
-/

open Matrix Unitary MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

theorem exists_symmetric_invertible_approximation
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    ∃ A : ℕ → Matrix (Fin n) (Fin n) ℝ,
      (∀ k, (A k).IsSymm ∧ (A k).det ≠ 0) ∧ Tendsto A atTop (𝓝 M) := by
  let hH : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hM
  let Q := hH.eigenvectorUnitary
  let e := conjStarAlgAut ℝ _ Q
  let d (k : ℕ) (i : Fin n) :=
    if hH.eigenvalues i = 0 then ((k : ℝ) + 1)⁻¹ else hH.eigenvalues i
  refine ⟨fun k => e (diagonal (d k)), ?_, ?_⟩
  · intro k
    refine ⟨isSymm_unitary_conj_diagonal Q (d k), ?_⟩
    have hdiag : IsUnit (diagonal (d k)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
      apply isUnit_iff_ne_zero.mpr
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      dsimp [d]
      split_ifs with hi
      · positivity
      · exact hi
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (hdiag.map e))
  · have hd : Tendsto d atTop (𝓝 hH.eigenvalues) := by
      apply tendsto_pi_nhds.mpr
      intro i
      by_cases hi : hH.eigenvalues i = 0
      · simp only [d, hi, ↓reduceIte]
        simpa only [Function.comp_def] using tendsto_inv_atTop_zero.comp
          (tendsto_atTop_mono (fun k : ℕ => le_add_of_nonneg_right
            (show (0 : ℝ) ≤ 1 by norm_num)) tendsto_natCast_atTop_atTop)
      · simpa only [d, hi, ↓reduceIte] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => hH.eigenvalues i) atTop _)
    have hdiagCont : Continuous (diagonal : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) := by
      fun_prop
    have hdiag : Tendsto (fun k => diagonal (d k)) atTop (𝓝 (diagonal hH.eigenvalues)) :=
      hdiagCont.continuousAt.tendsto.comp hd
    have he : Continuous e := by
      change Continuous (fun X => (Q : Matrix (Fin n) (Fin n) ℝ) * X * (star Q : Matrix (Fin n) (Fin n) ℝ))
      fun_prop
    have hspec : M = e (diagonal hH.eigenvalues) := by
      simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hH.spectral_theorem
    simpa only [hspec, Function.comp_def] using he.continuousAt.tendsto.comp hdiag

theorem continuous_matrixFrobeniusSq :
    Continuous (matrixFrobeniusSq : Matrix (Fin n) (Fin n) ℝ → ℝ) := by
  unfold matrixFrobeniusSq
  fun_prop

/-- Continuity of actual quadratic variances follows from the finite degree
two and degree four expansions with genuine integrability. -/
theorem measureLogConcave.continuous_quadraticVariance {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) :
    Continuous (fun M : Matrix (Fin n) (Fin n) ℝ =>
      ProbabilityTheory.variance (matrixQuadratic M) μ) := by
  have hm : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ =>
      ∫ x, matrixQuadratic M x ∂μ) := by
    have heq : (fun M : Matrix (Fin n) (Fin n) ℝ => ∫ x, matrixQuadratic M x ∂μ) =
        fun M => ∑ i, ∑ j, M i j * ∫ x : Space n, x i * x j ∂μ :=
      funext hμ.integral_matrixQuadratic_sum
    rw [heq]
    fun_prop
  have hs : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ =>
      ∫ x, matrixQuadratic M x ^ 2 ∂μ) := by
    have heq : (fun M : Matrix (Fin n) (Fin n) ℝ => ∫ x, matrixQuadratic M x ^ 2 ∂μ) =
        fun M => ∑ i, ∑ j, ∑ k, ∑ l, (M i j * M k l) *
          ∫ x : Space n, x i * x j * x k * x l ∂μ :=
      funext hμ.integral_matrixQuadratic_sq_sum
    rw [heq]
    fun_prop
  convert hs.sub (hm.pow 2) using 1
  funext M
  exact ProbabilityTheory.variance_eq_sub (hμ.memLp_two_matrixQuadratic M)

/-- It is sufficient to prove the quadratic estimate for invertible
symmetric matrices; no invertibility condition remains in the conclusion. -/
theorem measureLogConcave.quadraticVarianceEight_of_invertible {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : measureLogConcave μ)
    (hbound : ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsSymm → M.det ≠ 0 →
      ProbabilityTheory.variance (matrixQuadratic M) μ ≤ 8 * matrixFrobeniusSq M) :
    QuadraticVarianceEight μ := by
  intro M hM
  refine ⟨hμ.memLp_two_matrixQuadratic M, ?_⟩
  obtain ⟨A, hA, ht⟩ := exists_symmetric_invertible_approximation M hM
  exact le_of_tendsto_of_tendsto
    (hμ.continuous_quadraticVariance.continuousAt.tendsto.comp ht)
    ((continuous_const.mul continuous_matrixFrobeniusSq).continuousAt.tendsto.comp ht)
    (Eventually.of_forall fun k => hbound (A k) (hA k).1 (hA k).2)

end KLS
end

#print axioms KLS.exists_symmetric_invertible_approximation
#print axioms KLS.measureLogConcave.continuous_quadraticVariance
#print axioms KLS.measureLogConcave.quadraticVarianceEight_of_invertible
