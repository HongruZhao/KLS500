import KLS.IntegratedEnergyInfinite

/-! The full quadratic-variance estimate implies the literal normalized
third-cumulant matrix inequality by exact finite coordinate contractions. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
open KLS.TensorEnergy
variable {n : ℕ} {μ : Measure (Space n)}

theorem thirdCumulantMatrix_coordinate (k i j : Fin n) :
    thirdCumulantMatrix μ (EuclideanSpace.single k 1) i j = ∫ x, x k * x i * x j ∂μ := by
  unfold thirdCumulantMatrix
  congr 1
  funext x
  simp [inner_eq_coordinate_sum]

theorem IsIsotropic.thirdCumulantMatrix_coordinate_mulVec
    (hμ : IsIsotropic μ) (hQ : QuadraticVarianceEight μ)
    (u : Space n) (k i : Fin n) :
    (thirdCumulantMatrix μ (EuclideanSpace.single k 1) *ᵥ u.ofLp) i =
      thirdCumulantMatrix μ u i k := by
  change (∑ j, thirdCumulantMatrix μ (EuclideanSpace.single k 1) i j * u j) = _
  have hi (j : Fin n) : Integrable (fun x : Space n => (x k * x i * x j) * u j) μ := by
    have h := (hμ.integrable_thirdMoment hQ (EuclideanSpace.single k 1) i j).mul_const (u j)
    simpa only [inner_eq_coordinate_sum, PiLp.single_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h
  simp_rw [thirdCumulantMatrix_coordinate, ← integral_mul_const]
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  unfold thirdCumulantMatrix
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [inner_eq_coordinate_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem IsIsotropic.thirdCumulantMatrix_square_contraction
    (hμ : IsIsotropic μ) (hQ : QuadraticVarianceEight μ) (u : Space n) :
    u.ofLp ⬝ᵥ ((∑ k, thirdCumulantMatrix μ (EuclideanSpace.single k 1) *
      thirdCumulantMatrix μ (EuclideanSpace.single k 1)) *ᵥ u.ofLp) =
      matrixFrobeniusSq (thirdCumulantMatrix μ u) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  simp_rw [dotProduct_matrix_square _ (thirdCumulantMatrix_isSymm _ _).eq,
    dotProduct, hμ.thirdCumulantMatrix_coordinate_mulVec hQ]
  rw [Finset.sum_comm]
  simp only [matrixFrobeniusSq, pow_two]

variable [IsProbabilityMeasure μ]

/-- The matrix estimate is proved from the exact full quadratic hypothesis;
no logarithmic-concavity conclusion is inserted into that hypothesis. -/
theorem IsIsotropic.thirdCumulantMatrix_seed_eight
    (hμ : IsIsotropic μ) (hQ : QuadraticVarianceEight μ) :
    ((8 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      ∑ k, thirdCumulantMatrix μ (EuclideanSpace.single k 1) *
        thirdCumulantMatrix μ (EuclideanSpace.single k 1)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (8 • (1 : Matrix (Fin n) (Fin n) ℝ) - ∑ k,
      thirdCumulantMatrix μ (EuclideanSpace.single k 1) *
        thirdCumulantMatrix μ (EuclideanSpace.single k 1)).conjTranspose = _
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_sum, Matrix.transpose_mul,
      (thirdCumulantMatrix_isSymm _ _).eq]
  · intro v
    let u : Space n := WithLp.toLp 2 v
    have hb := hμ.thirdCumulant_frobeniusSq_le hQ u
    have hc := hμ.thirdCumulantMatrix_square_contraction hQ u
    change v ⬝ᵥ ((∑ k, thirdCumulantMatrix μ (EuclideanSpace.single k 1) *
      thirdCumulantMatrix μ (EuclideanSpace.single k 1)) *ᵥ v) = _ at hc
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [hc]
    have hu : ‖u‖^2 = v ⬝ᵥ v := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [u, dotProduct, pow_two]
    rw [hu] at hb
    linarith

end KLS
end
