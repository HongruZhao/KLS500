import KLS.ThirdCumulant
import KLS.ProbabilityMeanCentering
import KLS.PoincareGraphLimit

open MeasureTheory ProbabilityTheory InnerProductSpace Filter Matrix
open scoped BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual covariance of an observable with every coordinate product. -/
def quadraticCovarianceMatrix (μ : Measure (Space n)) (f : Space n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => covariance f (fun x => x i * x j) μ

theorem quadraticCovarianceMatrix_isSymm (μ : Measure (Space n)) (f : Space n → ℝ) :
    (quadraticCovarianceMatrix μ f).IsSymm := by
  ext i j
  change covariance f (fun x => x j * x i) μ = covariance f (fun x => x i * x j) μ
  simp only [mul_comm]

theorem quadraticCovarianceMatrix_congr_ae {μ : Measure (Space n)}
    {f g : Space n → ℝ} (hfg : f =ᵐ[μ] g) :
    quadraticCovarianceMatrix μ f = quadraticCovarianceMatrix μ g := by
  ext i j
  unfold quadraticCovarianceMatrix covariance
  rw [integral_congr_ae hfg]
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

theorem memLp_matrixQuadratic_of_coordinateProducts {μ : Measure (Space n)}
    (hcoord : ∀ i j : Fin n, MemLp (fun x => x i * x j) 2 μ)
    (M : Matrix (Fin n) (Fin n) ℝ) : MemLp (matrixQuadratic M) 2 μ := by
  have he : matrixQuadratic M = fun x => ∑ i, ∑ j, M i j * (x i * x j) := by
    funext x
    unfold matrixQuadratic
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact memLp_finsetSum Finset.univ (fun i _ => memLp_finsetSum Finset.univ
    (fun j _ => (hcoord i j).const_mul (M i j)))

/-- The genuine matrix Frobenius duality identity, including every symmetric
off-diagonal entry without an additional symmetrization factor. -/
theorem covariance_matrixQuadratic_eq_pairing {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hcoord : ∀ i j : Fin n, MemLp (fun x => x i * x j) 2 μ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    covariance f (matrixQuadratic M) μ = ∑ i, ∑ j, M i j * quadraticCovarianceMatrix μ f i j := by
  have he : matrixQuadratic M = fun x => ∑ i, ∑ j, M i j * (x i * x j) := by
    funext x
    unfold matrixQuadratic
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  rw [covariance_fun_sum_right
    (fun i => memLp_finsetSum Finset.univ (fun j _ => (hcoord i j).const_mul (M i j))) hf]
  apply Finset.sum_congr rfl
  intro i _
  rw [covariance_fun_sum_right (fun j => (hcoord i j).const_mul (M i j)) hf]
  simp only [covariance_const_mul_right, quadraticCovarianceMatrix]

lemma matrix_frobenius_pairing_sq_le (M A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, M i j * A i j) ^ 2 ≤ matrixFrobeniusSq M * matrixFrobeniusSq A := by
  simpa only [Fintype.sum_prod_type, matrixFrobeniusSq] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
      (fun p => M p.1 p.2) (fun p => A p.1 p.2)

/-- Self-pairing the symmetric covariance matrix gives the sharp operator
bound from the actual quadratic variance premise. -/
theorem QuadraticVarianceEight.quadraticCovariance_frobeniusSq_le_variance
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hQ : QuadraticVarianceEight μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    matrixFrobeniusSq (quadraticCovarianceMatrix μ f) ≤ 8 * ProbabilityTheory.variance f μ := by
  let A := quadraticCovarianceMatrix μ f
  obtain ⟨hA, hv⟩ := hQ A (quadraticCovarianceMatrix_isSymm μ f)
  have hs := covariance_sq_le_variance_mul_variance hf hA
  rw [covariance_matrixQuadratic_eq_pairing hf hQ.memLp_coordinate_mul] at hs
  have he : (∑ i, ∑ j, A i j * quadraticCovarianceMatrix μ f i j) = matrixFrobeniusSq A := by
    simp only [A, matrixFrobeniusSq, pow_two]
  rw [he] at hs
  have hb := hs.trans (mul_le_mul_of_nonneg_left hv (ProbabilityTheory.variance_nonneg f μ))
  have hS : 0 ≤ matrixFrobeniusSq A :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  change matrixFrobeniusSq A ≤ _
  nlinarith [ProbabilityTheory.variance_nonneg f μ]

theorem QuadraticVarianceEight.quadraticCovariance_frobeniusSq_le_norm
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hQ : QuadraticVarianceEight μ)
    (f : Lp ℝ 2 μ) : matrixFrobeniusSq (quadraticCovarianceMatrix μ f) ≤ 8 * ‖f‖ ^ 2 := by
  have hh := hQ.quadraticCovariance_frobeniusSq_le_variance (Lp.memLp f)
  have hn := CenteredL2.norm_center_sq μ f
  rw [CenteredL2.norm_center_sq_eq_variance] at hn
  nlinarith [sq_nonneg (∫ x, f x ∂μ)]

/-- The converse uses an actual centered quadratic test in L2. Its true
variance is its squared L2 norm, so no mean term or dimension loss remains. -/
theorem quadraticVarianceEight_of_quadraticCovariance_norm_bound
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hcoord : ∀ i j : Fin n, MemLp (fun x => x i * x j) 2 μ)
    (hbound : ∀ f : Lp ℝ 2 μ,
      matrixFrobeniusSq (quadraticCovarianceMatrix μ f) ≤ 8 * ‖f‖ ^ 2) :
    QuadraticVarianceEight μ := by
  intro M _hM
  have hq := memLp_matrixQuadratic_of_coordinateProducts hcoord M
  refine ⟨hq, ?_⟩
  let f := CenteredL2.center μ (hq.toLp (matrixQuadratic M))
  have hn : ‖f‖ ^ 2 = ProbabilityTheory.variance (matrixQuadratic M) μ :=
    norm_center_toLp_sq_eq_variance hq
  have hce : (f : Space n → ℝ) =ᵐ[μ]
      fun x => matrixQuadratic M x - ∫ y, matrixQuadratic M y ∂μ := by
    have hh := CenteredL2.center_ae μ (hq.toLp (matrixQuadratic M))
    rw [integral_congr_ae hq.coeFn_toLp] at hh
    exact hh.trans (hq.coeFn_toLp.sub (EventuallyEq.rfl))
  have hA : quadraticCovarianceMatrix μ f = quadraticCovarianceMatrix μ (matrixQuadratic M) := by
    rw [quadraticCovarianceMatrix_congr_ae hce]
    ext i j
    exact covariance_sub_const_left (hq.integrable (by norm_num)) _
  have hb := hbound f
  rw [hn, hA] at hb
  have hpair := covariance_matrixQuadratic_eq_pairing hq hcoord M
  rw [covariance_self hq.aemeasurable] at hpair
  have hcs := matrix_frobenius_pairing_sq_le M (quadraticCovarianceMatrix μ (matrixQuadratic M))
  rw [← hpair] at hcs
  have hM0 : 0 ≤ matrixFrobeniusSq M :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hfin := hcs.trans (mul_le_mul_of_nonneg_left hb hM0)
  nlinarith [ProbabilityTheory.variance_nonneg (matrixQuadratic M) μ]

end KLS
end
