import KLS.DefinitionBridges

/-!
# A conditional third-cumulant estimate

The quadratic variance estimate is an explicit hypothesis in this module.
It is not proved here, declared as an axiom, or inferred from log-concavity.
The argument below isolates the finite-dimensional covariance calculation
needed by the BKL route, including its moment-integrability requirements.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace KLS

/-- Cauchy--Schwarz for covariance, proved from positivity of variance of
every real linear combination. Both square-integrability hypotheses are
explicit. -/
theorem covariance_sq_le_variance_mul_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    covariance f g μ ^ 2 ≤ ProbabilityTheory.variance f μ *
      ProbabilityTheory.variance g μ := by
  have hpoly : ∀ t : ℝ, 0 ≤ ProbabilityTheory.variance f μ * (t * t) +
      (2 * covariance f g μ) * t + ProbabilityTheory.variance g μ := by
    intro t
    have hnonneg := ProbabilityTheory.variance_nonneg (fun x => t * f x + g x) μ
    rw [ProbabilityTheory.variance_fun_add (hf.const_mul t) hg,
      ProbabilityTheory.variance_const_mul, covariance_const_mul_left] at hnonneg
    nlinarith
  have hd := discrim_le_zero hpoly
  simp only [discrim] at hd
  nlinarith

/-- The real Euclidean projection written as a finite coordinate sum. -/
theorem inner_eq_coordinate_sum {n : ℕ} (x u : Space n) :
    inner ℝ x u = ∑ i, u i * x i := by
  simp [PiLp.inner_apply, RCLike.inner_apply]

theorem IsIsotropic.memLp_inner {n : ℕ} {μ : Measure (Space n)}
    (hμ : IsIsotropic μ) (u : Space n) :
    MemLp (fun x : Space n => inner ℝ x u) 2 μ := by
  simp_rw [inner_eq_coordinate_sum]
  exact memLp_finsetSum Finset.univ (fun i _ => (hμ.memLp_coordinate i).const_mul (u i))

theorem IsIsotropic.integral_inner {n : ℕ} {μ : Measure (Space n)}
    (hμ : IsIsotropic μ) (u : Space n) :
    (∫ x : Space n, inner ℝ x u ∂μ) = 0 := by
  simp_rw [inner_eq_coordinate_sum]
  rw [integral_finsetSum Finset.univ
    (fun i _ => (hμ.integrable_coordinate i).const_mul (u i))]
  simp [integral_const_mul, hμ.integral_coordinate]

theorem IsIsotropic.integral_coordinate_mul {n : ℕ} {μ : Measure (Space n)}
    (hμ : IsIsotropic μ) (i j : Fin n) :
    (∫ x : Space n, x i * x j ∂μ) = if i = j then 1 else 0 := by
  have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hμ.2.2.2
  simpa [secondMomentMatrix, Matrix.one_apply] using hij

theorem IsIsotropic.integral_inner_sq {n : ℕ} {μ : Measure (Space n)}
    (hμ : IsIsotropic μ) (u : Space n) :
    (∫ x : Space n, (inner ℝ x u) ^ 2 ∂μ) = ‖u‖ ^ 2 := by
  have hexpand (x : Space n) : (inner ℝ x u) ^ 2 =
      ∑ i, ∑ j, (u i * u j) * (x i * x j) := by
    rw [inner_eq_coordinate_sum]
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun j _ => (hμ.2.2.1 i j).const_mul (u i * u j)))]
  simp_rw [integral_finsetSum Finset.univ
    (fun j _ => (hμ.2.2.1 _ j).const_mul (u _ * u j)), integral_const_mul,
    hμ.integral_coordinate_mul]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [pow_two]

theorem IsIsotropic.real_variance_inner {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (u : Space n) :
    ProbabilityTheory.variance (fun x : Space n => inner ℝ x u) μ = ‖u‖ ^ 2 := by
  rw [ProbabilityTheory.variance_eq_sub (hμ.memLp_inner u)]
  change (∫ x : Space n, (inner ℝ x u) ^ 2 ∂μ) -
    (∫ x : Space n, inner ℝ x u ∂μ) ^ 2 = _
  rw [hμ.integral_inner_sq, hμ.integral_inner]
  simp

/-- The covariance bound against any square-integrable scalar function.
Centering the second function is automatic because isotropic projections
have zero mean. -/
theorem IsIsotropic.integral_inner_mul_sq_le {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (u : Space n)
    {g : Space n → ℝ} (hg : MemLp g 2 μ) :
    (∫ x, inner ℝ x u * g x ∂μ) ^ 2 ≤
      ‖u‖ ^ 2 * ProbabilityTheory.variance g μ := by
  have h := covariance_sq_le_variance_mul_variance (hμ.memLp_inner u) hg
  rw [covariance_eq_sub (hμ.memLp_inner u) hg, hμ.integral_inner,
    hμ.real_variance_inner] at h
  simpa only [zero_mul, sub_zero, Pi.mul_apply] using h

/-- The scalar quadratic form of a real matrix, without a symmetry assumption
in the definition. -/
def matrixQuadratic {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, M i j * x i * x j

/-- Squared Frobenius norm in finite coordinates. -/
def matrixFrobeniusSq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j) ^ 2

/-- The exact unresolved quadratic input for this conditional implication.
Square-integrability is included before the real variance is used. -/
def QuadraticVarianceEight {n : ℕ} (μ : Measure (Space n)) : Prop :=
  ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsSymm →
    MemLp (matrixQuadratic M) 2 μ ∧
      ProbabilityTheory.variance (matrixQuadratic M) μ ≤ 8 * matrixFrobeniusSq M

/-- The directional third-moment matrix. Under isotropy it is the directional
third cumulant; its integrability is established below from the quadratic
input, before its entries are used in linearity of integration. -/
def thirdCumulantMatrix {n : ℕ} (μ : Measure (Space n)) (u : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ x, inner ℝ x u * x i * x j ∂μ

theorem matrixQuadratic_one {n : ℕ} (x : Space n) :
    matrixQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [matrixQuadratic, Matrix.one_apply, pow_two]

theorem QuadraticVarianceEight.memLp_coordinate_mul {n : ℕ} {μ : Measure (Space n)}
    (hQ : QuadraticVarianceEight μ) (i j : Fin n) :
    MemLp (fun x : Space n => x i * x j) 2 μ := by
  have hnorm : MemLp (fun x : Space n => ‖x‖ ^ 2) 2 μ := by
    have hfun : matrixQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) =
        (fun x : Space n => ‖x‖ ^ 2) := funext matrixQuadratic_one
    rw [← hfun]
    exact (hQ 1 Matrix.isSymm_one).1
  apply hnorm.mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun x => by
    rw [norm_mul, pow_two]
    exact mul_le_mul (PiLp.norm_apply_le x i) (PiLp.norm_apply_le x j)
      (norm_nonneg _) (norm_nonneg _)

theorem thirdCumulantMatrix_isSymm {n : ℕ} (μ : Measure (Space n)) (u : Space n) :
    (thirdCumulantMatrix μ u).IsSymm := by
  ext i j
  change (∫ x, inner ℝ x u * x j * x i ∂μ) =
    (∫ x, inner ℝ x u * x i * x j ∂μ)
  congr 1
  funext x
  ring

theorem IsIsotropic.integrable_thirdMoment {n : ℕ} {μ : Measure (Space n)}
    (hμ : IsIsotropic μ) (hQ : QuadraticVarianceEight μ) (u : Space n)
    (i j : Fin n) : Integrable (fun x : Space n => inner ℝ x u * x i * x j) μ := by
  convert (hμ.memLp_inner u).integrable_mul (hQ.memLp_coordinate_mul i j) using 1
  funext x
  simp only [Pi.mul_apply]
  ring

/-- Self-pairing the third-moment matrix with its quadratic form yields its
squared Frobenius norm. Every summand is integrable by the preceding lemma. -/
theorem IsIsotropic.thirdCumulant_self_pairing {n : ℕ} {μ : Measure (Space n)}
    (hμ : IsIsotropic μ) (hQ : QuadraticVarianceEight μ) (u : Space n) :
    (∫ x, inner ℝ x u * matrixQuadratic (thirdCumulantMatrix μ u) x ∂μ) =
      matrixFrobeniusSq (thirdCumulantMatrix μ u) := by
  have hexpand (x : Space n) :
      inner ℝ x u * matrixQuadratic (thirdCumulantMatrix μ u) x =
        ∑ i, ∑ j, thirdCumulantMatrix μ u i j * (inner ℝ x u * x i * x j) := by
    simp only [matrixQuadratic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun j _ => (hμ.integrable_thirdMoment hQ u i j).const_mul
      (thirdCumulantMatrix μ u i j)))]
  unfold matrixFrobeniusSq
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ
    (fun j _ => (hμ.integrable_thirdMoment hQ u i j).const_mul
      (thirdCumulantMatrix μ u i j))]
  simp only [integral_const_mul, thirdCumulantMatrix, pow_two]

/-- Conditional BKL third-cumulant estimate. The exact quadratic variance
estimate is explicitly assumed; no log-concavity or KLS bound is smuggled into
the conclusion. -/
theorem IsIsotropic.thirdCumulant_frobeniusSq_le {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (hQ : QuadraticVarianceEight μ) (u : Space n) :
    matrixFrobeniusSq (thirdCumulantMatrix μ u) ≤ 8 * ‖u‖ ^ 2 := by
  obtain ⟨hT, hvar⟩ := hQ (thirdCumulantMatrix μ u) (thirdCumulantMatrix_isSymm μ u)
  have hcs := hμ.integral_inner_mul_sq_le u hT
  rw [hμ.thirdCumulant_self_pairing hQ u] at hcs
  have hbound := hcs.trans (mul_le_mul_of_nonneg_left hvar (sq_nonneg ‖u‖))
  have hS : 0 ≤ matrixFrobeniusSq (thirdCumulantMatrix μ u) := by
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  nlinarith [sq_nonneg ‖u‖]

end KLS
end

#print axioms KLS.covariance_sq_le_variance_mul_variance
#print axioms KLS.IsIsotropic.integral_inner_sq
#print axioms KLS.IsIsotropic.integral_inner_mul_sq_le
#print axioms KLS.IsIsotropic.integrable_thirdMoment
#print axioms KLS.IsIsotropic.thirdCumulant_self_pairing
#print axioms KLS.IsIsotropic.thirdCumulant_frobeniusSq_le
