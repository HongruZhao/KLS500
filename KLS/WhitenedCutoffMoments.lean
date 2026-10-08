import KLS.AffineWhitening

/-!
# Moment convergence for the actual whitened cutoffs

Finite products of affine coordinates are expanded exactly into products of
coordinates and the constant function. Thus convergence follows from the
already proved cutoff integrals and actual matrix/mean limits.
-/

open MeasureTheory ProbabilityTheory Set Filter Matrix Metric
open scoped ENNReal Topology BigOperators

noncomputable section
namespace KLS

def coordinateWithConstant {n : ℕ} : Option (Fin n) → Space n → ℝ
  | none, _ => 1
  | some i, x => x i

theorem continuous_coordinateWithConstant {n : ℕ} (i : Option (Fin n)) :
    Continuous (coordinateWithConstant i) := by
  cases i with
  | none => exact continuous_const
  | some i => exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

theorem norm_coordinateWithConstant_le {n : ℕ} (i : Option (Fin n)) (x : Space n) :
    ‖coordinateWithConstant i x‖ ≤ 1 + ‖x‖ := by
  cases i with
  | none => simpa only [coordinateWithConstant, norm_one] using le_add_of_nonneg_right (norm_nonneg x)
  | some i => exact (PiLp.norm_apply_le x i).trans (le_add_of_nonneg_left zero_le_one)

theorem measureLogConcave.integrable_prod_coordinateWithConstant {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → Option (Fin n)) :
    Integrable (fun x => ∏ a, coordinateWithConstant (s a) x) μ := by
  have hi := ((integrable_const (1 : ℝ) (μ := μ)).add
    (hμ.integrable_norm_pow (Fintype.card ι))).const_mul (2 ^ (Fintype.card ι - 1) : ℝ)
  apply hi.mono' (Continuous.aestronglyMeasurable (by
    exact continuous_finsetProd _ fun a _ => continuous_coordinateWithConstant (s a)))
  apply Eventually.of_forall
  intro x
  calc
    ‖∏ a, coordinateWithConstant (s a) x‖ = ∏ a, ‖coordinateWithConstant (s a) x‖ :=
      norm_prod _ _
    _ ≤ ∏ _a : ι, (1 + ‖x‖) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => norm_coordinateWithConstant_le (s a) x)
    _ = (1 + ‖x‖) ^ Fintype.card ι := by simp
    _ ≤ 2 ^ (Fintype.card ι - 1) * (1 + ‖x‖ ^ Fintype.card ι) := by
      simpa only [one_pow] using add_pow_le (by norm_num : (0 : ℝ) ≤ 1)
        (norm_nonneg x) (Fintype.card ι)

def affineCoordinateCoefficient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Space n) (i : Fin n) : Option (Fin n) → ℝ
  | none => b i
  | some j => A i j

theorem affineMatrixMap_coordinate_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b x : Space n) (i : Fin n) :
    affineMatrixMap A b x i = ∑ j, affineCoordinateCoefficient A b i j *
      coordinateWithConstant j x := by
  simp only [affineMatrixMap_apply, PiLp.add_apply, matrixAction_apply,
    Fintype.sum_option, affineCoordinateCoefficient, coordinateWithConstant, mul_one]
  ring

/-- Exact moment expansion for any finite product of affine coordinates. -/
theorem measureLogConcave.integral_prod_affineMatrixMeasure {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) :
    (∫ x, ∏ a, x (r a) ∂KLS.affineMatrixMeasure μ A b) =
      ∑ s : ι → Option (Fin n), (∏ a, affineCoordinateCoefficient A b (r a) (s a)) *
        ∫ x, ∏ a, coordinateWithConstant (s a) x ∂μ := by
  rw [KLS.affineMatrixMeasure, integral_map (affineMatrixMap A b).continuous.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x : Space n => ∏ a, x (r a)) _ from by fun_prop)]
  simp_rw [affineMatrixMap_coordinate_sum, Fintype.prod_sum, Finset.prod_mul_distrib]
  rw [integral_finsetSum Finset.univ (fun s _ =>
    (hμ.integrable_prod_coordinateWithConstant s).const_mul _)]
  apply Finset.sum_congr rfl
  intro s _
  exact integral_const_mul _ _

theorem affineMatrixMeasure_one_zero {n : ℕ} (μ : Measure (Space n)) :
    affineMatrixMeasure μ 1 0 = μ := by
  have hf : affineMatrixMap (1 : Matrix (Fin n) (Fin n) ℝ) 0 =
      ContinuousAffineMap.id ℝ (Space n) := by
    ext x i
    simp [affineMatrixMap_apply, matrixAction_apply, Matrix.one_apply]
  rw [affineMatrixMeasure, hf]
  exact Measure.map_id

theorem admissibleMeasure.tendsto_whitening_coefficient
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) (i : Fin n) (j : Option (Fin n)) :
    Tendsto (fun k =>
      let ν := ballCutoffMeasure μ R k
      let Q := inverseSqrtMatrix (covarianceMatrix ν)
      affineCoordinateCoefficient Q (-matrixAction Q (∫ x, x ∂ν)) i j)
      atTop (𝓝 (affineCoordinateCoefficient 1 0 i j)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hQ := hμ.tendsto_inverseSqrt_covarianceMatrix_ballCutoffMeasure hR
  have hQij (a b : Fin n) := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hQ a)) b
  cases j with
  | some j => exact hQij i j
  | none =>
    have hm (a : Fin n) : Tendsto (fun k => (∫ x, x ∂ballCutoffMeasure μ R k) a)
        atTop (𝓝 (0 : ℝ)) := by
      have heq (k : ℕ) : (∫ x, x ∂ballCutoffMeasure μ R k) a =
          ∫ x : Space n, x a ∂ballCutoffMeasure μ R k := by
        let : IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
          isProbabilityMeasure_ballCutoffMeasure hR k
        exact ((EuclideanSpace.proj a).integral_comp_comm
          ((hμ.memLp_id_ballCutoffMeasure hR k).integrable (by norm_num))).symm
      simpa only [heq] using hμ.tendsto_coordinate_ballCutoffMeasure R a
    have hh := (tendsto_finsetSum Finset.univ fun a _ => (hQij i a).mul (hm a)).neg
    simpa only [affineCoordinateCoefficient, PiLp.neg_apply, matrixAction_apply,
      mul_zero, Finset.sum_const_zero, neg_zero, PiLp.zero_apply] using hh

/-- Every finite coordinate moment of the actual centered/whitened cutoffs
converges to the original moment. In particular this includes degrees 1--4. -/
theorem admissibleMeasure.tendsto_coordinate_moment_whitenedBallCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → Fin n) :
    Tendsto (fun k => ∫ x, ∏ a, x (r a) ∂whitenedBallCutoffMeasure μ R k)
      atTop (𝓝 (∫ x, ∏ a, x (r a) ∂μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have heq (k : ℕ) := by
    let : IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
      isProbabilityMeasure_ballCutoffMeasure hR k
    exact (hμ.logConcave.ballCutoff_logConcave R k).integral_prod_affineMatrixMeasure r
      (inverseSqrtMatrix (covarianceMatrix (ballCutoffMeasure μ R k)))
      (-matrixAction (inverseSqrtMatrix (covarianceMatrix (ballCutoffMeasure μ R k)))
        (∫ x, x ∂ballCutoffMeasure μ R k))
  simp_rw [whitenedBallCutoffMeasure, whitenedMeasure, heq]
  have hlim := tendsto_finsetSum Finset.univ fun s _ =>
    (tendsto_finsetProd Finset.univ fun a _ =>
      hμ.tendsto_whitening_coefficient hR (r a) (s a)).mul
        (tendsto_integral_ballCutoffMeasure (hμ.logConcave.integrable_prod_coordinateWithConstant s) R)
  have hid := hμ.logConcave.integral_prod_affineMatrixMeasure r 1 0
  rw [affineMatrixMeasure_one_zero] at hid
  simpa only [← hid] using hlim


theorem matrixQuadratic_sq_fourfold_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : matrixQuadratic M x ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, (M i j * M k l) * (x i * x j * x k * x l) := by
  simp only [matrixQuadratic, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem measureLogConcave.integral_matrixQuadratic_sum {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, matrixQuadratic M x ∂μ) = ∑ i, ∑ j, M i j * ∫ x : Space n, x i * x j ∂μ := by
  have hi (i j : Fin n) : Integrable (fun x : Space n => M i j * (x i * x j)) μ :=
    ((hμ.memLp_two_coordinate_mul i j).integrable (by norm_num)).const_mul _
  simp only [matrixQuadratic, mul_assoc]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
  simp only [integral_const_mul]

theorem measureLogConcave.integral_matrixQuadratic_sq_sum {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, matrixQuadratic M x ^ 2 ∂μ) =
      ∑ i, ∑ j, ∑ k, ∑ l, (M i j * M k l) * ∫ x : Space n, x i * x j * x k * x l ∂μ := by
  have hi (i j k l : Fin n) :
      Integrable (fun x : Space n => (M i j * M k l) * (x i * x j * x k * x l)) μ := by
    have hh := ((hμ.memLp_two_coordinate_mul i j).integrable_mul
      (hμ.memLp_two_coordinate_mul k l)).const_mul (M i j * M k l)
    simpa only [Pi.mul_apply, mul_assoc] using hh
  simp_rw [matrixQuadratic_sq_fourfold_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hi i j k l))))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hi i j k l)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _ => integrable_finsetSum _ (fun l _ => hi i j k l))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum Finset.univ (fun l _ => hi i j k l)]
  simp only [integral_const_mul]

/-- Actual quadratic first moments converge under the constructed whitening. -/
theorem admissibleMeasure.tendsto_matrixQuadratic_whitenedBallCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ∫ x, matrixQuadratic M x ∂whitenedBallCutoffMeasure μ R k)
      atTop (𝓝 (∫ x, matrixQuadratic M x ∂μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have heq (k : ℕ) : (∫ x, matrixQuadratic M x ∂whitenedBallCutoffMeasure μ R k) =
      ∑ i, ∑ j, M i j * ∫ x : Space n, x i * x j ∂whitenedBallCutoffMeasure μ R k := by
    let : IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
      isProbabilityMeasure_ballCutoffMeasure hR k
    exact ((hμ.logConcave.ballCutoff_logConcave R k).whitenedMeasure).integral_matrixQuadratic_sum M
  simp_rw [heq, hμ.logConcave.integral_matrixQuadratic_sum M]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply Tendsto.const_mul
  simpa [Fin.prod_univ_succ] using
    hμ.tendsto_coordinate_moment_whitenedBallCutoffMeasure hR ![i, j]

/-- The degree-four moments needed for quadratic variances converge. -/
theorem admissibleMeasure.tendsto_matrixQuadratic_sq_whitenedBallCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ∫ x, matrixQuadratic M x ^ 2 ∂whitenedBallCutoffMeasure μ R k)
      atTop (𝓝 (∫ x, matrixQuadratic M x ^ 2 ∂μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have heq (k : ℕ) : (∫ x, matrixQuadratic M x ^ 2 ∂whitenedBallCutoffMeasure μ R k) =
      ∑ i, ∑ j, ∑ a, ∑ b, (M i j * M a b) *
        ∫ x : Space n, x i * x j * x a * x b ∂whitenedBallCutoffMeasure μ R k := by
    let : IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
      isProbabilityMeasure_ballCutoffMeasure hR k
    exact ((hμ.logConcave.ballCutoff_logConcave R k).whitenedMeasure).integral_matrixQuadratic_sq_sum M
  simp_rw [heq, hμ.logConcave.integral_matrixQuadratic_sq_sum M]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro a _
  apply tendsto_finsetSum
  intro b _
  apply Tendsto.const_mul
  simpa [Fin.prod_univ_succ, mul_assoc] using
    hμ.tendsto_coordinate_moment_whitenedBallCutoffMeasure hR ![i, j, a, b]

/-- Exact quadratic variance convergence under the actual centered/whitened
cutoffs, with all square integrability obligations discharged. -/
theorem admissibleMeasure.tendsto_quadraticVariance_whitenedBallCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ProbabilityTheory.variance (matrixQuadratic M)
      (whitenedBallCutoffMeasure μ R k))
      atTop (𝓝 (ProbabilityTheory.variance (matrixQuadratic M) μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have heq (k : ℕ) : ProbabilityTheory.variance (matrixQuadratic M)
      (whitenedBallCutoffMeasure μ R k) =
      (∫ x, matrixQuadratic M x ^ 2 ∂whitenedBallCutoffMeasure μ R k) -
        (∫ x, matrixQuadratic M x ∂whitenedBallCutoffMeasure μ R k) ^ 2 := by
    let : IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
      isProbabilityMeasure_ballCutoffMeasure hR k
    let : IsProbabilityMeasure (whitenedBallCutoffMeasure μ R k) :=
      inferInstanceAs (IsProbabilityMeasure (whitenedMeasure (ballCutoffMeasure μ R k)))
    exact ProbabilityTheory.variance_eq_sub
      (((hμ.logConcave.ballCutoff_logConcave R k).whitenedMeasure).memLp_two_matrixQuadratic M)
  have hh := (hμ.tendsto_matrixQuadratic_sq_whitenedBallCutoffMeasure hR M).sub
    ((hμ.tendsto_matrixQuadratic_whitenedBallCutoffMeasure hR M).pow 2)
  simpa only [heq, ProbabilityTheory.variance_eq_sub (hμ.logConcave.memLp_two_matrixQuadratic M),
    Pi.pow_apply] using hh


/-- Compact support is a sufficient reduction for the quadratic-variance
bound: the hypothesis is only that the bound has been proved for compactly
supported admissible measures in this same dimension. -/
theorem admissibleMeasure.quadraticVarianceEight_of_compact
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hcompact : ∀ ν : Measure (Space n), admissibleMeasure ν →
      IsCompact ν.support → QuadraticVarianceEight ν) : QuadraticVarianceEight μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨R, _, hR, hevent⟩ := hμ.exists_whitened_compact_cutoffs
  intro M hM
  refine ⟨hμ.logConcave.memLp_two_matrixQuadratic M, ?_⟩
  apply le_of_tendsto (hμ.tendsto_quadraticVariance_whitenedBallCutoffMeasure hR M)
  filter_upwards [hevent] with k hk
  exact (hcompact (whitenedBallCutoffMeasure μ R k) hk.1 hk.2 M hM).2

end KLS
end

#print axioms KLS.measureLogConcave.integral_prod_affineMatrixMeasure
#print axioms KLS.admissibleMeasure.tendsto_coordinate_moment_whitenedBallCutoffMeasure

#print axioms KLS.admissibleMeasure.tendsto_quadraticVariance_whitenedBallCutoffMeasure

#print axioms KLS.admissibleMeasure.quadraticVarianceEight_of_compact
