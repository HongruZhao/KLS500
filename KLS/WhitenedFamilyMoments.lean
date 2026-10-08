import KLS.WhitenedCutoffMoments

/-! Convergence of genuine covariance whitening for a family whose continuous
moments converge. The mean and covariance are computed from the laws; their
limits and eventual positive definiteness are derived. -/

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology ENNReal BigOperators

noncomputable section
namespace KLS

lemma measureLogConcave.memLp_id {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) :
    MemLp (fun x : Space n => x) 2 μ :=
  (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr (hμ.integrable_norm_pow 2)

section Family
variable {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
variable {ν : ℕ → Measure (Space n)} [∀ k, IsProbabilityMeasure (ν k)]
variable (hν : ∀ k, measureLogConcave (ν k))
variable (hlim : ∀ f : Space n → ℝ, Continuous f →
  Tendsto (fun k => ∫ x, f x ∂ν k) atTop (𝓝 (∫ x, f x ∂μ)))

include hμ hν hlim

theorem tendsto_covarianceMatrix_of_continuous_moments :
    Tendsto (fun k => covarianceMatrix (ν k)) atTop
      (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hc (k : ℕ) (a : Fin n) : MemLp (fun x : Space n => x a) 2 (ν k) :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).comp_memLp' ((hν k).memLp_id)
  have heq (k : ℕ) : covarianceMatrix (ν k) i j =
      (∫ x : Space n, x i * x j ∂ν k) -
        (∫ x : Space n, x i ∂ν k) * (∫ x : Space n, x j ∂ν k) := by
    rw [covarianceMatrix_apply ((hν k).memLp_id), covariance_eq_sub (hc k i) (hc k j)]
    rfl
  have hh := (hlim (fun x => x i * x j) (by fun_prop)).sub
    ((hlim (fun x => x i) (by fun_prop)).mul (hlim (fun x => x j) (by fun_prop)))
  simpa only [← heq, hμ.isotropic.integral_coordinate, hμ.isotropic.integral_coordinate_mul,
    zero_mul, sub_zero, Matrix.one_apply] using hh

theorem eventually_posDef_covarianceMatrix_of_continuous_moments :
    ∀ᶠ k in atTop, (covarianceMatrix (ν k)).PosDef :=
  eventually_posDef_of_tendsto_one (tendsto_covarianceMatrix_of_continuous_moments hμ hν hlim)
    (Eventually.of_forall fun _ => covarianceMatrix_posSemidef _)

theorem tendsto_whitening_coefficient_of_continuous_moments
    (i : Fin n) (j : Option (Fin n)) :
    Tendsto (fun k =>
      let Q := inverseSqrtMatrix (covarianceMatrix (ν k))
      affineCoordinateCoefficient Q (-matrixAction Q (∫ x, x ∂ν k)) i j)
      atTop (𝓝 (affineCoordinateCoefficient 1 0 i j)) := by
  have hQ := tendsto_inverseSqrtMatrix_one
    (tendsto_covarianceMatrix_of_continuous_moments hμ hν hlim)
    (Eventually.of_forall fun k => covarianceMatrix_posSemidef (ν k))
  have hQij (a b : Fin n) := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hQ a)) b
  cases j with
  | some j => exact hQij i j
  | none =>
    have hm (a : Fin n) : Tendsto (fun k => (∫ x, x ∂ν k) a) atTop (𝓝 (0 : ℝ)) := by
      have heq (k : ℕ) : (∫ x, x ∂ν k) a = ∫ x : Space n, x a ∂ν k :=
        ((EuclideanSpace.proj a).integral_comp_comm
          ((hν k).memLp_id.integrable (by norm_num))).symm
      simpa only [heq, hμ.isotropic.integral_coordinate] using
        hlim (fun x => x a) (by fun_prop)
    have hh := (tendsto_finsetSum Finset.univ fun a _ => (hQij i a).mul (hm a)).neg
    simpa only [affineCoordinateCoefficient, PiLp.neg_apply, matrixAction_apply,
      mul_zero, Finset.sum_const_zero, neg_zero, PiLp.zero_apply] using hh

/-- Every finite coordinate moment converges after the actual whitening. -/
theorem tendsto_coordinate_moment_whitenedMeasure_of_continuous_moments
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → Fin n) :
    Tendsto (fun k => ∫ x, ∏ a, x (r a) ∂whitenedMeasure (ν k))
      atTop (𝓝 (∫ x, ∏ a, x (r a) ∂μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have heq (k : ℕ) := (hν k).integral_prod_affineMatrixMeasure r
    (inverseSqrtMatrix (covarianceMatrix (ν k)))
    (-matrixAction (inverseSqrtMatrix (covarianceMatrix (ν k))) (∫ x, x ∂ν k))
  simp_rw [whitenedMeasure, heq]
  have hh := tendsto_finsetSum (Finset.univ : Finset (ι → Option (Fin n))) fun s _ =>
    (tendsto_finsetProd Finset.univ fun a _ =>
      tendsto_whitening_coefficient_of_continuous_moments hμ hν hlim (r a) (s a)).mul
        (hlim (fun x => ∏ a, coordinateWithConstant (s a) x)
          (continuous_finsetProd _ fun a _ => continuous_coordinateWithConstant (s a)))
  have hid := hμ.logConcave.integral_prod_affineMatrixMeasure r 1 0
  rw [affineMatrixMeasure_one_zero] at hid
  simpa only [← hid] using hh

theorem tendsto_matrixQuadratic_whitenedMeasure_of_continuous_moments
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ∫ x, matrixQuadratic M x ∂whitenedMeasure (ν k))
      atTop (𝓝 (∫ x, matrixQuadratic M x ∂μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  simp_rw [((hν _).whitenedMeasure).integral_matrixQuadratic_sum M,
    hμ.logConcave.integral_matrixQuadratic_sum M]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply Tendsto.const_mul
  simpa [Fin.prod_univ_succ] using
    tendsto_coordinate_moment_whitenedMeasure_of_continuous_moments hμ hν hlim ![i, j]

theorem tendsto_matrixQuadratic_sq_whitenedMeasure_of_continuous_moments
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ∫ x, matrixQuadratic M x ^ 2 ∂whitenedMeasure (ν k))
      atTop (𝓝 (∫ x, matrixQuadratic M x ^ 2 ∂μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  simp_rw [((hν _).whitenedMeasure).integral_matrixQuadratic_sq_sum M,
    hμ.logConcave.integral_matrixQuadratic_sq_sum M]
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
    tendsto_coordinate_moment_whitenedMeasure_of_continuous_moments hμ hν hlim ![i, j, a, b]

theorem tendsto_quadraticVariance_whitenedMeasure_of_continuous_moments
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ProbabilityTheory.variance (matrixQuadratic M) (whitenedMeasure (ν k)))
      atTop (𝓝 (ProbabilityTheory.variance (matrixQuadratic M) μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have heq (k : ℕ) := ProbabilityTheory.variance_eq_sub
    (((hν k).whitenedMeasure).memLp_two_matrixQuadratic M)
  have hh := (tendsto_matrixQuadratic_sq_whitenedMeasure_of_continuous_moments hμ hν hlim M).sub
    ((tendsto_matrixQuadratic_whitenedMeasure_of_continuous_moments hμ hν hlim M).pow 2)
  simpa only [heq, ProbabilityTheory.variance_eq_sub (hμ.logConcave.memLp_two_matrixQuadratic M),
    Pi.pow_apply] using hh

theorem eventually_admissible_whitenedMeasure_of_continuous_moments :
    ∀ᶠ k in atTop, admissibleMeasure (whitenedMeasure (ν k)) := by
  filter_upwards [eventually_posDef_covarianceMatrix_of_continuous_moments hμ hν hlim] with k hk
  exact ⟨inferInstance, (hν k).whitenedMeasure, whitenedMeasure_isIsotropic ((hν k).memLp_id) hk⟩

end Family
end KLS
end

#print axioms KLS.tendsto_covarianceMatrix_of_continuous_moments
#print axioms KLS.tendsto_quadraticVariance_whitenedMeasure_of_continuous_moments
#print axioms KLS.eventually_admissible_whitenedMeasure_of_continuous_moments
