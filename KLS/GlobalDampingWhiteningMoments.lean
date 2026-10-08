import KLS.GlobalDampingDensity

/-! The actual first and second damped moments give convergence of covariance whitening. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma IsIsotropic.memLp_id_quadraticDamping_nonneg {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) {ε : ℝ} (hε : 0 ≤ ε) :
    MemLp (fun x : Space n => x) 2 (quadraticDamping μ ε) := by
  apply (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr
  exact integrable_quadraticDamping_nonneg
    ((memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mp hμ.memLp_id) hε

section
variable {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
variable {ε : ℕ → ℝ} (hε : ∀ k, 0 ≤ ε k) (hεlim : Tendsto ε atTop (𝓝 0))

include hμ hε hεlim

theorem tendsto_covarianceMatrix_quadraticDamping_nonneg :
    Tendsto (fun k => covarianceMatrix (quadraticDamping μ (ε k))) atTop
      (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let ν := fun k => quadraticDamping μ (ε k)
  let : ∀ k, IsProbabilityMeasure (ν k) := fun k => isProbabilityMeasure_quadraticDamping_nonneg μ (hε k)
  have hL (k : ℕ) : MemLp (fun x : Space n => x) 2 (ν k) :=
    hμ.isotropic.memLp_id_quadraticDamping_nonneg (hε k)
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hc (k : ℕ) (a : Fin n) : MemLp (fun x : Space n => x a) 2 (ν k) :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).comp_memLp' (hL k)
  have heq (k : ℕ) : covarianceMatrix (ν k) i j =
      (∫ x : Space n, x i * x j ∂ν k) -
        (∫ x : Space n, x i ∂ν k) * (∫ x : Space n, x j ∂ν k) := by
    rw [covarianceMatrix_apply (hL k), covariance_eq_sub (hc k i) (hc k j)]
    rfl
  have hh := (tendsto_integral_quadraticDamping_nonneg μ
    (hμ.isotropic.2.2.1 i j) hε hεlim).sub
    ((tendsto_integral_quadraticDamping_nonneg μ (hμ.isotropic.integrable_coordinate i) hε hεlim).mul
      (tendsto_integral_quadraticDamping_nonneg μ (hμ.isotropic.integrable_coordinate j) hε hεlim))
  simpa only [← heq, hμ.isotropic.integral_coordinate, hμ.isotropic.integral_coordinate_mul,
    zero_mul, sub_zero, Matrix.one_apply, ν] using hh

theorem eventually_posDef_covarianceMatrix_quadraticDamping_nonneg :
    ∀ᶠ k in atTop, (covarianceMatrix (quadraticDamping μ (ε k))).PosDef :=
  eventually_posDef_of_tendsto_one (tendsto_covarianceMatrix_quadraticDamping_nonneg hμ hε hεlim)
    (Eventually.of_forall fun _ => covarianceMatrix_posSemidef _)

theorem tendsto_whitening_coefficient_quadraticDamping_nonneg
    (i : Fin n) (j : Option (Fin n)) :
    Tendsto (fun k =>
      let ν := quadraticDamping μ (ε k)
      let Q := inverseSqrtMatrix (covarianceMatrix ν)
      affineCoordinateCoefficient Q (-matrixAction Q (∫ x, x ∂ν)) i j)
      atTop (𝓝 (affineCoordinateCoefficient 1 0 i j)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let ν := fun k => quadraticDamping μ (ε k)
  let : ∀ k, IsProbabilityMeasure (ν k) := fun k => isProbabilityMeasure_quadraticDamping_nonneg μ (hε k)
  have hQ := tendsto_inverseSqrtMatrix_one
    (tendsto_covarianceMatrix_quadraticDamping_nonneg hμ hε hεlim)
    (Eventually.of_forall fun _ => covarianceMatrix_posSemidef _)
  have hQij (a b : Fin n) := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hQ a)) b
  cases j with
  | some j => exact hQij i j
  | none =>
    have hm (a : Fin n) : Tendsto (fun k => (∫ x, x ∂ν k) a) atTop (𝓝 (0 : ℝ)) := by
      have heq (k : ℕ) : (∫ x, x ∂ν k) a = ∫ x : Space n, x a ∂ν k :=
        ((EuclideanSpace.proj a).integral_comp_comm
          ((hμ.isotropic.memLp_id_quadraticDamping_nonneg (hε k)).integrable (by norm_num))).symm
      simpa only [heq, hμ.isotropic.integral_coordinate, ν] using
        tendsto_integral_quadraticDamping_nonneg μ (hμ.isotropic.integrable_coordinate a) hε hεlim
    have hh := (tendsto_finsetSum Finset.univ fun a _ => (hQij i a).mul (hm a)).neg
    simpa only [affineCoordinateCoefficient, PiLp.neg_apply, matrixAction_apply,
      mul_zero, Finset.sum_const_zero, neg_zero, PiLp.zero_apply] using hh

theorem eventually_admissible_global_strongDensity_whitened_damping
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hc : ConvexOn ℝ univ V)
    (heq : μ = potentialMeasure V) (hpos : ∀ k, 0 < ε k) :
    ∀ᶠ k in atTop, admissibleMeasure (whitenedMeasure (quadraticDamping μ (ε k))) ∧
      HasSmoothStronglyConvexDensity (whitenedMeasure (quadraticDamping μ (ε k))) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  filter_upwards [eventually_posDef_covarianceMatrix_quadraticDamping_nonneg hμ hε hεlim] with k hk
  let : IsProbabilityMeasure (quadraticDamping μ (ε k)) := isProbabilityMeasure_quadraticDamping_nonneg μ (hε k)
  refine ⟨⟨inferInstance,
    (measureLogConcave_quadraticDamping_of_potential hV hc heq (hε k)).whitenedMeasure,
    whitenedMeasure_isIsotropic (hμ.isotropic.memLp_id_quadraticDamping_nonneg (hε k)) hk⟩, ?_⟩
  exact affine_quadraticDamping_global_strongDensity hV hc heq (hpos k) _ _
    (inverseSqrtMatrix_det_ne_zero hk)

end
end KLS
end
