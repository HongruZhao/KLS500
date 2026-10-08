import KLS.FullQuadraticVarianceBound
import KLS.OneDimensionalJet
import KLS.AffineWhitening

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
noncomputable section
namespace KLS.ConstantReduction

variable {n : ℕ}

def standardizedScalarMap (f : Space n →L[ℝ] ℝ) (m σ : ℝ) : Space n →ᴬ[ℝ] Space 1 :=
  ((σ⁻¹ • scalarAxisEquiv.toContinuousLinearMap).comp f).toContinuousAffineMap +
    ContinuousAffineMap.const ℝ (Space n) (scalarAxisEquiv (-(m / σ)))

@[simp] theorem standardizedScalarMap_apply (f : Space n →L[ℝ] ℝ) (m σ : ℝ)
    (x : Space n) (i : Fin 1) : standardizedScalarMap f m σ x i = (f x - m) / σ := by
  fin_cases i
  simp [standardizedScalarMap, scalarAxisEquiv_apply, div_eq_mul_inv]
  ring

theorem standardizedScalarMap_isIsotropic {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (f : Space n →L[ℝ] ℝ) {σ : ℝ} (hσ : σ ≠ 0)
    (hvar : ProbabilityTheory.variance f μ = σ ^ 2) :
    IsIsotropic (μ.map (standardizedScalarMap f (∫ x, f x ∂μ) σ)) := by
  let F := standardizedScalarMap f (∫ x, f x ∂μ) σ
  let ν := μ.map F
  have hmem : MemLp (fun x => f x) 2 μ := by
    apply (memLp_two_iff_integrable_sq f.continuous.aestronglyMeasurable).mpr
    exact integrable_of_continuous_compact_support_measure hμ (by fun_prop)
  have hc (i : Fin 1) : MemLp (fun x : Space 1 => x i) 2 ν := by
    apply (memLp_map_measure_iff (by fun_prop) F.continuous.measurable.aemeasurable).mpr
    simpa [F, Function.comp_def, div_eq_mul_inv] using (hmem.sub (memLp_const _)).mul_const σ⁻¹
  have hi (i : Fin 1) : Integrable (fun x : Space 1 => x i) ν :=
    (hc i).integrable (by norm_num)
  have hmean (i : Fin 1) : (∫ x : Space 1, x i ∂ν) = 0 := by
    rw [show ν = μ.map F from rfl, integral_map F.continuous.measurable.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : Space 1 => x i) (μ.map F))]
    simp only [F, standardizedScalarMap_apply, integral_div]
    rw [integral_sub (hmem.integrable (by norm_num)) (integrable_const _)]
    simp
  have hsq (i : Fin 1) : (∫ x : Space 1, (x i)^2 ∂ν) = 1 := by
    rw [show ν = μ.map F from rfl, integral_map F.continuous.measurable.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : Space 1 => (x i)^2) (μ.map F))]
    simp only [F, standardizedScalarMap_apply, div_pow, integral_div]
    rw [← variance_eq_integral f.continuous.measurable.aemeasurable, hvar]
    exact div_self (pow_ne_zero _ hσ)
  refine ⟨Integrable.of_eval_piLp hi, ?_, ?_, ?_⟩
  · ext i
    rw [eval_integral_piLp hi i, hmean]
    rfl
  · intro i j
    exact (hc i).integrable_mul (hc j)
  · ext i j
    fin_cases i
    fin_cases j
    simpa [secondMomentMatrix, pow_two] using hsq (0 : Fin 1)

theorem centered_square_variance_le_eight {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (hlc : measureLogConcave μ) (f : Space n →L[ℝ] ℝ)
    (hv : 0 < ProbabilityTheory.variance f μ) :
    ProbabilityTheory.variance (fun x => (f x - ∫ y, f y ∂μ)^2) μ ≤ 8 * (ProbabilityTheory.variance f μ)^2 := by
  let σ := Real.sqrt (ProbabilityTheory.variance f μ)
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  have hσ2 : σ^2 = ProbabilityTheory.variance f μ := Real.sq_sqrt hv.le
  let F := standardizedScalarMap f (∫ x, f x ∂μ) σ
  let ν := μ.map F
  have hadm : admissibleMeasure ν :=
    ⟨inferInstance, hlc.map_continuousAffineMap F,
      standardizedScalarMap_isIsotropic hμ f hσ.ne' hσ2.symm⟩
  have hQ := (hadm.quadraticVarianceEight_unconditional 1 Matrix.isSymm_one).2
  have hform (x : Space 1) : matrixQuadratic (1 : Matrix (Fin 1) (Fin 1) ℝ) x = x 0 ^ 2 := by
    simp [matrixQuadratic, pow_two]
  simp_rw [show matrixQuadratic (1 : Matrix (Fin 1) (Fin 1) ℝ) = (fun x : Space 1 => x 0 ^ 2) from funext hform] at hQ
  norm_num [matrixFrobeniusSq] at hQ
  rw [show ν = μ.map F from rfl, variance_map (by fun_prop) F.continuous.measurable.aemeasurable] at hQ
  have heq : (fun x => (F x 0)^2) = (fun x => (σ^2)⁻¹ * (f x - ∫ y, f y ∂μ)^2) := by
    funext x
    simp [F, div_eq_mul_inv, mul_comm, mul_pow]
  change ProbabilityTheory.variance (fun x => (F x 0)^2) μ ≤ 8 at hQ
  rw [heq, variance_const_mul] at hQ
  have hp : 0 < (σ^2)^2 := by positivity
  have hh := (mul_le_mul_of_nonneg_left hQ hp.le)
  simp only [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (pow_ne_zero _ hσ.ne'), one_pow, one_mul] at hh
  simpa only [hσ2, mul_comm] using hh

end KLS.ConstantReduction
end
