import KLS.AdaptiveEnergyApriori

/-! Expectation of the actual covariance in an arbitrary fixed direction. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {n : ℕ}

def directionalCovarianceCLM (u : Space n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A => ∑ i, ∑ j, u i * A i j * u j
    map_add' := by
      intro A B
      simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro c A
      simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring }

theorem directionalCovarianceCLM_apply (u : Space n) (A : Matrix (Fin n) (Fin n) ℝ) :
    directionalCovarianceCLM u A = inner ℝ u (matrixAction A u) := by
  change (∑ i, ∑ j, u i * A i j * u j) = _
  simp only [inner_eq_coordinate_sum, matrixAction_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem directionalCovarianceCLM_one (u : Space n) :
    directionalCovarianceCLM u 1 = ‖u‖^2 := by
  rw [directionalCovarianceCLM_apply]
  have h : matrixAction (1 : Matrix (Fin n) (Fin n) ℝ) u = u := by
    ext i
    simp [matrixAction_apply, Matrix.one_apply]
  rw [h, real_inner_self_eq_norm_sq]

namespace AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe v
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

def directionalCovariancePath (u : Space n) (t : ℝ) (ω : Ω) : ℝ :=
  directionalCovarianceCLM u (D.covariancePath t ω)

theorem directionalCovariancePath_integrable (hμ : IsCompact μ.support) (u : Space n) (t : ℝ) :
    Integrable (D.directionalCovariancePath u t) P :=
  (directionalCovarianceCLM u).integrable_comp (D.covariancePath_integrable hμ t)

theorem integral_directionalCovariancePath (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (u : Space n) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, D.directionalCovariancePath u t ω ∂P) = Real.exp (-t) * ‖u‖^2 := by
  calc
    _ = directionalCovarianceCLM u (∫ ω, D.covariancePath t ω ∂P) :=
      (directionalCovarianceCLM u).integral_comp_comm (D.covariancePath_integrable hμ t)
    _ = _ := by
      rw [D.integral_covariancePath_eq_exp_neg_smul_one hμ hadm hℱ0 hnull ht,
        map_smul, directionalCovarianceCLM_one, smul_eq_mul]

theorem directionalCovariancePath_nonnegative (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (u : Space n) (t : ℝ) (ω : Ω) :
    0 ≤ D.directionalCovariancePath u t ω := by
  rw [directionalCovariancePath, directionalCovarianceCLM_apply, ← matrixQuadratic_eq_inner]
  simpa only [matrixQuadratic, dotProduct, mulVec, star_trivial, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm] using
    (D.covariancePath_posDef hμ hfull t ω).posSemidef.dotProduct_mulVec_nonneg u.ofLp

end MaximalProcess
end AdaptiveLocalization
end KLS
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.integral_directionalCovariancePath
