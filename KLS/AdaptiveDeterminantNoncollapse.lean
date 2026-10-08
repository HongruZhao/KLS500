import KLS.AdaptiveContinuousLogDet

/-! The actual covariance determinant stays uniformly positive on every finite horizon before lifetime. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

/-- A single event supports every finite horizon. The lower bound may depend
on the sample path and horizon, but is strictly positive and uniform in time. -/
theorem ae_finite_horizon_covariance_det_lower_bound (hμ : IsCompact μ.support)
    (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, 0 ≤ T → ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) T → (t : WithTop ℝ) < D.lifetime ω →
        δ ≤ (D.covariancePath t ω).det := by
  obtain ⟨Z, hZc, _, hZ⟩ := D.exists_continuous_logDet_representation hμ hadm hℱ0 hnull
  filter_upwards [hZ] with ω hω T _
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hZc ω).continuousOn
  refine ⟨Real.exp (-B), Real.exp_pos _, ?_⟩
  intro t ht hlife
  have hb : -B ≤ Z t ω := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hB t ht)).1
  calc
    Real.exp (-B) ≤ Real.exp (Z t ω) := Real.exp_le_exp.mpr hb
    _ = (D.covariancePath t ω).det := by
      rw [← hω t ht.1 hlife, Real.exp_log
        (D.covariancePath_posDef hμ hadm.isotropic.affineSpan_support_eq_top t ω).det_pos]

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.ae_finite_horizon_covariance_det_lower_bound
