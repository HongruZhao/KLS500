import KLS.AdaptiveMaximalCovarianceNoise
import KLS.AdaptiveQuadraticParameter

/-! Actual adaptive covariance evolution up to the constructed maximal lifetime. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 800000
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

theorem covariancePath_posDef (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (t : ℝ) (ω : Ω) : (D.covariancePath t ω).PosDef :=
  covariance_posDef hμ hfull (D.parameterPath t ω)

theorem covariancePath_continuousOn (hμ : IsCompact μ.support) : ∀ᵐ ω ∂P,
    ContinuousOn (fun t => D.covariancePath t ω)
      {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < D.lifetime ω} :=
  D.parameterPath_continuousOn.mono fun ω hω =>
    (contDiff_covariance_matrix hμ).continuous.comp_continuousOn hω

/-- The actual normalized covariance of the assembled maximal process obeys
 dA = -A dt + third-cumulant noise up to each genuine state exit. The identity
 holds almost surely at each fixed positive horizon; no infinite lifetime is assumed. -/
theorem covariance_equation (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (m : ℕ) (i j : Fin n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit m ω →
      D.covariancePath T ω i j - covariance μ 0 0 i j =
        -(∫ t in Icc (0 : ℝ) T, D.covariancePath t ω i j ∂volume) +
          ∑ k : Fin n, D.covarianceNoiseIntegral hμ m i j k T ω := by
  have hn : ∀ᵐ ω ∂P, ∀ k : Fin n, D.covarianceNoiseIntegral hμ m i j k T ω =
      BallProcess.covarianceNoiseIntegral (D m) hμ i j k T ω :=
    ae_all_iff.mpr fun k => D.covarianceNoiseIntegral_eq_local hμ m i j k hT
  filter_upwards [D.ae_path_eq_of_le_exit,
    BallProcess.covariance_equation (D m) hμ hfull hℱ0 hnull i j hT, hn]
    with ω hp he hnoise hle
  have hc (t : ℝ) (ht : 0 ≤ t) (he : (t : WithTop ℝ) ≤ D.exit m ω) :
      D.covariancePath t ω i j = BallProcess.covariancePath (D m) t ω i j := by
    unfold covariancePath BallProcess.covariancePath parameterPath BallProcess.parameterPath
    rw [hp m t ht he]
  have hd : (∫ t in Icc (0 : ℝ) T, BallProcess.covariancePath (D m) t ω i j ∂volume) =
      ∫ t in Icc (0 : ℝ) T, D.covariancePath t ω i j ∂volume := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    exact (hc t ht.1
      ((show (t : WithTop ℝ) ≤ (T : WithTop ℝ) by exact_mod_cast ht.2).trans hle)).symm
  rw [hc T hT.le hle, he hle, hd]
  congr 1
  exact Finset.sum_congr rfl fun k _ => (hnoise k).symm

end MaximalProcess

/-- A concrete adaptive covariance process exists from compact full-dimensional
probability data. It carries the actual local SDE, positive quadratic parameter,
and genuine covariance evolution. Nonexplosion remains a separate theorem. -/
theorem exists_adaptiveCovarianceProcess (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (hfull : affineSpan ℝ μ.support = ⊤) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)),
      IsMaximalLocalSde D ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < D.lifetime ω →
        (D.parameterPath t ω).2.PosSemidef) ∧
      (∀ (m : ℕ) (i j : Fin n) (T : ℝ), 0 < T → ∀ᵐ ω ∂P,
        (T : WithTop ℝ) ≤ D.exit m ω →
          D.covariancePath T ω i j - covariance μ 0 0 i j =
            -(∫ t in Icc (0 : ℝ) T, D.covariancePath t ω i j ∂volume) +
              ∑ k : Fin n, D.covarianceNoiseIntegral hμ m i j k T ω) := by
  obtain ⟨Ω, mΩ, P, hP, W, D, hD⟩ := exists_adaptiveMaximalLocalProcess μ hμ hfull
  exact ⟨Ω, mΩ, P, hP, W, D, hD, D.ae_all_matrix_posSemidef hμ hfull,
    fun m i j T hT => D.covariance_equation hμ hfull
      (usualFiltration_beforeZero W) (usualFiltration_null W) m i j hT⟩

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.covariance_equation
#print axioms KLS.AdaptiveLocalization.exists_adaptiveCovarianceProcess
