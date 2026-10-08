import KLS.AdaptiveClippedLogDetEquation

/-! A globally continuous process agrees with the actual covariance logdet before lifetime. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
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

/-- Construct the continuous extension from genuine Brownian integrals of the
bounded clipped trace coefficients and the bounded clipped drift. Countably many
rational-time identities identify it with actual covariance logdet before lifetime. -/
theorem exists_continuous_logDet_representation (hμ : IsCompact μ.support)
    (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) :
    ∃ Z : ℝ → Ω → ℝ,
      (∀ ω : Ω, Continuous fun t => Z t ω) ∧
      (∀ T : ℝ, 0 ≤ T → Z T =ᵐ[P] fun ω =>
        Real.log (covariance μ 0 0).det +
          (∫ t in Icc (0 : ℝ) T, D.clippedLogDetDrift ω t ∂volume) +
            ∑ k : Fin n, D.clippedLogDetNoiseIntegral hμ hadm.isotropic.affineSpan_support_eq_top k T ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < D.lifetime ω →
        Real.log (D.covariancePath t ω).det = Z t ω) := by
  have hfull := hadm.isotropic.affineSpan_support_eq_top
  have hex (k : Fin n) : ∃ M : ℝ → Ω → ℝ,
      (∀ ω : Ω, Continuous fun t => M t ω) ∧ (∀ t : ℝ, Measurable[ℱ t] (M t)) ∧
      ∀ t : ℝ, 0 ≤ t → M t =ᵐ[P] D.clippedLogDetNoiseIntegral hμ hfull k t :=
    exists_continuousAdapted_modification (W.W k) ℱ (hW k) (D.clippedLogDetNoise k)
      (D.clippedLogDetNoise_measurable hμ hfull k) (D.clippedLogDetNoise_progressive hμ hfull k)
      (D.clippedLogDetNoise_energy k) (logDetNoiseBound_nonneg n) (D.clippedLogDetNoise_bound k)
      hℱ0 hnull
  choose M hMc hMa hMe using hex
  let Z : ℝ → Ω → ℝ := fun t ω => Real.log (covariance μ 0 0).det +
    (∫ s in Icc (0 : ℝ) t, D.clippedLogDetDrift ω s ∂volume) + ∑ k : Fin n, M k t ω
  have hZc (ω : Ω) : Continuous fun t => Z t ω := by
    apply (continuous_const.add (continuous_setIntegral_Icc
      (Measurable.of_uncurry_left (D.clippedLogDetDrift_measurable hμ hfull))
      (logDetDriftBound_nonneg n) (D.clippedLogDetDrift_bound ω))).add
    exact continuous_finset_sum _ fun k _ => hMc k ω
  have hZm (T : ℝ) (hT : 0 ≤ T) : Z T =ᵐ[P] fun ω =>
      Real.log (covariance μ 0 0).det +
        (∫ t in Icc (0 : ℝ) T, D.clippedLogDetDrift ω t ∂volume) +
          ∑ k : Fin n, D.clippedLogDetNoiseIntegral hμ hfull k T ω := by
    filter_upwards [ae_all_iff.mpr fun k => hMe k T hT] with ω hω
    exact congrArg (fun s : ℝ => Real.log (covariance μ 0 0).det +
      (∫ t in Icc (0 : ℝ) T, D.clippedLogDetDrift ω t ∂volume) + s)
        (Finset.sum_congr rfl fun k _ => hω k)
  have hM0 : ∀ᵐ ω ∂P, ∀ k : Fin n, M k 0 ω = 0 := by
    apply ae_all_iff.mpr
    intro k
    have hz := stochasticIntegralBrownian_ae_zero_of_nonpos (W.W k) ℱ (hW k)
      (D.clippedLogDetNoise k) (D.clippedLogDetNoise_measurable hμ hfull k)
      (D.clippedLogDetNoise_progressive hμ hfull k) (D.clippedLogDetNoise_energy k)
      (show (0 : ℝ) ≤ 0 from le_rfl)
    filter_upwards [hMe k 0 le_rfl, hz] with ω he hzω
    exact he.trans hzω
  have hZ0 : Z 0 =ᵐ[P] fun _ => Real.log (covariance μ 0 0).det := by
    filter_upwards [hM0] with ω hω
    simp [Z, hω]
  have hlocal (m : ℕ) : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ D.exit m ω →
      coordinateLogDet μ ((D m).pair.Y t ω) = Z t ω := by
    apply ae_all_eq_before_cutoff
      (fun ω => (contDiff_coordinateLogDet hμ hfull).continuous.comp ((D m).pair.ito_Y.continuous_path ω)) hZc
    · filter_upwards [(D m).initial_Y, hZ0] with ω h0 hz
      dsimp only [Function.comp_apply]
      rw [h0, hz]
      simp only [coordinateLogDet, coordinateCovarianceMatrix, decodeState_zero, Prod.fst_zero, Prod.snd_zero]
    · intro T hT
      filter_upwards [D.clippedLogDet_equation hμ hadm hℱ0 hnull m hT,
        D.ae_path_eq_of_le_exit, hZm T hT.le] with ω he hp hz hle
      have hcov : Real.log (D.covariancePath T ω).det = coordinateLogDet μ ((D m).pair.Y T ω) := by
        unfold covariancePath parameterPath coordinateLogDet coordinateCovarianceMatrix
        rw [hp m T hT.le hle]
      have he' := he hle
      rw [hcov] at he'
      dsimp only [Function.comp_apply]
      linarith
  refine ⟨Z, hZc, hZm, ?_⟩
  filter_upwards [ae_all_iff.mpr hlocal, D.ae_path_eq_of_le_exit] with ω hl hp t ht hlife
  obtain ⟨m, hm⟩ := (D.lt_lifetime_iff ω t).mp hlife
  change coordinateLogDet μ (D.path t ω) = Z t ω
  rw [hp m t ht hm.le]
  exact hl m t ht hm.le

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.exists_continuous_logDet_representation
