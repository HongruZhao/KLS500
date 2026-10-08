import KLS.AdaptiveMaximalCumulantNoise

/-! The actual nonexplosive adaptive process has the higher-cumulant equation (73). -/
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

/-- Equation (73), for actual cumulants of the assembled law, up to each genuine
parameter exit. Its next-cumulant noises are actual square-integrable Brownian integrals. -/
theorem cumulant_equation (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (m : ℕ) (hm : 3 ≤ m) (h : Fin m → Space n) (i₀ : Fin m)
    (r : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit r ω →
      D.cumulantPath m h T ω - cumulantTensor μ m h =
        -(∫ t in Icc (0 : ℝ) T, (m : ℝ) * D.cumulantPath m h t ω +
          lowerCumulantDrift μ h (D.path t ω) i₀ ∂volume) +
            ∑ k : Fin n, D.cumulantNoiseIntegral m h hμ (by omega) r k T ω := by
  have hm0 : m ≠ 0 := by omega
  have hn : ∀ᵐ ω ∂P, ∀ k : Fin n, D.cumulantNoiseIntegral m h hμ hm0 r k T ω =
      BallProcess.cumulantNoiseIntegral m h (D r) hμ hm0 k T ω :=
    ae_all_iff.mpr fun k => D.cumulantNoiseIntegral_eq_local m h hμ hm0 r k hT
  filter_upwards [D.ae_path_eq_of_le_exit,
    BallProcess.cumulant_equation m h (D r) hμ hfull hm i₀ hℱ0 hnull hT, hn]
    with ω hp he hnoise hle
  have he' := he hle
  rw [← hp r T hT.le hle] at he'
  have hd : (∫ t in Icc (0 : ℝ) T,
      (m : ℝ) * coordinateCumulant μ m h ((D r).pair.Y t ω) +
        lowerCumulantDrift μ h ((D r).pair.Y t ω) i₀ ∂volume) =
      ∫ t in Icc (0 : ℝ) T, (m : ℝ) * D.cumulantPath m h t ω +
        lowerCumulantDrift μ h (D.path t ω) i₀ ∂volume := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change (m : ℝ) * coordinateCumulant μ m h ((D r).pair.Y t ω) +
      lowerCumulantDrift μ h ((D r).pair.Y t ω) i₀ =
        (m : ℝ) * coordinateCumulant μ m h (D.path t ω) + lowerCumulantDrift μ h (D.path t ω) i₀
    rw [hp r t ht.1 ((show (t : WithTop ℝ) ≤ (T : WithTop ℝ) by exact_mod_cast ht.2).trans hle)]
  exact he'.trans (congrArg₂ (fun a b : ℝ => -a+b) hd
    (Finset.sum_congr rfl fun k _ => (hnoise k).symm))

/-- For compact admissible input the actual parameter exits exhaust every finite time. -/
theorem ae_cumulant_exits_exhaust (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, ∃ r : ℕ, (T : WithTop ℝ) < D.exit r ω := by
  filter_upwards [D.ae_lifetime_eq_top hμ hadm hℱ0 hnull] with ω htop T
  exact (D.lt_lifetime_iff ω T).mp (by rw [htop]; exact WithTop.coe_lt_top T)

end MaximalProcess

/-- A genuine nonexplosive adaptive process carries equation (73) at every localizing
exit, for every order and every mixed tuple. No cumulant dynamics are supplied as data. -/
theorem exists_adaptiveCumulantProcess (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)),
      IsMaximalLocalSde D ∧
      (∀ᵐ ω ∂P, D.lifetime ω = ⊤) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ, ∃ r : ℕ, (T : WithTop ℝ) < D.exit r ω) ∧
      (∀ (m : ℕ) (hm : 3 ≤ m) (h : Fin m → Space n) (i₀ : Fin m) (r : ℕ) (T : ℝ),
        0 < T → ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit r ω →
          D.cumulantPath m h T ω - cumulantTensor μ m h =
            -(∫ t in Icc (0 : ℝ) T, (m : ℝ) * D.cumulantPath m h t ω +
              lowerCumulantDrift μ h (D.path t ω) i₀ ∂volume) +
              ∑ k : Fin n, D.cumulantNoiseIntegral m h hμ (by omega) r k T ω) := by
  obtain ⟨Ω, mΩ, P, hP, W, D, hD, htop, _⟩ := exists_adaptiveGlobalProcess μ hμ hadm
  exact ⟨Ω, mΩ, P, hP, W, D, hD, htop,
    D.ae_cumulant_exits_exhaust hμ hadm (usualFiltration_beforeZero W) (usualFiltration_null W),
    fun m hm h i₀ r T hT => D.cumulant_equation hμ hadm.isotropic.affineSpan_support_eq_top
      (usualFiltration_beforeZero W) (usualFiltration_null W) m hm h i₀ r hT⟩

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.cumulant_equation
#print axioms KLS.AdaptiveLocalization.exists_adaptiveCumulantProcess
