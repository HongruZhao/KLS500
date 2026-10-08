import KLS.AdaptiveGlobalAverageIto

/-! Actual law averages are bounded martingales, and preserve their base expectation. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}

def nonnegativeFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) : Filtration ℝ≥0 ‹MeasurableSpace Ω› where
  seq t := ℱ (t : ℝ)
  mono' := fun _ _ h => ℱ.mono (by exact_mod_cast h)
  le' t := ℱ.le (t : ℝ)

namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW) (f : Space n → ℝ)

def averagePath (t : ℝ) (ω : Ω) : ℝ := ∫ x, f x ∂D.localizationLaw t ω

theorem averagePath_initial : D.averagePath f 0 =ᵐ[P] fun _ => ∫ x, f x ∂μ := by
  filter_upwards [D.path_initial] with ω h0
  change coordinateAverage μ f (D.path 0 ω) = _
  rw [h0]
  simp only [coordinateAverage, Pi.zero_apply, decodeState_zero, Prod.fst_zero, Prod.snd_zero, law_zero_zero]

theorem averagePath_stronglyAdapted (hμ : IsCompact μ.support) (hfi : Integrable f μ) :
    StronglyAdapted ℱ (D.averagePath f) := fun t =>
  (((contDiff_coordinateAverage hμ hfi).continuous.measurable).comp (D.measurable_path_slice t)).stronglyMeasurable

theorem averagePath_bound (hμ : IsCompact μ.support) {B : ℝ}
    (hB : ∀ x ∈ μ.support, |f x| ≤ B) (t : ℝ) (ω : Ω) : |D.averagePath f t ω| ≤ B :=
  abs_coordinateAverage_le hμ hB (D.path t ω)

variable (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ μ.support, |f x| ≤ B)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)

theorem averagePath_eq_integralExpression {T : ℝ} (hT : 0 ≤ T) :
    D.averagePath f T =ᵐ[P] fun ω => (∫ x, f x ∂μ) +
      ∑ k : Fin n, D.globalAverageNoiseIntegral f hμ hadm hf hB0 hB hℱ0 hnull k T ω := by
  rcases hT.eq_or_lt with he | he
  · subst T
    have hz : ∀ᵐ ω ∂P, ∀ k : Fin n,
        D.globalAverageNoiseIntegral f hμ hadm hf hB0 hB hℱ0 hnull k 0 ω = 0 :=
      ae_all_iff.mpr fun k => stochasticIntegralBrownian_ae_zero_of_nonpos (W.W k) ℱ (hW k)
        (D.globalAverageNoise f k) (D.globalAverageNoise_measurable f hμ (integrable_of_bounded_on_support hf hB) k)
        (D.globalAverageNoise_progressive f hμ (integrable_of_bounded_on_support hf hB) k)
        (D.globalAverageNoise_energy f hμ hadm hf hB0 hB hℱ0 hnull k) le_rfl
    filter_upwards [D.averagePath_initial f, hz] with ω h0 hzω
    simp only [h0, hzω, Finset.sum_const_zero, add_zero]
  · filter_upwards [D.average_equation_global f hμ hadm hf hB0 hB hℱ0 hnull he] with ω hω
    exact sub_eq_iff_eq_add'.mp hω

theorem averageIntegralExpression_martingale :
    Martingale (fun t ω => (∫ x, f x ∂μ) +
      ∑ k : Fin n, D.globalAverageNoiseIntegral f hμ hadm hf hB0 hB hℱ0 hnull k t ω) ℱ P := by
  have hs (S : Finset (Fin n)) : Martingale (fun t ω =>
      ∑ k ∈ S, D.globalAverageNoiseIntegral f hμ hadm hf hB0 hB hℱ0 hnull k t ω) ℱ P := by
    induction S using Finset.induction_on with
    | empty =>
      convert! martingale_zero ℝ ℱ P using 1
    | @insert a S ha ih =>
      convert! (D.globalAverageNoiseIntegral_martingale f hμ hadm hf hB0 hB hℱ0 hnull a).add ih using 1
      funext t ω
      simp only [Finset.sum_insert ha, Pi.add_apply]
  exact (martingale_const ℱ P (∫ x, f x ∂μ)).add (hs Finset.univ)

include hμ hadm hf hB0 hB hℱ0 hnull

/-- Literal test-law averages, indexed by nonnegative physical time, are martingales. -/
theorem averagePath_martingale :
    Martingale (fun t : ℝ≥0 => D.averagePath f (t : ℝ)) (nonnegativeFiltration ℱ) P := by
  have hm := D.averageIntegralExpression_martingale f hμ hadm hf hB0 hB hℱ0 hnull
  have hm' : Martingale (fun (t : ℝ≥0) ω => (∫ x, f x ∂μ) +
      ∑ k : Fin n, D.globalAverageNoiseIntegral f hμ hadm hf hB0 hB hℱ0 hnull k (t : ℝ) ω)
      (nonnegativeFiltration ℱ) P :=
    ⟨fun t => hm.stronglyMeasurable (t : ℝ), fun s t hst => hm.condExp_ae_eq (by exact_mod_cast hst)⟩
  exact hm'.congr (fun t => D.averagePath_stronglyAdapted f hμ (integrable_of_bounded_on_support hf hB) (t : ℝ))
    (fun t => (D.averagePath_eq_integralExpression f hμ hadm hf hB0 hB hℱ0 hnull t.2).symm)

theorem integral_averagePath_eq_base {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, D.averagePath f T ω ∂P) = ∫ x, f x ∂μ := by
  have hm := D.averagePath_martingale f hμ hadm hf hB0 hB hℱ0 hnull
  have he : (∫ ω, D.averagePath f 0 ω ∂P) = ∫ ω, D.averagePath f T ω ∂P := by
    have hh := hm.setIntegral_eq (show (0 : ℝ≥0) ≤ ⟨T, hT⟩ from bot_le) (s := Set.univ) MeasurableSet.univ
    change (∫ ω in Set.univ, D.averagePath f 0 ω ∂P) = (∫ ω in Set.univ, D.averagePath f T ω ∂P) at hh
    simpa only [setIntegral_univ] using hh
  rw [← he]
  exact (integral_congr_ae (D.averagePath_initial f)).trans (by simp)

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.averagePath_martingale
#print axioms KLS.AdaptiveLocalization.MaximalProcess.integral_averagePath_eq_base
