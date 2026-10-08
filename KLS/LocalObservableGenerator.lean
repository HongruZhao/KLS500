import KLS.LocalObservableIto

/-! Combine the genuine local Itô drift into its actual infinitesimal generator. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.LocalDiffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard
open KLSLevyAdapter KLSLevyProbe
universe u
variable {N d : ℕ}

def observableGenerator (b : (Fin N → ℝ) → Fin N → ℝ)
    (s : Fin d → (Fin N → ℝ) → Fin N → ℝ)
    (f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ)
    (f'' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ)
    (z : Fin N → ℝ) : ℝ :=
  (∑ a : Fin N, coordDeriv f' a z * b z a) +
    1/2 * ∑ a : Fin N, ∑ c : Fin N, coordDeriv₂ f'' a c z *
      ∑ k : Fin d, s k z a * s k z c

theorem integral_generator_sums {ν : Measure ℝ}
    {F : Fin N → ℝ → ℝ} {G : Fin N → Fin N → ℝ → ℝ}
    (hF : ∀ a, Integrable (F a) ν) (hG : ∀ a c, Integrable (G a c) ν) :
    (∫ t, (∑ a : Fin N, F a t) + 1/2 * ∑ a : Fin N, ∑ c : Fin N, G a c t ∂ν) =
      (∑ a : Fin N, ∫ t, F a t ∂ν) + 1/2 * ∑ a : Fin N, ∑ c : Fin N, ∫ t, G a c t ∂ν := by
  rw [integral_add (integrable_finsetSum _ fun a _ => hF a)
    ((integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ => hG a c).const_mul _),
    integral_finsetSum _ (fun a _ => hF a), integral_const_mul,
    integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun c _ => hG a c)]
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  exact integral_finsetSum _ fun c _ => hG a c

namespace LocalProcess
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ} {R : ℝ}
  (D : LocalProcess W ℱ hW b s R)
  {f : (Fin N → ℝ) → ℝ}
  {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}

theorem itoFormula_original_generator
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (hfC : ContDiff ℝ 2 f) (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z) (hc : Continuous f') (hc₂ : Continuous f'')
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ z, ‖f' z‖ ≤ K)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      f (D.pair.Y T ω) - f (D.pair.Y 0 ω) =
        (∫ t in Icc (0 : ℝ) T, observableGenerator b s f' f'' (D.pair.Y t ω) ∂volume) +
        ∑ a : Fin N, ∑ k : Fin d, D.observableNoiseIntegral f' hc hK0 hK a k T ω := by
  filter_upwards [D.itoFormula_original_bounded_derivative hℱ0 hnull hfC hf hf' hc hK0 hK hT]
    with ω hω hle
  rw [hω hle, integral_Icc_eq_integral_Ioc]
  have hY := D.pair.ito_Y.continuous_path ω
  have hF (a : Fin N) : IntegrableOn
      (fun t => coordDeriv f' a (D.pair.Y t ω) * b (D.pair.Y t ω) a) (Ioc (0 : ℝ) T) volume :=
    (((continuous_coordDeriv hc a).comp hY).mul
      (((continuous_apply a).comp D.drift_continuous).comp hY)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hG (a c : Fin N) : IntegrableOn
      (fun t => coordDeriv₂ f'' a c (D.pair.Y t ω) *
        ∑ k : Fin d, s k (D.pair.Y t ω) a * s k (D.pair.Y t ω) c) (Ioc (0 : ℝ) T) volume := by
    have hcG : Continuous (fun t => coordDeriv₂ f'' a c (D.pair.Y t ω) *
        ∑ k : Fin d, s k (D.pair.Y t ω) a * s k (D.pair.Y t ω) c) := by
      apply ((continuous_coordDeriv₂ hc₂ a c).comp hY).mul
      apply continuous_finset_sum
      intro k _
      exact (((continuous_apply a).comp (D.diffusion_continuous k)).comp hY).mul
        (((continuous_apply c).comp (D.diffusion_continuous k)).comp hY)
    exact hcG.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [show (∫ t in Ioc (0 : ℝ) T, observableGenerator b s f' f'' (D.pair.Y t ω) ∂volume) =
      (∑ a : Fin N, ∫ t in Ioc (0 : ℝ) T, coordDeriv f' a (D.pair.Y t ω) * b (D.pair.Y t ω) a ∂volume) +
      1/2 * ∑ a : Fin N, ∑ c : Fin N, ∫ t in Ioc (0 : ℝ) T,
        coordDeriv₂ f'' a c (D.pair.Y t ω) *
          ∑ k : Fin d, s k (D.pair.Y t ω) a * s k (D.pair.Y t ω) c ∂volume from
    integral_generator_sums hF hG]
  ring

end LocalProcess
end KLS.LocalDiffusion
end
#print axioms KLS.LocalDiffusion.LocalProcess.itoFormula_original_generator
