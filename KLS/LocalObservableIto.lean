import KLS.LocalObservableNoise

/-! Itô's formula with the original coefficients up to the genuine local exit. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.LocalDiffusion.LocalProcess
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard
open KLSLevyAdapter KLSLevyProbe
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ} {R : ℝ}
  (D : LocalProcess W ℱ hW b s R)
  {f : (Fin N → ℝ) → ℝ}
  {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ}

/-- A genuine local Itô formula. The noise is the original diffusion multiplied
by the actual gradient and stopped at the actual state exit time. -/
theorem itoFormula_original_bounded_derivative
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (hfC : ContDiff ℝ 2 f) (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z) (hc : Continuous f')
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ z, ‖f' z‖ ≤ K)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      f (D.pair.Y T ω) - f (D.pair.Y 0 ω) =
        (∑ a : Fin N, ∫ t in Ioc (0 : ℝ) T,
          coordDeriv f' a (D.pair.Y t ω) * b (D.pair.Y t ω) a ∂volume) +
        (∑ a : Fin N, ∑ k : Fin d, D.observableNoiseIntegral f' hc hK0 hK a k T ω) +
        1/2 * ∑ a : Fin N, ∑ c : Fin N, ∫ t in Ioc (0 : ℝ) T,
          coordDeriv₂ f'' a c (D.pair.Y t ω) *
            ∑ k : Fin d, s k (D.pair.Y t ω) a * s k (D.pair.Y t ω) c ∂volume := by
  obtain ⟨L, hL⟩ := D.lipschitz
  have hi := D.pair.itoFormula_bounded_derivative hℱ0 hnull D.regular hL
    hfC hf hf' hc hK0 hK hT
  have hn : ∀ᵐ ω ∂P, ∀ a : Fin N, ∀ k : Fin d, (T : WithTop ℝ) ≤ D.exit ω →
      D.observableNoiseIntegral f' hc hK0 hK a k T ω =
        stochasticIntegralBrownian (W.W k) ℱ (hW k)
          (fun ω t => coordDeriv f' a (D.pair.Y t ω) * D.extension.σ t (D.pair.X t ω) a k)
          (D.pair.weighted_diffusion_measurable hc a k)
          (D.pair.weighted_diffusion_progressive hc a k)
          (D.pair.weighted_diffusion_energy hK0 hK a k) T ω :=
    ae_all_iff.mpr fun a => ae_all_iff.mpr fun k =>
      D.observableNoiseIntegral_eq_before_exit f' hc hK0 hK a k hT
  filter_upwards [hi, hn, D.original_coefficients_before_exit] with ω hiω hnω hcoef hle
  rw [hiω]
  have ht (t : ℝ) (h : t ∈ Ioc (0 : ℝ) T) : (t : WithTop ℝ) ≤ D.exit ω :=
    (show (t : WithTop ℝ) ≤ (T : WithTop ℝ) by exact_mod_cast h.2).trans hle
  have hd : (∑ a : Fin N, ∫ t in Ioc (0 : ℝ) T,
      coordDeriv f' a (D.pair.Y t ω) * D.extension.μ t (D.pair.X t ω) a ∂volume) =
      ∑ a : Fin N, ∫ t in Ioc (0 : ℝ) T,
        coordDeriv f' a (D.pair.Y t ω) * b (D.pair.Y t ω) a ∂volume := by
    apply Finset.sum_congr rfl
    intro a _
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t h
    dsimp only
    rw [congrFun (hcoef t h.1.le (ht t h)).1 a]
  have hs : (∑ a : Fin N, ∑ c : Fin N, ∫ t in Ioc (0 : ℝ) T,
      coordDeriv₂ f'' a c (D.pair.Y t ω) *
        ∑ k : Fin d, D.extension.σ t (D.pair.X t ω) a k * D.extension.σ t (D.pair.X t ω) c k ∂volume) =
      ∑ a : Fin N, ∑ c : Fin N, ∫ t in Ioc (0 : ℝ) T,
        coordDeriv₂ f'' a c (D.pair.Y t ω) *
          ∑ k : Fin d, s k (D.pair.Y t ω) a * s k (D.pair.Y t ω) c ∂volume := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t h
    dsimp only
    simp_rw [(hcoef t h.1.le (ht t h)).2]
  rw [hd, hs]
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  exact (hnω a k hle).symm

end KLS.LocalDiffusion.LocalProcess
end
#print axioms KLS.LocalDiffusion.LocalProcess.itoFormula_original_bounded_derivative
