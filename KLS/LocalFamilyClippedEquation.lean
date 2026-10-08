import KLS.LocalFamilyCoefficientExit

/-! Original and clipped Brownian equations agree before the genuine joint exit. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.LocalDiffusion.LocalProcessFamily
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Picard
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ}
  (D : LocalProcessFamily W ℱ hW b s)

theorem noiseIntegral_eq_clipped_before_joint (m L : ℕ) (i : Fin N) (k : Fin d)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.jointCoefficientExit m L ω →
      D.noiseIntegral m i k T ω = D.clippedNoiseIntegral L i k T ω := by
  let τ := D.jointCoefficientExit m L
  have hτ := D.jointCoefficientExit_isStoppingTime m L
  have hm₁ := D.noise_measurable m i k
  have hp₁ := D.noise_progressive m i k
  have hq₁ := D.noise_energy m i k
  have hm₂ := D.clippedNoise_measurable L i k
  have hp₂ := D.clippedNoise_progressive L i k
  have hq₂ := D.clippedNoise_energy L i k
  have hagree : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Probability.stopped τ (D.noise m i k) ω t = Probability.stopped τ (D.clippedNoise L i k) ω t := by
    filter_upwards [D.ae_clipped_eq_before_joint m L] with ω hc t ht
    unfold Probability.stopped
    by_cases he : (t : WithTop ℝ) ≤ τ ω
    · rw [if_pos he, if_pos he]
      unfold noise Probability.stopped
      rw [if_pos (le_min_iff.mp he).1]
      exact ((hc t ht he).2 i k).symm
    · rw [if_neg he, if_neg he]
  have hi := stochasticIntegral_congr_ae_nonneg (W.W k) ℱ (hW k)
    (Probability.measurable_uncurry_stopped hτ hm₁) (Probability.measurable_uncurry_stopped hτ hm₂)
    (hp₁.stopped hτ) (hp₂.stopped hτ)
    (energy_lt_top_of_abs_le (fun ω t => Probability.abs_stopped_le τ (D.noise m i k) ω t) hq₁)
    (energy_lt_top_of_abs_le (fun ω t => Probability.abs_stopped_le τ (D.clippedNoise L i k) ω t) hq₂)
    hagree hT
  have h₁ := stochasticIntegralBrownian_stopped_eq_of_le τ (W.W k) ℱ (hW k) hτ hm₁ hp₁ hq₁ hT
  have h₂ := stochasticIntegralBrownian_stopped_eq_of_le τ (W.W k) ℱ (hW k) hτ hm₂ hp₂ hq₂ hT
  filter_upwards [hi, h₁, h₂] with ω hiω h₁ω h₂ω he
  exact (h₁ω he).symm.trans (hiω.trans (h₂ω he))

theorem clipped_equation_before_joint (m L : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.jointCoefficientExit m L ω → ∀ i : Fin N,
      D.path T ω i = (∫ t in Icc (0 : ℝ) T, D.clippedDrift L i ω t ∂volume) +
        ∑ k : Fin d, D.clippedNoiseIntegral L i k T ω := by
  have hn := ae_all_iff.mpr fun i : Fin N => ae_all_iff.mpr fun k : Fin d =>
    D.noiseIntegral_eq_clipped_before_joint m L i k hT
  filter_upwards [D.originalEquation m hT, D.ae_clipped_eq_before_joint m L, hn]
    with ω he hc hnω hj i
  have hd : (∫ t in Icc (0 : ℝ) T, b (D.path t ω) i ∂volume) =
      ∫ t in Icc (0 : ℝ) T, D.clippedDrift L i ω t ∂volume := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    exact ((hc t ht.1 ((show (t : WithTop ℝ) ≤ (T : WithTop ℝ) by exact_mod_cast ht.2).trans hj)).1 i).symm
  exact (he (le_min_iff.mp hj).1 i).trans (congrArg₂ (fun x y : ℝ => x+y) hd
    (Finset.sum_congr rfl fun k _ => hnω i k hj))

end KLS.LocalDiffusion.LocalProcessFamily
end
#print axioms KLS.LocalDiffusion.LocalProcessFamily.clipped_equation_before_joint
