import KLS.LocalObservableCutoff

/-! Genuine local Itô formula without a global derivative bound on the observable. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.LocalDiffusion.LocalProcess
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLSLevyProbe
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ} {R : ℝ}
  (D : LocalProcess W ℱ hW b s R) (f : (Fin N → ℝ) → ℝ)
  (hf : ContDiff ℝ (⊤ : ℕ∞) f)

theorem smoothObservableNoise_eq_cutoff (a : Fin N) (k : Fin d) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      D.observableNoise (fderiv ℝ f) a k ω t =
      D.observableNoise (fderiv ℝ (cutoffObservable f R)) a k ω t := by
  filter_upwards [D.initial_Y] with ω h0 t ht
  unfold observableNoise noise Probability.stopped
  change _ * (if (t : WithTop ℝ) ≤ D.exit ω then _ else 0) =
    _ * (if (t : WithTop ℝ) ≤ D.exit ω then _ else 0)
  split_ifs with he
  · rw [show coordDeriv (fderiv ℝ (cutoffObservable f R)) a (D.pair.Y t ω) =
        coordDeriv (fderiv ℝ f) a (D.pair.Y t ω) by
      unfold coordDeriv
      rw [fderiv_cutoffObservable_eq f R (D.norm_le_before_exit ω h0 ht he)]]
  · simp

include hf in
theorem smoothObservableNoise_energy (a : Fin N) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.observableNoise (fderiv ℝ f) a k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_fderiv_cutoffObservable hf R
  have he : (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.observableNoise (fderiv ℝ f) a k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) =
      ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.observableNoise (fderiv ℝ (cutoffObservable f R)) a k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P := by
    apply lintegral_congr_ae
    filter_upwards [D.smoothObservableNoise_eq_cutoff f a k] with ω hω
    exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hω t ht.1]
  rw [he]
  exact D.observableNoise_energy _ hK0 hK a k T hT

def smoothObservableNoiseIntegral (a : Fin N) (k : Fin d) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.observableNoise (fderiv ℝ f) a k)
    (D.observableNoise_measurable _ (hf.continuous_fderiv (by simp)) a k)
    (D.observableNoise_progressive _ (hf.continuous_fderiv (by simp)) a k)
    (D.smoothObservableNoise_energy f hf a k) T

theorem smoothObservableNoiseIntegral_eq_cutoff {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ z, ‖fderiv ℝ (cutoffObservable f R) z‖ ≤ K)
    (a : Fin N) (k : Fin d) {T : ℝ} (hT : 0 < T) :
    D.smoothObservableNoiseIntegral f hf a k T =ᵐ[P]
      D.observableNoiseIntegral (fderiv ℝ (cutoffObservable f R))
        ((contDiff_cutoffObservable hf R).continuous_fderiv (by simp)) hK0 hK a k T :=
  stochasticIntegral_congr_ae_nonneg (W.W k) ℱ (hW k)
    (D.observableNoise_measurable _ (hf.continuous_fderiv (by simp)) a k)
    (D.observableNoise_measurable _ ((contDiff_cutoffObservable hf R).continuous_fderiv (by simp)) a k)
    (D.observableNoise_progressive _ (hf.continuous_fderiv (by simp)) a k)
    (D.observableNoise_progressive _ ((contDiff_cutoffObservable hf R).continuous_fderiv (by simp)) a k)
    (D.smoothObservableNoise_energy f hf a k) (D.observableNoise_energy _ hK0 hK a k)
    (D.smoothObservableNoise_eq_cutoff f a k) hT

/-- The Brownian integrals contain the actual derivative of the original smooth
observable, multiplied by the original diffusion and stopped at the actual exit. -/
theorem itoFormula_original_smooth
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      f (D.pair.Y T ω) - f (D.pair.Y 0 ω) =
        (∫ t in Icc (0 : ℝ) T,
          observableGenerator b s (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f)) (D.pair.Y t ω) ∂volume) +
        ∑ a : Fin N, ∑ k : Fin d, D.smoothObservableNoiseIntegral f hf a k T ω := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_fderiv_cutoffObservable hf R
  have hg := contDiff_cutoffObservable hf R
  have hg' := hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hi := D.itoFormula_original_generator hℱ0 hnull (hg.of_le (by simp))
    (fun z => (hg.differentiable (by simp) z).hasFDerivAt)
    (fun z => (hg'.differentiable (by simp) z).hasFDerivAt)
    hg'.continuous (hg'.continuous_fderiv (by simp)) hK0 hK hT
  have hn : ∀ᵐ ω ∂P, ∀ a : Fin N, ∀ k : Fin d,
      D.smoothObservableNoiseIntegral f hf a k T ω =
      D.observableNoiseIntegral (fderiv ℝ (cutoffObservable f R))
        (hg.continuous_fderiv (by simp)) hK0 hK a k T ω :=
    ae_all_iff.mpr fun a => ae_all_iff.mpr fun k =>
      D.smoothObservableNoiseIntegral_eq_cutoff f hf hK0 hK a k hT
  filter_upwards [hi, hn, D.initial_Y] with ω hiω hnω h0 hle
  have hnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖D.pair.Y t ω‖ ≤ R :=
    D.norm_le_before_exit ω h0 ht.1 ((show (t : WithTop ℝ) ≤ (T : WithTop ℝ) by exact_mod_cast ht.2).trans hle)
  have hgen : (∫ t in Icc (0 : ℝ) T,
      observableGenerator b s (fderiv ℝ (cutoffObservable f R))
        (fderiv ℝ (fderiv ℝ (cutoffObservable f R))) (D.pair.Y t ω) ∂volume) =
      ∫ t in Icc (0 : ℝ) T,
      observableGenerator b s (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f)) (D.pair.Y t ω) ∂volume := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    unfold observableGenerator coordDeriv coordDeriv₂
    rw [fderiv_cutoffObservable_eq f R (hnorm t ht),
      fderiv_fderiv_cutoffObservable_eq f R (hnorm t ht)]
  have hs : (∑ a : Fin N, ∑ k : Fin d,
      D.observableNoiseIntegral (fderiv ℝ (cutoffObservable f R))
        (hg.continuous_fderiv (by simp)) hK0 hK a k T ω) =
      ∑ a : Fin N, ∑ k : Fin d, D.smoothObservableNoiseIntegral f hf a k T ω := by
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_congr rfl fun k _ => (hnω a k).symm
  have hiω' := hiω hle
  rw [cutoffObservable_eq f R (hnorm T ⟨hT.le, le_rfl⟩),
    cutoffObservable_eq f R (hnorm 0 ⟨le_rfl, hT.le⟩), hgen, hs] at hiω'
  exact hiω'

end KLS.LocalDiffusion.LocalProcess
end
#print axioms KLS.LocalDiffusion.LocalProcess.itoFormula_original_smooth
