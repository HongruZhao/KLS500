import KLS.StoppedEnergyToolkit
import KLS.StoppedGronwall
import KLS.ContinuousExitCompatibility

/-! The homogeneous second-moment estimate for two actual ball extensions. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
namespace KLS.LocalDiffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard
open KLSLevyAdapter KLSLevyProbe
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ}
  {R₁ R₂ : ℝ} (D₁ : LocalProcess W ℱ hW b s R₁) (D₂ : LocalProcess W ℱ hW b s R₂)
  (ρ : ℝ)

set_option maxHeartbeats 800000 in
theorem commonDifference_energy_le (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ R₁) (hρ₂ : ρ ≤ R₂)
    {L t : ℝ} (hL : D₁.extension.IsLipschitz (0 : Measure Unit) L) (ht : 0 < t) :
    ∫⁻ ω, ENNReal.ofReal (∑ i, (commonDifference D₁ D₂ ρ t ω i)^2) ∂P ≤
      (N : ℝ≥0∞)^2 * (2 * (ENNReal.ofReal t + (d : ℝ≥0∞)^2) * ENNReal.ofReal (L^2)) *
        ∫⁻ ω, ∫⁻ u in Icc (0 : ℝ) t,
          ∑ i, (‖commonDifference D₁ D₂ ρ u ω i‖₊ : ℝ≥0∞)^2 ∂volume ∂P := by
  let τ := commonExit D₁ D₂ ρ
  have hτ := commonExit_isStoppingTime D₁ D₂ ρ
  let I : ℝ≥0∞ := ∫⁻ ω, ∫⁻ u in Icc (0 : ℝ) t,
    ∑ i, (‖commonDifference D₁ D₂ ρ u ω i‖₊ : ℝ≥0∞)^2 ∂volume ∂P
  let K : ℝ≥0∞ := ENNReal.ofReal (L^2)
  have hcoeff := common_stopped_coefficients_sq_bound D₁ D₂ ρ hρ hρ₁ hρ₂ hL
  have hb (i : Fin N) :
      ∫⁻ ω, ∫⁻ u in Icc (0 : ℝ) t,
        (‖D₁.stoppedDrift τ i ω u - D₂.stoppedDrift τ i ω u‖₊ : ℝ≥0∞)^2 ∂volume ∂P ≤ K * I :=
    energy_le_of_ae_sq_bound (hcoeff.mono fun ω hω u hu => (hω u hu).1 i)
  have hs (i : Fin N) (k : Fin d) :
      ∫⁻ ω, ∫⁻ u in Icc (0 : ℝ) t,
        (‖D₁.stoppedDiffusion τ i k ω u - D₂.stoppedDiffusion τ i k ω u‖₊ : ℝ≥0∞)^2 ∂volume ∂P ≤ K * I :=
    energy_le_of_ae_sq_bound (hcoeff.mono fun ω hω u hu => (hω u hu).2 i k)
  have hv := lintegral_sq_norm_vectorItoProcess_sub_le W ℱ hW
    (D₂.stoppedDiffusion_measurable τ hτ) (D₂.stoppedDiffusion_progressive τ hτ)
    (D₂.stoppedDiffusion_energy τ)
    (D₁.stoppedDiffusion_measurable τ hτ) (D₁.stoppedDiffusion_progressive τ hτ)
    (D₁.stoppedDiffusion_energy τ) (X₀ := 0) (fun _ => measurable_const)
    (D₂.stoppedDrift_measurable τ hτ) (D₁.stoppedDrift_measurable τ hτ)
    ht (D₂.stoppedDrift_energy τ) (D₁.stoppedDrift_energy τ)
  change (∫⁻ ω, (‖D₁.stoppedIto τ hτ t ω - D₂.stoppedIto τ hτ t ω‖₊ : ℝ≥0∞)^2 ∂P) ≤ _ at hv
  have hvb : ∫⁻ ω, (‖D₁.stoppedIto τ hτ t ω - D₂.stoppedIto τ hτ t ω‖₊ : ℝ≥0∞)^2 ∂P ≤
      (N : ℝ≥0∞) * (2 * (ENNReal.ofReal t + (d : ℝ≥0∞)^2) * K) * I := by
    refine hv.trans ?_
    calc (∑ i : Fin N, (2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ u in Icc (0 : ℝ) t,
          (‖D₁.stoppedDrift τ i ω u - D₂.stoppedDrift τ i ω u‖₊ : ℝ≥0∞)^2 ∂volume ∂P) +
        2 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ u in Icc (0 : ℝ) t,
          (‖D₁.stoppedDiffusion τ i k ω u - D₂.stoppedDiffusion τ i k ω u‖₊ : ℝ≥0∞)^2 ∂volume ∂P)))
        ≤ ∑ _i : Fin N, (2 * (ENNReal.ofReal t * (K * I)) +
          2 * ((d : ℝ≥0∞) * ((d : ℝ≥0∞) * (K * I)))) := by
            apply Finset.sum_le_sum
            intro i _
            apply add_le_add (mul_le_mul' le_rfl (mul_le_mul' le_rfl (hb i)))
            apply mul_le_mul' le_rfl
            apply mul_le_mul' le_rfl
            calc (∑ k : Fin d, ∫⁻ ω, ∫⁻ u in Icc (0 : ℝ) t,
                  (‖D₁.stoppedDiffusion τ i k ω u - D₂.stoppedDiffusion τ i k ω u‖₊ : ℝ≥0∞)^2 ∂volume ∂P)
                ≤ ∑ _k : Fin d, K * I := Finset.sum_le_sum fun k _ => hs i k
              _ = _ := by simp
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  rw [lintegral_ofReal_sum_sq_eq]
  have hred : (∫⁻ ω, ∑ i, (‖commonDifference D₁ D₂ ρ t ω i‖₊ : ℝ≥0∞)^2 ∂P) ≤
      (N : ℝ≥0∞) * ∫⁻ ω, (‖D₁.stoppedIto τ hτ t ω - D₂.stoppedIto τ hτ t ω‖₊ : ℝ≥0∞)^2 ∂P := by
    rw [← lintegral_const_mul' _ _ (by finiteness : (N : ℝ≥0∞) ≠ ⊤)]
    apply lintegral_mono_ae
    filter_upwards [D₁.stoppedIto_eq_before τ hτ ht, D₂.stoppedIto_eq_before τ hτ ht]
      with ω h1 h2
    by_cases he : (t : WithTop ℝ) ≤ τ ω
    · have heq : commonDifference D₁ D₂ ρ t ω = D₁.stoppedIto τ hτ t ω - D₂.stoppedIto τ hτ t ω := by
        funext i
        simp only [commonDifference, Probability.stopped, show (t : WithTop ℝ) ≤ commonExit D₁ D₂ ρ ω from he,
          if_true, h1 he, h2 he, Pi.sub_apply]
      rw [heq]
      exact sum_sq_nnnorm_le_dim _
    · simp [commonDifference, Probability.stopped, show ¬ (t : WithTop ℝ) ≤ commonExit D₁ D₂ ρ ω from he]
  refine hred.trans ((mul_le_mul' le_rfl hvb).trans (le_of_eq ?_))
  dsimp only [K, I]
  ring

end KLS.LocalDiffusion
end
#print axioms KLS.LocalDiffusion.commonDifference_energy_le
