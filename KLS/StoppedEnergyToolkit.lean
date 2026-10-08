import KLS.CommonExitDifference

/-! Elementary energy comparison used for the concrete stopped coefficient differences. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
namespace KLS.LocalDiffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem energy_le_of_ae_sq_bound {F : Ω → ℝ → ℝ} {Z : ℝ → Ω → Fin N → ℝ}
    {L t : ℝ} (h : ∀ᵐ ω ∂P, ∀ u : ℝ, 0 ≤ u → (F ω u)^2 ≤ L^2 * ∑ i, (Z u ω i)^2) :
    ∫⁻ ω, ∫⁻ u in Icc (0 : ℝ) t, (‖F ω u‖₊ : ℝ≥0∞)^2 ∂volume ∂P ≤
      ENNReal.ofReal (L^2) * ∫⁻ ω, ∫⁻ u in Icc (0 : ℝ) t,
        ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞)^2 ∂volume ∂P := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [h] with ω hω
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro u hu
  rw [ennreal_nnnorm_sq_real]
  calc ENNReal.ofReal ((F ω u)^2) ≤ ENNReal.ofReal (L^2 * ∑ i, (Z u ω i)^2) :=
      ENNReal.ofReal_le_ofReal (hω u hu.1)
    _ = _ := by
      rw [ENNReal.ofReal_mul (sq_nonneg L), ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      congr 1
      exact Finset.sum_congr rfl fun i _ => (ennreal_nnnorm_sq_real _).symm

/-- A coordinate-square sum is bounded by the dimension times the squared sup norm. -/
theorem sum_sq_nnnorm_le_dim (x : Fin N → ℝ) :
    ∑ i, (‖x i‖₊ : ℝ≥0∞)^2 ≤ (N : ℝ≥0∞) * (‖x‖₊ : ℝ≥0∞)^2 := by
  calc ∑ i, (‖x i‖₊ : ℝ≥0∞)^2 ≤ ∑ _i : Fin N, (‖x‖₊ : ℝ≥0∞)^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply pow_le_pow_left'
        exact_mod_cast nnnorm_le_pi_nnnorm x i
      _ = _ := by simp

end KLS.LocalDiffusion
end
