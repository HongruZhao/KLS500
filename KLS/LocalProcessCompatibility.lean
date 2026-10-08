import KLS.CommonExitEnergy

/-! Pathwise agreement and equality of genuine exits for the constructed ball extensions. -/
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

theorem commonDifference_ae_zero (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ R₁) (hρ₂ : ρ ≤ R₂)
    {T : ℝ} (hT : 0 < T) : commonDifference D₁ D₂ ρ T =ᵐ[P] 0 := by
  obtain ⟨L, hL⟩ := D₁.lipschitz
  let C : ℝ := (N : ℝ)^2 * (2 * (T + (d : ℝ)^2) * L^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCeq : ENNReal.ofReal C =
      (N : ℝ≥0∞)^2 * (2 * (ENNReal.ofReal T + (d : ℝ≥0∞)^2) * ENNReal.ofReal (L^2)) := by
    dsimp [C]
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add hT.le (sq_nonneg _),
      ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_pow (Nat.cast_nonneg _)]
    norm_num
  have hbd : ∀ t ∈ Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i, (commonDifference D₁ D₂ ρ t ω i)^2) ∂P ≤
        ENNReal.ofReal C * ∫⁻ ω, ∫⁻ u in Icc (0 : ℝ) t,
          ∑ i, (‖commonDifference D₁ D₂ ρ u ω i‖₊ : ℝ≥0∞)^2 ∂volume ∂P := by
    intro t ht
    rcases ht.1.eq_or_lt with he | he
    · have hz : (∫⁻ ω, ENNReal.ofReal (∑ i, (commonDifference D₁ D₂ ρ t ω i)^2) ∂P) = 0 := by
        rw [← he]
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [commonDifference_initial D₁ D₂ ρ] with ω hω
        simp [hω]
      rw [hz]
      exact zero_le
    · refine (commonDifference_energy_le D₁ D₂ ρ hρ hρ₁ hρ₂ hL he).trans ?_
      rw [hCeq]
      apply mul_le_mul' _ le_rfl
      apply mul_le_mul' le_rfl
      apply mul_le_mul' _ le_rfl
      apply mul_le_mul' le_rfl
      exact add_le_add (ENNReal.ofReal_le_ofReal ht.2) le_rfl
  exact ae_zero_of_perTime_energy_bound (commonDifference_measurable D₁ D₂ ρ)
    (commonDifference_sup_energy D₁ D₂ ρ hρ) hT hC hbd T ⟨hT.le, le_rfl⟩

/-- Fixed-time compatibility is proved from the actual local SDEs and their
Lipschitz extensions; no uniqueness or stopped-energy premise is assumed. -/
theorem ae_eq_before_commonExit (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ R₁) (hρ₂ : ρ ≤ R₂)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ commonExit D₁ D₂ ρ ω → D₁.pair.Y T ω = D₂.pair.Y T ω := by
  filter_upwards [commonDifference_ae_zero D₁ D₂ ρ hρ hρ₁ hρ₂ hT] with ω hω he
  funext i
  have hi := congrFun hω i
  simp only [commonDifference, Probability.stopped, if_pos he, Pi.zero_apply] at hi
  exact sub_eq_zero.mp hi

/-- One common full-probability event carries agreement at every time up to the
common genuine norm exit. -/
theorem ae_all_eq_before_commonExit (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ R₁) (hρ₂ : ρ ≤ R₂) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ commonExit D₁ D₂ ρ ω →
      D₁.pair.Y t ω = D₂.pair.Y t ω :=
  ae_all_eq_before_cutoff D₁.pair.ito_Y.continuous_path D₂.pair.ito_Y.continuous_path
    (by filter_upwards [D₁.initial_Y, D₂.initial_Y] with ω h1 h2; exact h1.trans h2.symm)
    (fun _ ht => ae_eq_before_commonExit D₁ D₂ ρ hρ hρ₁ hρ₂ ht)

/-- Because both representatives are continuous, their same-radius exits agree. -/
theorem ae_exit_eq (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ R₁) (hρ₂ : ρ ≤ R₂) :
    D₁.pair.exit ρ =ᵐ[P] D₂.pair.exit ρ := by
  filter_upwards [ae_all_eq_before_commonExit D₁ D₂ ρ hρ hρ₁ hρ₂] with ω hω
  exact exitTime_eq_of_eq_before_common (D₁.pair.ito_Y.continuous_path ω)
    (D₂.pair.ito_Y.continuous_path ω) ρ (fun t ht h1 h2 => hω t ht (le_min h1 h2))

/-- The ball extensions agree up to either process's smaller-radius exit. -/
theorem ae_all_eq_before_exit (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ R₁) (hρ₂ : ρ ≤ R₂) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ D₁.pair.exit ρ ω →
      D₁.pair.Y t ω = D₂.pair.Y t ω := by
  filter_upwards [ae_all_eq_before_commonExit D₁ D₂ ρ hρ hρ₁ hρ₂,
    ae_exit_eq D₁ D₂ ρ hρ hρ₁ hρ₂] with ω hω heq t ht hle
  apply hω t ht
  exact le_min hle (heq ▸ hle)

end KLS.LocalDiffusion
end
#print axioms KLS.LocalDiffusion.commonDifference_ae_zero
#print axioms KLS.LocalDiffusion.ae_all_eq_before_exit
#print axioms KLS.LocalDiffusion.ae_exit_eq
