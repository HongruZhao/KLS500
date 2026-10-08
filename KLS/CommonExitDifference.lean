import KLS.LocalStoppedPair

/-! Measurability, finite energy and coefficient bounds at the common genuine exit. -/
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

def commonExit : Ω → WithTop ℝ := fun ω => min (D₁.pair.exit ρ ω) (D₂.pair.exit ρ ω)

theorem commonExit_isStoppingTime : IsStoppingTime ℱ (commonExit D₁ D₂ ρ) := by
  intro t
  simpa only [commonExit, min_le_iff, setOf_or] using
    (D₁.pair.exit_isStoppingTime ρ t).union (D₂.pair.exit_isStoppingTime ρ t)

def commonDifference (t : ℝ) (ω : Ω) (i : Fin N) : ℝ :=
  Probability.stopped (commonExit D₁ D₂ ρ)
    (fun ω t => D₁.pair.Y t ω i - D₂.pair.Y t ω i) ω t

theorem commonDifference_measurable :
    Measurable (Function.uncurry fun ω t => commonDifference D₁ D₂ ρ t ω) := by
  apply measurable_pi_lambda
  intro i
  exact Probability.measurable_uncurry_stopped (commonExit_isStoppingTime D₁ D₂ ρ)
    ((D₁.pair.ito_Y.measurable_uncurry_comp (measurable_pi_apply i)).sub
      (D₂.pair.ito_Y.measurable_uncurry_comp (measurable_pi_apply i)))

theorem norm_le_of_le_exit {R : ℝ} (D : LocalProcess W ℱ hW b s R)
    {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) {ω : Ω} (h0 : D.pair.Y 0 ω = 0)
    (he : (t : WithTop ℝ) ≤ D.pair.exit r ω) : ‖D.pair.Y t ω‖ ≤ r := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, h0, norm_zero]; exact hr
  · exact D.pair.norm_le_before_exit ω h he

theorem commonDifference_norm_bound (hρ : 0 ≤ ρ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin N,
      ‖commonDifference D₁ D₂ ρ t ω i‖ ≤ 2 * ρ := by
  filter_upwards [D₁.initial_Y, D₂.initial_Y] with ω h0 h0' t ht i
  unfold commonDifference Probability.stopped
  split_ifs with he
  · have h1 := norm_le_of_le_exit D₁ hρ ht h0 ((le_min_iff.mp he).1)
    have h2 := norm_le_of_le_exit D₂ hρ ht h0' ((le_min_iff.mp he).2)
    calc ‖D₁.pair.Y t ω i - D₂.pair.Y t ω i‖
        ≤ ‖D₁.pair.Y t ω i‖ + ‖D₂.pair.Y t ω i‖ := norm_sub_le _ _
      _ ≤ ρ + ρ := add_le_add ((norm_le_pi_norm _ i).trans h1) ((norm_le_pi_norm _ i).trans h2)
      _ = 2 * ρ := by ring
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hρ

theorem commonDifference_sup_energy (hρ : 0 ≤ ρ) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (⨆ t : Icc (0 : ℝ) T,
      ∑ i, (‖commonDifference D₁ D₂ ρ (t : ℝ) ω i‖₊ : ℝ≥0∞)^2) ∂P < ⊤ := by
  have hbd : ∀ᵐ ω ∂P, (⨆ t : Icc (0 : ℝ) T,
      ∑ i, (‖commonDifference D₁ D₂ ρ (t : ℝ) ω i‖₊ : ℝ≥0∞)^2)
      ≤ (N : ℝ≥0∞) * ENNReal.ofReal ((2 * ρ)^2) := by
    filter_upwards [commonDifference_norm_bound D₁ D₂ ρ hρ] with ω hω
    apply iSup_le
    intro t
    calc ∑ i, (‖commonDifference D₁ D₂ ρ (t : ℝ) ω i‖₊ : ℝ≥0∞)^2
        ≤ ∑ _i : Fin N, ENNReal.ofReal ((2 * ρ)^2) := by
          apply Finset.sum_le_sum
          intro i _
          rw [ennreal_nnnorm_sq_normed]
          apply ENNReal.ofReal_le_ofReal
          exact pow_le_pow_left₀ (norm_nonneg _) (hω t t.2.1 i) 2
      _ = _ := by simp
  refine lt_of_le_of_lt (lintegral_mono_ae hbd) ?_
  simp only [lintegral_const, measure_univ, mul_one]
  finiteness

theorem commonDifference_initial : commonDifference D₁ D₂ ρ 0 =ᵐ[P] 0 := by
  filter_upwards [D₁.initial_Y, D₂.initial_Y] with ω h1 h2
  funext i
  simp [commonDifference, Probability.stopped, h1, h2]

/-- The actual stopped coefficients are read as the first extension at both states,
which are in its agreement ball before the common exit. -/
theorem common_stopped_coefficients (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ R₁) (hρ₂ : ρ ≤ R₂) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ commonExit D₁ D₂ ρ ω →
      D₁.extension.μ t (D₁.pair.X t ω) = D₁.extension.μ t (D₁.pair.Y t ω) ∧
      D₂.extension.μ t (D₂.pair.X t ω) = D₁.extension.μ t (D₂.pair.Y t ω) ∧
      (∀ i k, D₁.extension.σ t (D₁.pair.X t ω) i k = D₁.extension.σ t (D₁.pair.Y t ω) i k) ∧
      (∀ i k, D₂.extension.σ t (D₂.pair.X t ω) i k = D₁.extension.σ t (D₂.pair.Y t ω) i k) := by
  filter_upwards [D₁.initial_Y, D₂.initial_Y, D₁.pair.path_eq, D₂.pair.path_eq]
    with ω h0 h0' he1 he2 t ht he
  rw [he1 t ht, he2 t ht]
  have hn := norm_le_of_le_exit D₂ hρ ht h0' (le_min_iff.mp he).2
  exact ⟨rfl, (D₂.drift_eq t _ (hn.trans hρ₂)).trans (D₁.drift_eq t _ (hn.trans hρ₁)).symm,
    fun _ _ => rfl, fun i k => (D₂.diffusion_eq t _ (hn.trans hρ₂) i k).trans
      (D₁.diffusion_eq t _ (hn.trans hρ₁) i k).symm⟩

theorem common_stopped_coefficients_sq_bound (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ R₁) (hρ₂ : ρ ≤ R₂)
    {L : ℝ} (hL : D₁.extension.IsLipschitz (0 : Measure Unit) L) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      (∀ i, (D₁.stoppedDrift (commonExit D₁ D₂ ρ) i ω t -
        D₂.stoppedDrift (commonExit D₁ D₂ ρ) i ω t)^2 ≤
        L^2 * ∑ j, (commonDifference D₁ D₂ ρ t ω j)^2) ∧
      (∀ i k, (D₁.stoppedDiffusion (commonExit D₁ D₂ ρ) i k ω t -
        D₂.stoppedDiffusion (commonExit D₁ D₂ ρ) i k ω t)^2 ≤
        L^2 * ∑ j, (commonDifference D₁ D₂ ρ t ω j)^2) := by
  filter_upwards [common_stopped_coefficients D₁ D₂ ρ hρ hρ₁ hρ₂]
    with ω hω t ht
  by_cases he : (t : WithTop ℝ) ≤ commonExit D₁ D₂ ρ ω
  · obtain ⟨hb1, hb2, hs1, hs2⟩ := hω t ht he
    simp only [LocalProcess.stoppedDrift, LocalProcess.stoppedDiffusion,
      commonDifference, Probability.stopped, if_pos he]
    have hnorm := mul_le_mul_of_nonneg_left
      (sq_norm_le_sum_sq (D₁.pair.Y t ω - D₂.pair.Y t ω)) (sq_nonneg L)
    constructor
    · intro i
      rw [congrFun hb1 i, congrFun hb2 i]
      have hb := mu_lip_componentwise D₁.extension hL t (D₁.pair.Y t ω) (D₂.pair.Y t ω) i
      have hb' := pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [sq_abs, mul_pow] at hb'
      exact hb'.trans hnorm
    · intro i k
      rw [hs1 i k, hs2 i k]
      refine le_trans ?_ ((hL.2.2.1 t (D₁.pair.Y t ω) (D₂.pair.Y t ω)).trans hnorm)
      exact (Finset.single_le_sum
        (f := fun k => (D₁.extension.σ t (D₁.pair.Y t ω) i k - D₁.extension.σ t (D₂.pair.Y t ω) i k)^2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ k)).trans
        (Finset.single_le_sum
          (f := fun i => ∑ k, (D₁.extension.σ t (D₁.pair.Y t ω) i k - D₁.extension.σ t (D₂.pair.Y t ω) i k)^2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i))
  · simp [LocalProcess.stoppedDrift, LocalProcess.stoppedDiffusion,
      commonDifference, Probability.stopped, he]

end KLS.LocalDiffusion
end
#print axioms KLS.LocalDiffusion.commonDifference_sup_energy
#print axioms KLS.LocalDiffusion.common_stopped_coefficients_sq_bound
