/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.PicardSelfMap

/-!
# The Bielecki-norm contraction estimate for the Picard map

At each time of the window the `L²` mass of the difference of two Picard steps is bounded by
`9 n L² T` times the doubly-integrated energy of the difference of their arguments, so that under
the Bielecki weight `e^{-2βt}` the map contracts at rate `9 n L² T / (2β)`; together with the
threshold `9 n L² T < 2β` under which that rate is `< 1`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

set_option maxHeartbeats 4000000 in
-- The contraction chain rewrites the full three-component Picard term at each `t`;
-- the accumulated `gcongr`/`calc` steps exceed the default budget.
/-- **Picard step Bielecki β-norm contraction (per-time lintegral form).**

The headline contraction estimate. For each `t ∈ [0, T]`, the lintegral L²
mass of the Picard step difference is bounded by

  `9 · n · L² · T · ∫⁻ ω, ∫₀^t ‖X_s - Y_s‖² ds ∂P`,

via the triangle bound on the three components (factor 3) combined with
the uniform overbound `n L² t` on the σ-step and γ-step (factor 3 again
because `t ≤ T` is applied to a sum of three identical-shape bounds). The
literature-tight σ/γ bounds (`L²` per component without `n t`) tighten this
to the `3 n L² (T + 2) / (2β)` rate of `picardStep_bielecki_contraction_tight`.

After applying the Bielecki weight `e^{-2βt}` and using
`bielecki_weighted_integral_bound`, the per-`t` weighted bound is
`9 n L² T / (2β) · ‖X - Y‖²_β,T`. Together with
`picardStep_bielecki_contraction_rate_lt_one`, the Picard map is a strict
contraction in the Bielecki β-norm for `β > 9 n L² T / 2`.

The σ-step and γ-step bound hypotheses (`h_σ_step_bound`, `h_γ_step_bound`)
have the same signature shape as the drift bound
`picardStep_drift_diff_lintegral_sq_bound`. The well-posedness proof does
not go through this theorem: it uses the per-component estimates
`picardStep_diffusion_diff_lipschitz_sq_componentwise` and
`picardStep_jump_diff_lipschitz_sq_componentwise` through
`bieleckiNorm_picardStep_diff_le` (`Ito/PicardOutput.lean`). -/
theorem picardStep_bielecki_contraction
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L : ℝ} (hL_nn : 0 ≤ L)
    -- μ-Lipschitz (componentwise; used inside the drift lintegral bound):
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (T : ℝ) (_hT : 0 < T)
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_X : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_Y : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    -- Drift bound's a.e. hypotheses (must hold at every `t ∈ [0, T]`):
    (h_drift_bound_ae : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        ≤ (n : ℝ) * L ^ 2 * t *
            ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    (h_drift_inner_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, 0 ≤
      ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    -- σ-step lintegral bound (hypothesis — discharged by parallel σ-Lipschitz proof):
    (h_σ_step_bound : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
          - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2 * t) *
          ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P)
    -- γ-step lintegral bound (hypothesis — discharged by parallel γ-Lipschitz proof):
    (h_γ_step_bound : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2 * t) *
          ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P)
    -- AEMeasurability of the three component sum-of-squares ofReal functions.
    -- These are needed to split the triple-term lintegral on the RHS of
    -- `picardStep_diff_lintegral_sum_sq_le`. The downstream caller will produce
    -- them from joint measurability of X, Y and the σ/γ coefficient measurability.
    (h_drift_ofReal_aemeas : ∀ t : ℝ, AEMeasurable (fun ω : Ω => ENNReal.ofReal
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)) P)
    (h_diff_ofReal_aemeas : ∀ t : ℝ, AEMeasurable (fun ω : Ω => ENNReal.ofReal
      (∑ i : Fin n, ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
          - picardStep_diffusion W ℱ hℱW coeffs Y
              h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)) P)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep W N ℱ hℱW hℱN coeffs X x₀
          h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        - picardStep W N ℱ hℱW hℱN coeffs Y x₀
          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
    ≤ ENNReal.ofReal (9 * (n : ℝ) * L ^ 2 * T) *
        ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t,
          ‖X s ω - Y s ω‖ ^ 2) ∂P := by
  obtain ⟨ht_nn, ht_le⟩ := ht
  -- Drift bound at t (proven; from `Picard.lean`).
  have h_drift := picardStep_drift_diff_lintegral_sq_bound (E := E) P coeffs hL_nn h_μ_lip
    X Y x₀ t ht_nn (h_drift_bound_ae t ⟨ht_nn, ht_le⟩) (h_drift_inner_nn t ⟨ht_nn, ht_le⟩)
  -- σ + γ bounds at t (hypothesized).
  have h_σ := h_σ_step_bound t ⟨ht_nn, ht_le⟩
  have h_γ := h_γ_step_bound t ⟨ht_nn, ht_le⟩
  -- Triangle inequality bound (lintegral form; single-integral RHS).
  have h_triangle' := picardStep_diff_lintegral_sum_sq_le W N ℱ hℱW hℱN coeffs X Y x₀
    h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
    h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t
  -- Combine: triangle (single-integral RHS) bounded by 3 * (drift + σ + γ) bound sum.
  -- Rewrite the single-integral RHS as three separate integrals via the AEMeasurable hypotheses,
  -- then sum the three lintegral bounds.
  set Iω : ℝ≥0∞ :=
    ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t,
      ‖X s ω - Y s ω‖ ^ 2) ∂P with hIω_def
  set Bnt : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) * L ^ 2 * t) with hBnt_def
  -- h_drift, h_σ, h_γ are bounds of the form `lintegral ≤ Bnt * Iω` for each component.
  -- Sum: `drift_l + σ_l + γ_l ≤ 3 (Bnt * Iω)`.
  -- Step 1: Split the lintegral RHS in h_triangle' into three pieces.
  have h_split_2 : ∫⁻ ω, (ENNReal.ofReal
        (∑ i : Fin n,
          ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
        + ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N ℱ hℱN coeffs Y
                    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P
      = (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W ℱ hℱW coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
        + ∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N ℱ hℱN coeffs Y
                    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P :=
    MeasureTheory.lintegral_add_left' (h_diff_ofReal_aemeas t) _
  have h_split_1 : ∫⁻ ω, (ENNReal.ofReal
        (∑ i : Fin n,
          ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        + (ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W ℱ hℱW coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N ℱ hℱN coeffs Y
                      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))) ∂P
      = (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω
                - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
        + ∫⁻ ω, (ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W ℱ hℱW coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N ℱ hℱN coeffs Y
                      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P :=
    MeasureTheory.lintegral_add_left' (h_drift_ofReal_aemeas t) _
  -- Combine the splits with the pulled-out 3 factor.
  have h_triangle_split :
      ∫⁻ ω, 3 * (ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                  - picardStep_diffusion W ℱ hℱW coeffs Y
                      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N ℱ hℱN coeffs Y
                      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P
      = 3 * ((∫⁻ ω, ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_drift coeffs X x₀ t ω
                  - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
            + (∫⁻ ω, ENNReal.ofReal
                  (∑ i : Fin n,
                    ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                      - picardStep_diffusion W ℱ hℱW coeffs Y
                          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
            + ∫⁻ ω, ENNReal.ofReal
                (∑ i : Fin n,
                  ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                    - picardStep_jump N ℱ hℱN coeffs Y
                        h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P) := by
    rw [MeasureTheory.lintegral_const_mul' _ _ (by norm_num)]
    -- After pulling 3 out: goal is `3 * lintegral_of_sum = 3 * (l1 + l2 + l3)`.
    -- The lintegral_of_sum needs to be split using h_split_1 and h_split_2.
    congr 1
    rw [show (fun ω => ENNReal.ofReal (∑ i, ((picardStep_drift coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        + ENNReal.ofReal (∑ i, ((picardStep_diffusion W ℱ hℱW coeffs X
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
        + ENNReal.ofReal (∑ i,
            ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
            - picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))
      = (fun ω => ENNReal.ofReal (∑ i, ((picardStep_drift coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        + (ENNReal.ofReal (∑ i, ((picardStep_diffusion W ℱ hℱW coeffs X
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i,
              ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
              - picardStep_jump N ℱ hℱN coeffs Y
                  h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))) from by
      funext ω; rw [add_assoc]]
    rw [h_split_1, h_split_2, add_assoc]
  -- Now: combine the three lintegrals using drift/σ/γ bounds (each ≤ Bnt * Iω).
  have h_sum_bound :
      (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω
                - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
        + (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W ℱ hℱW coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
        + (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N ℱ hℱN coeffs Y
                    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P)
      ≤ Bnt * Iω + Bnt * Iω + Bnt * Iω :=
    add_le_add (add_le_add h_drift h_σ) h_γ
  -- Bnt ≤ ofReal(n L² T) since t ≤ T.
  have h_Bnt_T : Bnt ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2 * T) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have h_nL2_nn : 0 ≤ (n : ℝ) * L ^ 2 :=
      mul_nonneg (Nat.cast_nonneg n) (sq_nonneg L)
    exact mul_le_mul_of_nonneg_left ht_le h_nL2_nn
  -- 9 = 3 * 3 as ℝ≥0∞.
  -- Final chain: Φ ≤ ∫⁻ (3 * ...) = 3 * (...) ≤ 3 * (3 Bnt Iω)
  --   = 9 Bnt Iω ≤ 9 (n L² T) Iω.
  calc ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep W N ℱ hℱW hℱN coeffs X x₀
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep W N ℱ hℱW hℱN coeffs Y x₀
            h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
              h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ∫⁻ ω, 3 *
          (ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                  - picardStep_diffusion W ℱ hℱW coeffs Y
                      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N ℱ hℱN coeffs Y
                      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))
          ∂P := h_triangle'
    _ = 3 * ((∫⁻ ω, ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_drift coeffs X x₀ t ω
                  - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
            + (∫⁻ ω, ENNReal.ofReal
                  (∑ i : Fin n,
                    ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                      - picardStep_diffusion W ℱ hℱW coeffs Y
                          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
            + ∫⁻ ω, ENNReal.ofReal
                (∑ i : Fin n,
                  ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                    - picardStep_jump N ℱ hℱN coeffs Y
                        h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P) :=
        h_triangle_split
    _ ≤ 3 * (Bnt * Iω + Bnt * Iω + Bnt * Iω) :=
        mul_le_mul_of_nonneg_left h_sum_bound (by exact bot_le)
    _ = 9 * Bnt * Iω := by ring
    _ ≤ 9 * ENNReal.ofReal ((n : ℝ) * L ^ 2 * T) * Iω := by
        gcongr
    _ = ENNReal.ofReal (9 * ((n : ℝ) * L ^ 2 * T)) * Iω := by
        rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 from by rw [ENNReal.ofReal_ofNat]]
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9)]
    _ = ENNReal.ofReal (9 * (n : ℝ) * L ^ 2 * T) * Iω := by ring_nf

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Picard contraction rate threshold.**

The Picard contraction rate `9 n L² T / (2β)` is `< 1` iff `β > 9 n L² T / 2`.

This is the threshold condition for the Picard map to be a strict contraction
in the Bielecki β-norm. Pairing with `picardStep_bielecki_contraction` and
the Bielecki weight bound `bielecki_weighted_integral_bound`, the resulting
estimate

  `e^{-2βt} · ‖Φ X t - Φ Y t‖_{L²(P)}² ≤ (9 n L² T / (2β)) · ‖X - Y‖_{β,T}²`

is a strict contraction for `β > 9 n L² T / 2`. -/
lemma picardStep_bielecki_contraction_rate_lt_one
    (n : ℕ) {L : ℝ} (_hL_nn : 0 ≤ L)
    {β T : ℝ} (hT_pos : 0 < T)
    (h_β_threshold : 9 * (n : ℝ) * L ^ 2 * T < 2 * β) :
    9 * (n : ℝ) * L ^ 2 * T / (2 * β) < 1 := by
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by
    have h_LHS_nn : 0 ≤ 9 * (n : ℝ) * L ^ 2 * T :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
        (sq_nonneg L)) hT_pos.le
    linarith
  rw [div_lt_one h_two_beta_pos]
  exact h_β_threshold

end LevyStochCalc.Ito.Picard
