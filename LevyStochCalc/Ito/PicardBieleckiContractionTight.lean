/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.PicardBieleckiContraction

/-!
# The Picard contraction at the literature-tight rate

The refinement of the Bielecki-norm contraction estimate that takes the diffusion and jump bounds
in their tight form, without the redundant time factor, giving the constant `3 n L² (T + 2)` in
place of `9 n L² T` and hence the contraction rate `3 n L² (T + 2) / (2β)`; together with the
threshold `3 n L² (T + 2) < 2β` under which that rate is `< 1`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

set_option maxHeartbeats 4000000 in
-- Same contraction chain as `picardStep_bielecki_contraction`, with the tighter
-- constant tracked through every step; it exceeds the default budget.
/-- **Picard step Bielecki β-norm contraction — literature-tight rate.**

Refinement of `picardStep_bielecki_contraction` that produces the
literature-tight contraction rate `3 n L² (T + 2)` instead of
`9 n L² T`. The improvement comes from taking the σ-step and γ-step
bound hypotheses in their *tight* form (without the redundant `t`
factor that the original lemma uses to over-bound all three
components uniformly by the drift's `n L² t` constant).

For each `t ∈ [0, T]`, the lintegral L² mass of the Picard step
difference is bounded by

  `3 · n · L² · (T + 2) · ∫⁻ ω, ∫₀^t ‖X_s - Y_s‖² ds ∂P`,

where the three constants summed before the triangle factor 3 are:

* drift: `n · L² · t` per dimension — Cauchy-Schwarz on the time
  integral × per-row μ-Lipschitz × sum over `n` rows,
* σ: `n · L²` per dimension — Itô isometry (no `t` factor) ×
  per-row σ-Lipschitz × sum over `n` rows,
* γ: `n · L²` per dimension — Itô-Lévy isometry (no `t` factor) ×
  per-row γ-Lipschitz × sum over `n` rows.

Total: `(n L² t + 2 n L²) ≤ n L² (T + 2)`, then × 3 from the
triangle inequality `(a + b + c)² ≤ 3 (a² + b² + c²)`.

After applying the Bielecki weight `e^{-2βt}` and using
`bielecki_weighted_integral_bound`, the per-`t` weighted bound is
`3 n L² (T + 2) / (2β) · ‖X - Y‖²_β,T`. Together with
`picardStep_bielecki_contraction_tight_rate_lt_one`, the Picard map
is a strict contraction in the Bielecki β-norm for
`β > 3 n L² (T + 2) / 2`.

For `T ≥ 1` and `n ≥ 1`, this threshold is strictly tighter than the
original `β > 9 n L² T / 2` (since `T + 2 ≤ 3 T` when `T ≥ 1`).
Asymptotically (large `n T`) it matches the literature's
`3 n L² T / (2β)` rate. -/
theorem picardStep_bielecki_contraction_tight
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
    -- **Tight σ-step lintegral bound** (no `t` factor — the
    -- redundant `n · t` padding from the loose version has been
    -- removed; only the natural `n L²` constant remains):
    (h_σ_step_bound_tight : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
          - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2) *
          ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P)
    -- **Tight γ-step lintegral bound** (no `t` factor — analogous
    -- removal of the `n · t` padding):
    (h_γ_step_bound_tight : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2) *
          ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P)
    -- AEMeasurability of the three component sum-of-squares ofReal functions,
    -- needed to split the triple-term lintegral on the RHS of
    -- `picardStep_diff_lintegral_sum_sq_le`.
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
    ≤ ENNReal.ofReal (3 * (n : ℝ) * L ^ 2 * (T + 2)) *
        ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t,
          ‖X s ω - Y s ω‖ ^ 2) ∂P := by
  obtain ⟨ht_nn, ht_le⟩ := ht
  -- Drift bound at t (proven; from `Picard.lean`).
  have h_drift := picardStep_drift_diff_lintegral_sq_bound (E := E) P coeffs hL_nn h_μ_lip
    X Y x₀ t ht_nn (h_drift_bound_ae t ⟨ht_nn, ht_le⟩) (h_drift_inner_nn t ⟨ht_nn, ht_le⟩)
  -- σ + γ bounds at t (tight form, hypothesized).
  have h_σ := h_σ_step_bound_tight t ⟨ht_nn, ht_le⟩
  have h_γ := h_γ_step_bound_tight t ⟨ht_nn, ht_le⟩
  -- Triangle inequality bound (lintegral form; single-integral RHS).
  have h_triangle' := picardStep_diff_lintegral_sum_sq_le W N ℱ hℱW hℱN coeffs X Y x₀
    h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
    h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t
  -- Abbreviations.
  set Iω : ℝ≥0∞ :=
    ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t,
      ‖X s ω - Y s ω‖ ^ 2) ∂P with hIω_def
  -- Bnt_drift = n L² t  (drift), Bnt_σγ = n L²  (σ and γ tight).
  set Bnt_drift : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) * L ^ 2 * t) with hBnt_drift_def
  set Bnt_σγ : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) * L ^ 2) with hBnt_σγ_def
  -- Step 1: Split the triple-sum lintegral on the RHS into three separate lintegrals.
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
  -- Combine the three lintegrals with their NATURAL (distinct) Bnt constants.
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
      ≤ Bnt_drift * Iω + Bnt_σγ * Iω + Bnt_σγ * Iω :=
    add_le_add (add_le_add h_drift h_σ) h_γ
  -- Algebraic upper bound: Bnt_drift + 2·Bnt_σγ ≤ ENNReal.ofReal (n L² (T + 2)).
  -- Pointwise: n L² t + 2 n L² = n L² (t + 2) ≤ n L² (T + 2)  since t ≤ T.
  have h_nL2_nn : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 :=
    mul_nonneg (Nat.cast_nonneg n) (sq_nonneg L)
  have h_nL2t_nn : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 * t :=
    mul_nonneg h_nL2_nn ht_nn
  have h_T2_nn : (0 : ℝ) ≤ T + 2 := by linarith [(le_trans ht_nn ht_le)]
  have h_nL2_T2_nn : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 * (T + 2) :=
    mul_nonneg h_nL2_nn h_T2_nn
  -- Bnt_drift + 2·Bnt_σγ = ENNReal.ofReal (n L² t + 2 n L²) = ENNReal.ofReal (n L² (t + 2))
  --                     ≤ ENNReal.ofReal (n L² (T + 2)).
  have h_Bnt_combine : Bnt_drift + Bnt_σγ + Bnt_σγ
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2 * (T + 2)) := by
    -- Step 1: Convert sum of ofReal to ofReal of sum (using nonnegativity).
    rw [show Bnt_drift + Bnt_σγ + Bnt_σγ
          = ENNReal.ofReal ((n : ℝ) * L ^ 2 * t + (n : ℝ) * L ^ 2 + (n : ℝ) * L ^ 2) from by
      rw [hBnt_drift_def, hBnt_σγ_def]
      rw [← ENNReal.ofReal_add h_nL2t_nn h_nL2_nn,
          ← ENNReal.ofReal_add (add_nonneg h_nL2t_nn h_nL2_nn) h_nL2_nn]]
    -- Step 2: Bound n L² t + n L² + n L² = n L² (t + 2) ≤ n L² (T + 2)  via t ≤ T.
    refine ENNReal.ofReal_le_ofReal ?_
    have h_eq : (n : ℝ) * L ^ 2 * t + (n : ℝ) * L ^ 2 + (n : ℝ) * L ^ 2
                = (n : ℝ) * L ^ 2 * (t + 2) := by ring
    rw [h_eq]
    have h_mono : (n : ℝ) * L ^ 2 * (t + 2) ≤ (n : ℝ) * L ^ 2 * (T + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) h_nL2_nn
    exact h_mono
  -- Final chain.
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
    _ ≤ 3 * (Bnt_drift * Iω + Bnt_σγ * Iω + Bnt_σγ * Iω) :=
        mul_le_mul_of_nonneg_left h_sum_bound (by exact bot_le)
    _ = 3 * (Bnt_drift + Bnt_σγ + Bnt_σγ) * Iω := by ring
    _ ≤ 3 * ENNReal.ofReal ((n : ℝ) * L ^ 2 * (T + 2)) * Iω := by
        gcongr
    _ = ENNReal.ofReal (3 * ((n : ℝ) * L ^ 2 * (T + 2))) * Iω := by
        rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by rw [ENNReal.ofReal_ofNat]]
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
    _ = ENNReal.ofReal (3 * (n : ℝ) * L ^ 2 * (T + 2)) * Iω := by ring_nf

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Tight Picard contraction rate threshold.**

The tight Picard contraction rate `3 n L² (T + 2) / (2β)` is `< 1`
iff `β > 3 n L² (T + 2) / 2`.

This is the threshold condition for the Picard map to be a strict
contraction in the Bielecki β-norm under the tight rate. Pairing with
`picardStep_bielecki_contraction_tight` and the Bielecki weight bound
`bielecki_weighted_integral_bound`, the resulting estimate

  `e^{-2βt} · ‖Φ X t - Φ Y t‖_{L²(P)}²`
  `  ≤ (3 n L² (T + 2) / (2β)) · ‖X - Y‖_{β,T}²`

is a strict contraction for `β > 3 n L² (T + 2) / 2`.

For `T ≥ 1` and `n ≥ 1`, this threshold is strictly less than the
original loose threshold `9 n L² T / 2` (since `T + 2 ≤ 3 T` when
`T ≥ 1`), so the Picard fixed point exists at a smaller `β`. -/
lemma picardStep_bielecki_contraction_tight_rate_lt_one
    (n : ℕ) {L : ℝ} (_hL_nn : 0 ≤ L)
    {β T : ℝ} (hT_pos : 0 < T)
    (h_β_threshold : 3 * (n : ℝ) * L ^ 2 * (T + 2) < 2 * β) :
    3 * (n : ℝ) * L ^ 2 * (T + 2) / (2 * β) < 1 := by
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by
    have h_T2_nn : 0 ≤ T + 2 := by linarith
    have h_LHS_nn : 0 ≤ 3 * (n : ℝ) * L ^ 2 * (T + 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
        (sq_nonneg L)) h_T2_nn
    linarith
  rw [div_lt_one h_two_beta_pos]
  exact h_β_threshold

end LevyStochCalc.Ito.Picard
