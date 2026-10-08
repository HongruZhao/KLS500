/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.PicardStochasticLipschitz

/-!
# The Picard map as a self-map of the process space, and its difference bounds

The output of a Picard step as an element of `SBoundedProcess`, the induced self-map
`picardStepOnS2` of the process space and the identification of its path map; and the
sub-additivity bounds `(a + b + c)² ≤ 3 (a² + b² + c²)` in real, vector and `ω`-integrated form,
which split the difference of two Picard steps into its drift, diffusion and jump contributions.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Construct an `SBoundedProcess` from the Picard step output and
the three caller-supplied field hypotheses.**

This is the `fromCandidate`-style constructor described in the module
docstring: given the data + hypotheses that make `picardStep` well-typed
(σ-side measurability/progressive-measurability/L²-boundedness +
γ-side analogue), PLUS three explicit hypothesis bundles for the
output's joint measurability, càdlàg paths, and finite Bielecki-norm,
package the result into an `SBoundedProcess`.

The σ/γ hypothesis bundles are the same ones that `picardStep` takes;
they are reproduced here as named arguments so the constructor can be
invoked uniformly across Picard iterates (each iterate produces the
same shape of hypotheses for the next iterate, with σ/γ replaced by
σ/γ along the new candidate).

The three output-field hypotheses
(`h_out_meas`, `h_out_adapted`, `h_out_cadlag`, `h_out_sup_L2`) encode the
"missing-Mathlib-infrastructure" content that a BDG-based analytic
argument would otherwise discharge — see the module docstring. -/
noncomputable def SBoundedProcess.ofPicardStep
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    -- σ-side hypotheses for the Brownian integral
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    -- γ-side hypotheses for the compensated-Poisson integral
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ)
    -- Three explicit output-field hypotheses (see module docstring).
    (h_out_meas : Measurable (Function.uncurry
      (fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω)))
    (h_out_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto
        (fun s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω)
        (nhdsWithin t (Set.Ioi t))
        (nhds (picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
            Filter.Tendsto
              (fun s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
                h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i)
              (nhdsWithin t (Set.Iio t)) (nhds L))
    (h_out_adapted : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ
      (fun ω s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i))
    (h_out_sup_L2 : bieleckiNorm (P := P) 0 T
      (fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω) < ⊤) :
    SBoundedProcess (n := n) P ℱ T where
  X := fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
    h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω
  measurable_path := h_out_meas
  adapted := h_out_adapted
  cadlag_paths := h_out_cadlag
  sup_L2 := h_out_sup_L2

/-- **The Picard self-map on `SBoundedProcess`.**

Given:

* the Brownian motion `W`, the Poisson random measure `N`, the coefficient
  bundle `coeffs`, and the initial condition `x₀`,
* an `SBoundedProcess` candidate `X`,
* σ/γ-side measurability + L²-boundedness bundles for `coeffs` along
  `X.X` (these depend on `X` and must be supplied at call time — they
  are produced uniformly across all Picard iterates by combining the
  shared coeffs measurability with the SBoundedProcess's joint
  measurability via `sigma_along_X_measurable` and
  `gamma_along_X_measurable`),
* the **four output-field hypothesis bundles** for the lifted iterate.

…produces a new `SBoundedProcess` whose underlying path map is
exactly `picardStep` applied to `X.X`.

This is the `Φ : SBoundedProcess → SBoundedProcess` map that the Banach
fixed-point theorem consumes in
`picardFixedPoint_jumpDiffusion_exists_unique`. The contraction
estimate (proved in `Picard.lean`) operates on the
underlying path map and lifts trivially through `picardStepOnS2`. -/
noncomputable def picardStepOnS2
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ) (T : ℝ)
    (X : SBoundedProcess (n := n) P ℱ T)
    -- σ-side hypotheses along X.X
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X.X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X.X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    -- γ-side hypotheses along X.X
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X.X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    -- Four output-field hypothesis bundles (see module docstring).
    (h_out_meas : Measurable (Function.uncurry
      (fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω)))
    (h_out_adapted : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ
      (fun ω s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i))
    (h_out_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto
        (fun s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω)
        (nhdsWithin t (Set.Ioi t))
        (nhds (picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
            Filter.Tendsto
              (fun s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
                h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i)
              (nhdsWithin t (Set.Iio t)) (nhds L))
    (h_out_sup_L2 : bieleckiNorm (P := P) 0 T
      (fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω) < ⊤) :
    SBoundedProcess (n := n) P ℱ T :=
  SBoundedProcess.ofPicardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
    h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq T
    h_out_meas h_out_cadlag h_out_adapted h_out_sup_L2

-- `picardStep`, its two integral components and `bieleckiNorm` unfold to `Finset` sums
-- over `Fin d` / `Fin n` and to the `L²`-limit integrals; the statement below repeats
-- those terms verbatim on both sides, so unfolding them during unification only costs
-- time (296760 `Fin.foldr` reductions before this seal).
attribute [local irreducible] picardStep picardStep_diffusion picardStep_jump bieleckiNorm
attribute [local irreducible]
  LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
attribute [local irreducible] LevyStochCalc.Brownian.Ito.stochasticIntegral
attribute [local irreducible] LevyStochCalc.Poisson.Compensated.stochasticIntegral

set_option maxHeartbeats 400000 in
-- The three output hypotheses restate the whole Picard term, so checking them against
-- `picardStepOnS2`'s binders compares the filtration argument of every progressive-
-- measurability side condition; that alone exceeds the default budget.
-- maxHeartbeats: the `rfl` below unifies the full argument bundle of `ofPicardStep`.
set_option maxHeartbeats 1600000 in
/-- The path map of `picardStepOnS2 W N ℱ … X` is `picardStep` applied to `X.X`, so a
bound on `picardStep` is a bound on the lifted iterate's path map. -/
@[simp]
lemma picardStepOnS2_X
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ) (T : ℝ)
    (X : SBoundedProcess (n := n) P ℱ T)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X.X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X.X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X.X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_out_meas : Measurable (Function.uncurry
      (fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω)))
    (h_out_adapted : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ
      (fun ω s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i))
    (h_out_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto
        (fun s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω)
        (nhdsWithin t (Set.Ioi t))
        (nhds (picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
            Filter.Tendsto
              (fun s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
                h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i)
              (nhdsWithin t (Set.Iio t)) (nhds L))
    (h_out_sup_L2 : bieleckiNorm (P := P) 0 T
      (fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω) < ⊤) :
    (picardStepOnS2 (E := E) W N ℱ hℱW hℱN coeffs x₀ T X
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq
        h_out_meas h_out_adapted h_out_cadlag h_out_sup_L2).X
      = fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω := by
  rfl

end LevyStochCalc.Ito.Picard

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Sub-additivity of squared sums on three terms.**

  `(a + b + c)² ≤ 3 · (a² + b² + c²)`.

This is the standard Cauchy-Schwarz / AM-QM bound on three terms and is the
load-bearing combinatorial step that turns the three component L² bounds
(drift, σ, γ) into a single bound on the full Picard step. -/
lemma sq_add_three_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Sub-additivity of squared norms on three vector terms.**

For `u v w : Fin n → ℝ`,

  `∑ i, (u i + v i + w i)² ≤ 3 · (∑ i, (u i)² + ∑ i, (v i)² + ∑ i, (w i)²)`.

This is `sq_add_three_le` applied componentwise and summed over `Fin n`. -/
lemma sum_sq_add_three_le {n : ℕ} (u v w : Fin n → ℝ) :
    ∑ i : Fin n, (u i + v i + w i) ^ 2
      ≤ 3 * (∑ i : Fin n, (u i) ^ 2 + ∑ i : Fin n, (v i) ^ 2
              + ∑ i : Fin n, (w i) ^ 2) := by
  have h_each : ∀ i : Fin n, (u i + v i + w i) ^ 2
      ≤ 3 * ((u i) ^ 2 + (v i) ^ 2 + (w i) ^ 2) := fun i =>
    sq_add_three_le (u i) (v i) (w i)
  calc (∑ i : Fin n, (u i + v i + w i) ^ 2)
      ≤ ∑ i : Fin n, 3 * ((u i) ^ 2 + (v i) ^ 2 + (w i) ^ 2) :=
        Finset.sum_le_sum (fun i _ => h_each i)
    _ = 3 * ∑ i : Fin n, ((u i) ^ 2 + (v i) ^ 2 + (w i) ^ 2) := by
        rw [← Finset.mul_sum]
    _ = 3 * (∑ i : Fin n, (u i) ^ 2 + ∑ i : Fin n, (v i) ^ 2
              + ∑ i : Fin n, (w i) ^ 2) := by
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

set_option maxHeartbeats 4000000 in
-- The three Picard components are compared under one `Finset.sum` over `Fin n`;
-- `nlinarith` on the resulting sum-of-squares exceeds the default budget.
/-- **Picard step pointwise sum-of-squares triangle bound.**

For `Φ X = drift X + diff X + jump X` and any two `X Y`, the squared
Euclidean norm of `(Φ X - Φ Y) t ω` is bounded componentwise by three
times the sum of the three component squared norms:

  `∑ i, ((Φ X t ω - Φ Y t ω) i)²
    ≤ 3 · (∑ i, ((drift_diff)i)² + ∑ i, ((diff_diff)i)² + ∑ i, ((jump_diff)i)²)`.

This is the algebraic identity `picardStep = drift + diff + jump` followed
by `sum_sq_add_three_le`. -/
lemma picardStep_diff_sum_sq_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
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
    (t : ℝ) (ω : Ω) :
    ∑ i : Fin n, ((picardStep W N ℱ hℱW hℱN coeffs X x₀
        h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
      - picardStep W N ℱ hℱW hℱN coeffs Y x₀
        h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2
    ≤ 3 * (∑ i : Fin n, ((picardStep_drift coeffs X x₀ t ω
                          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
          + ∑ i : Fin n, ((picardStep_diffusion W ℱ hℱW coeffs X
                            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                          - picardStep_diffusion W ℱ hℱW coeffs Y
                            h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2
          + ∑ i : Fin n, ((picardStep_jump N ℱ hℱN coeffs X
                            h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                          - picardStep_jump N ℱ hℱN coeffs Y
                            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) := by
  -- Unfold picardStep = drift + diffusion + jump and apply sum_sq_add_three_le.
  unfold picardStep
  have h_sq_eq : ∀ i : Fin n,
      (((picardStep_drift coeffs X x₀ t ω
            + picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            + picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω)
          - (picardStep_drift coeffs Y x₀ t ω
            + picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω
            + picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω)) i) ^ 2
      = ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i
          + (picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
              - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i
          + (picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
              - picardStep_jump N ℱ hℱN coeffs Y
                  h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2 := by
    intro i
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [Finset.sum_congr rfl (fun i _ => h_sq_eq i)]
  exact sum_sq_add_three_le _ _ _

set_option maxHeartbeats 4000000 in
-- Lifting the pointwise bound under `∫⁻` re-elaborates the three Picard components
-- inside the integrand; the monotonicity chain exceeds the default budget.
/-- **Picard step lintegral sum-of-squares triangle bound (single-integral form).**

Lift `picardStep_diff_sum_sq_le` to the lintegral over `ω`. The RHS is
stated as a SINGLE lintegral of the (pointwise) three-term sum, not as
three separate lintegrals, in order to avoid requiring AEMeasurable
hypotheses on the individual component differences (which would in turn
require joint measurability hypotheses on `X, Y` that are not yet in scope
at this level of the Picard scaffolding).

To downstream callers: once you have AEMeasurable hypotheses for the
individual `ENNReal.ofReal (∑ i, ((picardStep_drift ...) i)^2)` and the
analogous σ + γ functions, you can split the RHS lintegral via
`MeasureTheory.lintegral_add_left'` to recover the three-separate-lintegrals
form expected by the drift/σ/γ bound lemmas. -/
lemma picardStep_diff_lintegral_sum_sq_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
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
    (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep W N ℱ hℱW hℱN coeffs X x₀
          h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        - picardStep W N ℱ hℱW hℱN coeffs Y x₀
          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
    ≤ ∫⁻ ω, 3 * (ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω
                - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W ℱ hℱW coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N ℱ hℱN coeffs Y
                    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P := by
  -- Pointwise (in ω) ENNReal-lifted form of `picardStep_diff_sum_sq_le`.
  have h_ptw : ∀ ω : Ω,
      ENNReal.ofReal (∑ i : Fin n,
        ((picardStep W N ℱ hℱW hℱN coeffs X x₀
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep W N ℱ hℱW hℱN coeffs Y x₀
            h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
              h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)
      ≤ 3 *
          (ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                  - picardStep_diffusion W ℱ hℱW coeffs Y
                      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N ℱ hℱN coeffs Y
                      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) := by
    intro ω
    have h_real := picardStep_diff_sum_sq_le W N ℱ hℱW hℱN coeffs X Y x₀
      h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω
    have h_drift_nn : 0 ≤ ∑ i : Fin n,
        ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h_diff_nn : 0 ≤ ∑ i : Fin n,
        ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
          - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h_jump_nn : 0 ≤ ∑ i : Fin n,
        ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    -- Convert h_real : LHS ≤ 3 * (a + b + c) to ENNReal.
    have h_RHS_eq : (3 : ℝ≥0∞) *
        (ENNReal.ofReal (∑ i : Fin n,
            ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W ℱ hℱW coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))
        = ENNReal.ofReal (3 * (∑ i : Fin n,
            ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
          + ∑ i : Fin n,
            ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
              - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2
          + ∑ i : Fin n,
            ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
              - picardStep_jump N ℱ hℱN coeffs Y
                  h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) := by
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by rw [ENNReal.ofReal_ofNat]]
      rw [← ENNReal.ofReal_add h_drift_nn h_diff_nn]
      rw [← ENNReal.ofReal_add (by positivity) h_jump_nn]
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
    rw [h_RHS_eq]
    exact ENNReal.ofReal_le_ofReal h_real
  exact MeasureTheory.lintegral_mono h_ptw

end LevyStochCalc.Ito.Picard
