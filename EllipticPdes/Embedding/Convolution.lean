/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Young's `Lᵖ` inequality for a probability kernel

This file collects the reusable convolution machinery feeding the weak-gradient Morrey
embedding. The headline result `eLpNorm_convolution_le` is a specialised Young inequality:
convolving an `Lᵖ` function against a non-negative kernel of unit mass does not increase its
`Lᵖ` seminorm. The classical proof uses the (currently absent) Minkowski integral inequality;
we instead derive the pointwise bound directly from Hölder's inequality in `ℝ≥0∞` and close
with Tonelli, so no Minkowski inequality is required.

The mollifier kernel `φ.normed volume` is the intended instance (non-negative by
`ContDiffBump.nonneg_normed`, unit mass by `ContDiffBump.integral_normed`), and the restricted
corollary `eLpNorm_convolution_restrict_le` is the form consumed downstream.

The second result `tendsto_eLpNorm_convolution_sub` records the `Lᵖ` convergence of the
mollifications `h ⋆ ρ_ε` to `h` as the bump radii shrink. It is proved by a density `3ε`
argument: approximate `h` in `Lᵖ` by a smooth compactly supported `w`
(`MeasureTheory.MemLp.exist_eLpNorm_sub_le`), control the tail `(h - w) ⋆ ρ_ε` by the Young
bound above, and drive the middle term `w ⋆ ρ_ε - w` to zero using the uniform convergence
supplied by `ContDiffBump.dist_normed_convolution_le` on the fixed compact support. No
`Lᵖ`-continuity of translation is required, and the argument is valid along an arbitrary filter.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution Topology Pointwise

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-- Convolution against the scalar multiplication of `ℝ` with respect to Lebesgue measure. -/
local notation:67 f:68 " ⋆ₛ " g:68 =>
  MeasureTheory.convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- **Pointwise Young bound.** For `1 ≤ p` and a kernel `ρ` of unit `ℝ≥0∞`-mass,
`‖(h ⋆ ρ)(x)‖ₑ ^ p ≤ ∫⁻ t, ‖h t‖ₑ ^ p ‖ρ (x - t)‖ₑ`. -/
private theorem enorm_convolution_rpow_le {p : ℝ} (hp : 1 ≤ p)
    {ρ h : EuclideanSpace ℝ (Fin d) → ℝ} (hρen : AEMeasurable (fun z => ‖ρ z‖ₑ) volume)
    (hhen : AEMeasurable (fun z => ‖h z‖ₑ) volume) (hmass : ∫⁻ z, ‖ρ z‖ₑ ∂volume = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖(h ⋆ₛ ρ) x‖ₑ ^ p ≤ ∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hρxen : AEMeasurable (fun t => ‖ρ (x - t)‖ₑ) volume :=
    hρen.comp_quasiMeasurePreserving
      (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving
  have hwmass : ∫⁻ t, ‖ρ (x - t)‖ₑ ∂volume = 1 :=
    (lintegral_sub_left_eq_self (fun z => ‖ρ z‖ₑ) x).trans hmass
  have hbound : ‖(h ⋆ₛ ρ) x‖ₑ ≤ ∫⁻ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ∂volume := by
    rw [convolution_def]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul, enorm_mul]
  refine le_trans (ENNReal.rpow_le_rpow hbound hp0.le) ?_
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · rw [← hp1, ENNReal.rpow_one]
    exact le_of_eq (lintegral_congr fun t => by rw [ENNReal.rpow_one])
  · have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1
    set q := Real.conjExponent p with hq_def
    have hq_pos : 0 < q := hpq.symm.pos
    have hsum : 1 / p + 1 / q = 1 := by simpa using hpq.one_div_add_one_div
    have e1 : ∀ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ^ (1 / p) * ‖ρ (x - t)‖ₑ ^ (1 / q)
        = ‖h t‖ₑ * ‖ρ (x - t)‖ₑ := fun t => by
      rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hpq.one_div_nonneg
        hpq.symm.one_div_nonneg, hsum, ENNReal.rpow_one]
    have e2 : ∀ t, (‖h t‖ₑ * ‖ρ (x - t)‖ₑ ^ (1 / p)) ^ p
        = ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ := fun t => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div,
        inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
    have e3 : ∀ t, (‖ρ (x - t)‖ₑ ^ (1 / q)) ^ q = ‖ρ (x - t)‖ₑ := fun t => by
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq_pos.ne', ENNReal.rpow_one]
    have hol : ∫⁻ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ∂volume
        ≤ (∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume) ^ (1 / p) := by
      have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
        (hhen.mul (hρxen.pow_const (1 / p))) (hρxen.pow_const (1 / q))
      simp only [Pi.mul_apply] at hH
      rwa [lintegral_congr e1, lintegral_congr e2, lintegral_congr e3, hwmass, ENNReal.one_rpow,
        mul_one] at hH
    calc (∫⁻ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ∂volume) ^ p
        ≤ ((∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume) ^ (1 / p)) ^ p :=
          ENNReal.rpow_le_rpow hol hp0.le
      _ = ∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]

/-- **Young's `Lᵖ` inequality for a probability kernel.** For `1 ≤ p`, a non-negative kernel
`ρ` with unit mass `∫ ρ = 1`, and `h ∈ Lᵖ`, the convolution against `ρ` does not increase the
`Lᵖ` seminorm: `‖h ⋆ ρ‖_{Lᵖ} ≤ ‖h‖_{Lᵖ}`. Proved by the pointwise Hölder bound
`|(h ⋆ ρ)(x)|^p ≤ ∫ |h(t)|^p ρ(x - t)` together with Tonelli and unit mass; no Minkowski
integral inequality is required. -/
theorem eLpNorm_convolution_le
    {p : ℝ} (hp : 1 ≤ p) {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ0 : 0 ≤ ρ) (hρm : AEStronglyMeasurable ρ volume) (hρ1 : ∫ y, ρ y ∂volume = 1)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : MemLp h (ENNReal.ofReal p) volume) :
    eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) (ENNReal.ofReal p) volume
      ≤ eLpNorm h (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hP0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hPtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hhen : AEMeasurable (fun z => ‖h z‖ₑ) volume := hh.aestronglyMeasurable.enorm
  have hρen : AEMeasurable (fun z => ‖ρ z‖ₑ) volume := hρm.enorm
  -- the kernel is integrable, with unit `ℝ≥0∞`-mass
  have hρint : Integrable ρ volume := by
    by_contra hcon
    rw [integral_undef hcon] at hρ1
    exact one_ne_zero hρ1.symm
  have hmass : ∫⁻ z, ‖ρ z‖ₑ ∂volume = 1 := by
    rw [lintegral_congr fun z => Real.enorm_of_nonneg (hρ0 z),
      ← ofReal_integral_eq_lintegral_ofReal hρint (ae_of_all _ fun z => hρ0 z), hρ1,
      ENNReal.ofReal_one]
  -- measurability of the uncurried Tonelli integrand
  have hswapmeas : AEMeasurable
      (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖h q.2‖ₑ ^ p * ‖ρ (q.1 - q.2)‖ₑ) (volume.prod volume) :=
    ((hhen.pow_const p).comp_snd).mul
      (hρen.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  -- reduce the seminorm inequality to the `lintegral` inequality
  have hconvm : AEStronglyMeasurable (h ⋆ₛ ρ) volume :=
    (AEStronglyMeasurable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ)
      hh.aestronglyMeasurable hρm).integral_prod_right'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop hconvm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop hh.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  refine ENNReal.rpow_le_rpow ?_ (one_div_nonneg.mpr hp0.le)
  calc ∫⁻ x, ‖(h ⋆ₛ ρ) x‖ₑ ^ p ∂volume
      ≤ ∫⁻ x, ∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume ∂volume :=
        lintegral_mono (enorm_convolution_rpow_le hp hρen hhen hmass)
    _ = ∫⁻ t, ∫⁻ x, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume ∂volume :=
        lintegral_lintegral_swap hswapmeas
    _ = ∫⁻ t, ‖h t‖ₑ ^ p * ∫⁻ x, ‖ρ (x - t)‖ₑ ∂volume ∂volume := by
        refine lintegral_congr fun t => ?_
        exact lintegral_const_mul'' (‖h t‖ₑ ^ p) (hρen.comp_quasiMeasurePreserving
          (measurePreserving_sub_right volume t).quasiMeasurePreserving)
    _ = ∫⁻ t, ‖h t‖ₑ ^ p * 1 ∂volume := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_sub_right_eq_self (fun z => ‖ρ z‖ₑ) t, hmass]
    _ = ∫⁻ x, ‖h x‖ₑ ^ p ∂volume := by simp

/-- Young bound restricted to a set `s` on the left, upper-bounded by the full `Lᵖ` norm. -/
theorem eLpNorm_convolution_restrict_le {p : ℝ} (hp : 1 ≤ p)
    {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ0 : 0 ≤ ρ) (hρm : AEStronglyMeasurable ρ volume)
    (hρ1 : ∫ y, ρ y ∂volume = 1) {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh : MemLp h (ENNReal.ofReal p) volume) (s : Set (EuclideanSpace ℝ (Fin d))) :
    eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) (ENNReal.ofReal p)
        (volume.restrict s)
      ≤ eLpNorm h (ENNReal.ofReal p) volume :=
  le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self)
    (eLpNorm_convolution_le hp hρ0 hρm hρ1 hh)

/-- Convolution against scalar multiplication is commutative. -/
theorem convolution_lsmul_comm {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] [MeasurableNeg G] {μ : Measure G} [μ.IsAddLeftInvariant]
    [μ.IsNegInvariant] (f g : G → ℝ) :
    f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g = g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f := by
  rw [← convolution_flip]
  congr 1
  exact ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => mul_comm b a

/-- A finite quantity times a small enough number is below any positive finite bound. -/
private theorem exists_pos_mul_ofReal_le {A η : ℝ≥0∞} (hA : A ≠ ∞) (hη : 0 < η)
    (hηtop : η ≠ ∞) : ∃ ε : ℝ, 0 < ε ∧ A * ENNReal.ofReal ε ≤ η := by
  have hA1top : A + 1 ≠ ∞ := by simp [hA]
  have hA1pos : A + 1 ≠ 0 := by positivity
  refine ⟨(η / (A + 1)).toReal, ENNReal.toReal_pos (ENNReal.div_pos hη.ne' hA1top).ne'
    (ENNReal.div_ne_top hηtop hA1pos), ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.div_ne_top hηtop hA1pos)]
  calc A * (η / (A + 1)) ≤ (A + 1) * (η / (A + 1)) := by gcongr; exact le_self_add
    _ ≤ η := ENNReal.mul_div_le

/-- **Middle `3ε` term.** For a continuous compactly supported `w`, the mollifications
`w ⋆ ρ_ε` converge to `w` in `Lᵖ` as the outer bump radii shrink. The convolutions are
uniformly close to `w` on the fixed compact `closedBall 0 1 + tsupport w` (uniform continuity
of `w` plus `ContDiffBump.dist_normed_convolution_le`), and the `Lᵖ` seminorm of a uniformly
small function on a fixed finite-measure set is small. This needs only `rOut → 0`, not the
inner/outer ratio bound. -/
private theorem tendsto_eLpNorm_bump_convolution_sub {p : ℝ} (hp : 1 ≤ p)
    {w : EuclideanSpace ℝ (Fin d) → ℝ} (hwc : Continuous w) (hwcs : HasCompactSupport w)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin d))}
    (hφ : Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Filter.Tendsto
      (fun i => eLpNorm
          (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) - w)
          (ENNReal.ofReal p) volume) l (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hunif : UniformContinuous w := hwcs.uniformContinuous_of_continuous hwc
  -- the fixed compact set that contains every `w ⋆ ρ_i - w`
  set S1 := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 + tsupport w with hS1def
  have hS1cpt : IsCompact S1 := (isCompact_closedBall _ _).add hwcs
  have hS1fin : volume S1 ≠ ∞ := hS1cpt.measure_lt_top.ne
  have hAtop : volume S1 ^ p⁻¹ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hS1fin
  have htsuppS1 : tsupport w ⊆ S1 := by
    intro y hy
    rw [hS1def]
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 :=
      Metric.mem_closedBall_self zero_le_one
    simpa using Set.add_mem_add h0 hy
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ∞ with rfl | hηtop
  · exact Filter.Eventually.of_forall fun _ => le_top
  obtain ⟨ε, hε0, hAε⟩ := exists_pos_mul_ofReal_le hAtop hη hηtop
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp hunif ε hε0
  filter_upwards [Metric.tendsto_nhds.mp hφ δ hδ0, Metric.tendsto_nhds.mp hφ 1 one_pos]
    with i hiδ hi1
  have hrδ : (φ i).rOut < δ := by
    rwa [Real.dist_0_eq_abs, abs_of_pos (φ i).rOut_pos] at hiδ
  have hr1 : (φ i).rOut < 1 := by
    rwa [Real.dist_0_eq_abs, abs_of_pos (φ i).rOut_pos] at hi1
  -- swap the convolution so the bump is on the left
  have hcomm : w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume)
      = ((φ i).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w :=
    convolution_lsmul_comm _ _
  -- uniform closeness on the whole space
  have hpt : ∀ x₀, dist ((((φ i).normed volume)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x₀) (w x₀) ≤ ε := by
    intro x₀
    refine (φ i).dist_normed_convolution_le hwc.aestronglyMeasurable ?_
    intro x hx
    rw [mem_ball] at hx
    exact (hδ (lt_trans hx hrδ)).le
  -- support of the difference lies in the fixed compact `S1`
  have hsuppconv : Function.support (((φ i).normed volume)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) ⊆ S1 := by
    refine (support_convolution_subset _).trans ?_
    rw [hS1def]
    refine Set.add_subset_add ?_ (subset_tsupport w)
    rw [(φ i).support_normed_eq]
    exact Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hr1.le)
  have hsupp : Function.support ((((φ i).normed volume)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) - w) ⊆ S1 := by
    intro x hx
    by_contra hxS1
    refine Function.mem_support.mp hx ?_
    have hwx : w x = 0 := image_eq_zero_of_notMem_tsupport fun hxt => hxS1 (htsuppS1 hxt)
    have hcx : (((φ i).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x = 0 :=
      Function.notMem_support.mp fun hxs => hxS1 (hsuppconv hxs)
    rw [Pi.sub_apply, hwx, hcx, sub_zero]
  have hdm : AEStronglyMeasurable ((((φ i).normed volume)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) - w) volume := by
    rw [← hcomm]
    exact ((HasCompactSupport.continuous_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (φ i).hasCompactSupport_normed hwc.locallyIntegrable
      ((φ i).contDiff_normed (n := 1)).continuous).sub hwc).aestronglyMeasurable
  -- assemble the `Lᵖ` bound
  rw [hcomm]
  calc eLpNorm ((((φ i).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) - w)
        (ENNReal.ofReal p) volume
      = eLpNorm ((((φ i).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) - w)
          (ENNReal.ofReal p) (volume.restrict S1) :=
        (eLpNorm_restrict_eq_of_support_subset hdm hsupp).symm
    _ ≤ (volume.restrict S1) Set.univ ^ ((ENNReal.ofReal p).toReal⁻¹) * ENNReal.ofReal ε :=
        eLpNorm_le_of_ae_bound hdm.restrict (Filter.Eventually.of_forall fun x => by
          rw [Pi.sub_apply, ← dist_eq_norm]; exact hpt x)
    _ = volume S1 ^ p⁻¹ * ENNReal.ofReal ε := by
        rw [Measure.restrict_apply_univ, ENNReal.toReal_ofReal hp0.le]
    _ ≤ η := hAε

/-- **The `3ε` decomposition.** For `w` continuous and `h`, `w` in `Lᵖ`, a unit-mass kernel `ρ`
of compact support satisfies
`‖h ⋆ ρ - h‖_p ≤ ‖w ⋆ ρ - w‖_p + 2 ‖h - w‖_p`, by Young's inequality for `(h - w) ⋆ ρ`. -/
private theorem eLpNorm_convolution_sub_le {p : ℝ} (hp : 1 ≤ p)
    {ρ h w : EuclideanSpace ℝ (Fin d) → ℝ} (hρ0 : 0 ≤ ρ) (hρcont : Continuous ρ)
    (hρcs : HasCompactSupport ρ) (hρ1 : ∫ y, ρ y ∂volume = 1)
    (hh : MemLp h (ENNReal.ofReal p) volume) (hw : MemLp w (ENNReal.ofReal p) volume) :
    eLpNorm (h ⋆ₛ ρ - h) (ENNReal.ofReal p) volume
      ≤ eLpNorm (w ⋆ₛ ρ - w) (ENNReal.ofReal p) volume
        + 2 * eLpNorm (h - w) (ENNReal.ofReal p) volume := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hCE : ∀ f, LocallyIntegrable f volume →
      ConvolutionExists f ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun f hf =>
    hρcs.convolutionExists_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hf hρcont
  have hadd : h ⋆ₛ ρ = (h - w) ⋆ₛ ρ + w ⋆ₛ ρ := by
    have := (hCE _ ((hh.sub hw).locallyIntegrable hq1)).add_distrib
      (hCE _ (hw.locallyIntegrable hq1))
    rwa [show (h - w) + w = h from by funext x; simp] at this
  have hfun : h ⋆ₛ ρ - h = (h - w) ⋆ₛ ρ + ((w ⋆ₛ ρ - w) + (w - h)) := by
    funext x
    have := congrFun hadd x
    simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
    rw [this]; ring
  rw [hfun]
  calc _ ≤ eLpNorm ((h - w) ⋆ₛ ρ) (ENNReal.ofReal p) volume
        + (eLpNorm (w ⋆ₛ ρ - w) (ENNReal.ofReal p) volume
          + eLpNorm (w - h) (ENNReal.ofReal p) volume) :=
        (eLpNorm_add_le hq1).trans (add_le_add le_rfl (eLpNorm_add_le hq1))
    _ ≤ eLpNorm (h - w) (ENNReal.ofReal p) volume
        + (eLpNorm (w ⋆ₛ ρ - w) (ENNReal.ofReal p) volume
          + eLpNorm (h - w) (ENNReal.ofReal p) volume) := by
        rw [eLpNorm_sub_comm w h]
        exact add_le_add (eLpNorm_convolution_le hp hρ0 hρcont.aestronglyMeasurable hρ1
          (hh.sub hw)) le_rfl
    _ = _ := by ring

/-- **`Lᵖ` convergence of mollifications.** For `1 ≤ p`, an `Lᵖ` function `h`, and a family of
normalised bumps whose outer radii tend to `0` (with a bounded inner/outer ratio), the
mollifications `h ⋆ ρ_ε` converge to `h` in `Lᵖ`. Proved by a density `3ε` argument: approximate
`h` in `Lᵖ` by a smooth compactly supported `w` (`MeasureTheory.MemLp.exist_eLpNorm_sub_le`),
bound the tail `(h - w) ⋆ ρ_ε` by `eLpNorm_convolution_le`, and send `w ⋆ ρ_ε - w` to zero with
`tendsto_eLpNorm_bump_convolution_sub`. No `Lᵖ`-continuity of translation is used. -/
theorem tendsto_eLpNorm_convolution_sub {p : ℝ} (hp : 1 ≤ p)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : MemLp h (ENNReal.ofReal p) volume)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin d))} {K : ℝ}
    (hφ : Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (_hK : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn) :
    Filter.Tendsto
      (fun i => eLpNorm
          (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) - h)
          (ENNReal.ofReal p) volume) l (𝓝 0) := by
  have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ∞ with rfl | hηtop
  · exact Filter.Eventually.of_forall fun _ => le_top
  -- density: pick a smooth compactly supported `w` within `δ = η/3` of `h`
  set δ : ℝ := η.toReal / 3 with hδdef
  have hδ0 : 0 < δ := by have := ENNReal.toReal_pos hη.ne' hηtop; positivity
  obtain ⟨w, hwcs, hwsmooth, hwle⟩ := hh.exist_eLpNorm_sub_le hqtop hq1 hδ0
  have hwc : Continuous w := hwsmooth.continuous
  have hwml : MemLp w (ENNReal.ofReal p) volume := hwc.memLp_of_hasCompactSupport hwcs
  -- the middle term tends to zero, hence is eventually `≤ δ`
  have hmid_ev := ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_bump_convolution_sub hp hwc hwcs hφ)
    (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ0)
  filter_upwards [hmid_ev] with i hi
  refine (eLpNorm_convolution_sub_le hp (ρ := (φ i).normed volume) (fun x => (φ i).nonneg_normed x)
    ((φ i).contDiff_normed (n := 1)).continuous (φ i).hasCompactSupport_normed
    (φ i).integral_normed hh hwml).trans ?_
  calc _ ≤ ENNReal.ofReal δ + 2 * ENNReal.ofReal δ :=
        add_le_add hi (mul_le_mul' le_rfl hwle)
    _ = η := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add hδ0.le (by positivity),
          show δ + 2 * δ = η.toReal from by rw [hδdef]; ring, ENNReal.ofReal_toReal hηtop]

/-- **The standard shrinking mollifiers.** The bump of outer radius `δ / (n + 1)` and inner
radius half of it. -/
def stdBump {E : Type*} [NormedAddCommGroup E] (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ContDiffBump (0 : E) where
  rIn := δ / (n + 1) / 2
  rOut := δ / (n + 1)
  rIn_pos := half_pos (by positivity)
  rIn_lt_rOut := half_lt_self (by positivity)

/-- The outer radius of the standard mollifier. -/
@[simp]
theorem rOut_stdBump {E : Type*} [NormedAddCommGroup E]
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : (stdBump (E := E) δ hδ n).rOut = δ / (n + 1) := rfl

/-- The inner radius of the standard mollifier. -/
@[simp]
theorem rIn_stdBump {E : Type*} [NormedAddCommGroup E]
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : (stdBump (E := E) δ hδ n).rIn = δ / (n + 1) / 2 := rfl

/-- The outer radii of the standard mollifiers tend to zero. -/
theorem tendsto_rOut_stdBump {E : Type*} [NormedAddCommGroup E]
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun n => (stdBump (E := E) δ hδ n).rOut) Filter.atTop (𝓝 0) := by
  simp only [rOut_stdBump]
  exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- The outer radii of the standard mollifiers are at most `δ`. -/
theorem rOut_stdBump_le_self {E : Type*} [NormedAddCommGroup E]
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (stdBump (E := E) δ hδ n).rOut ≤ δ := by
  rw [rOut_stdBump]
  exact div_le_self hδ.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])

/-- The standard mollifiers have bounded ratio of radii. -/
theorem rOut_stdBump_le {E : Type*} [NormedAddCommGroup E]
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (stdBump (E := E) δ hδ n).rOut ≤ 2 * (stdBump (E := E) δ hδ n).rIn := by
  simp only [rOut_stdBump, rIn_stdBump]
  exact le_of_eq (by ring)

/-- The mollification of a locally integrable function is smooth. -/
theorem contDiff_convolution_normed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E)) {h : E → ℝ}
    (hh : LocallyIntegrable h μ) :
    ContDiff ℝ (⊤ : ℕ∞) (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ρ.normed μ) :=
  ρ.hasCompactSupport_normed.contDiff_convolution_right _ hh ρ.contDiff_normed

/-- The mollification of a compactly supported function has compact support. -/
theorem hasCompactSupport_convolution_normed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [HasContDiffBump E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E))
    {h : E → ℝ} (hh : HasCompactSupport h) :
    HasCompactSupport (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ρ.normed μ) :=
  HasCompactSupport.convolution _ hh ρ.hasCompactSupport_normed

/-- **Mollifications converge in `L¹`.** The standard mollifications of an integrable function
converge to it in `L¹`. -/
theorem tendsto_eLpNorm_one_stdBump_convolution_sub {δ : ℝ} (hδ : 0 < δ)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : Integrable h volume) :
    Filter.Tendsto (fun n => eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (stdBump δ hδ n : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).normed volume - h) 1 volume)
      Filter.atTop (𝓝 0) := by
  simpa using tendsto_eLpNorm_convolution_sub le_rfl
    (by rw [ENNReal.ofReal_one]; exact memLp_one_iff_integrable.mpr hh) (tendsto_rOut_stdBump hδ)
    (Filter.Eventually.of_forall (rOut_stdBump_le hδ))

/-- **Lowering an exponent on a finite measure space costs a constant.** For `0 < p ≤ q` there
is `A` with `‖f‖_{Lᵖ} ≤ A ‖f‖_{Lq}`, namely `μ(univ)^{1/p - 1/q}`. -/
theorem exists_const_eLpNorm_le_of_le {α E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] [NormedAddCommGroup E] {p q : ℝ≥0∞} (hp : p ≠ 0) (hpq : p ≤ q) :
    ∃ A : ℝ≥0, ∀ f : α → E, AEStronglyMeasurable f μ → eLpNorm f p μ ≤ A * eLpNorm f q μ := by
  have he : 0 ≤ 1 / p.toReal - 1 / q.toReal := by
    rcases eq_or_ne q ⊤ with rfl | hq
    · simp
    · rw [sub_nonneg]
      exact one_div_le_one_div_of_le (ENNReal.toReal_pos hp (ne_top_of_le_ne_top hq hpq))
        (ENNReal.toReal_mono hq hpq)
  refine ⟨(μ univ ^ (1 / p.toReal - 1 / q.toReal)).toNNReal, fun f hf => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg he (measure_ne_top μ _)), mul_comm]
  exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf

/-- A function bounded by `B` together with its `d` partial derivatives, each bounded by `B`,
has total `a + ∑ k, b k` at most `(d + 1) B`. -/
theorem add_sum_le_of_le {d : ℕ} {a B : ℝ≥0∞} {b : Fin d → ℝ≥0∞} (ha : a ≤ B)
    (hb : ∀ k, b k ≤ B) : a + ∑ k, b k ≤ (d + 1) * B := by
  calc a + ∑ k, b k ≤ B + ∑ _k : Fin d, B := add_le_add ha (Finset.sum_le_sum fun k _ => hb k)
    _ = (d + 1) * B := by simp [add_mul, add_comm]

/-- The sum of `d` seminorms, each at most `B`, is at most `d * B`, read in `ℝ≥0`. -/
theorem sum_toNNReal_eLpNorm_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {g : Fin d → α → ℝ} {p : ℝ≥0∞} {B : ℝ≥0} (h : ∀ k, eLpNorm (g k) p μ ≤ B) :
    ∑ k, (eLpNorm (g k) p μ).toNNReal ≤ d * B := by
  calc ∑ k, (eLpNorm (g k) p μ).toNNReal ≤ ∑ _k : Fin d, B :=
        Finset.sum_le_sum fun k _ =>
          (ENNReal.toNNReal_mono ENNReal.coe_ne_top (h k)).trans_eq (ENNReal.toNNReal_coe B)
    _ = d * B := by simp

/-- **A continuous linear map into `Lp` from an almost everywhere linear family of functions.**
The family `T` sends a point of a normed space to a function in `Lp`, linearly up to null sets,
with `‖T x‖_p ≤ C ‖x‖`. -/
def lpCLM {X α : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : MeasurableSpace α}
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] (T : X → α → ℝ) (hT : ∀ x, MemLp (T x) p μ)
    (hadd : ∀ x y, T (x + y) =ᵐ[μ] T x + T y) (hsmul : ∀ (c : ℝ) x, T (c • x) =ᵐ[μ] c • T x)
    (C : ℝ≥0) (hC : ∀ x, eLpNorm (T x) p μ ≤ C * ‖x‖ₑ) : X →L[ℝ] Lp ℝ p μ :=
  LinearMap.mkContinuous
    { toFun := fun x => (hT x).toLp (T x)
      map_add' := fun x y => by
        rw [MemLp.toLp_congr _ ((hT x).add (hT y)) (hadd x y), MemLp.toLp_add]
      map_smul' := fun c x => by
        rw [MemLp.toLp_congr _ ((hT x).const_smul c) (hsmul c x), MemLp.toLp_const_smul]
        rfl }
    C (fun x => by
      change ‖(hT x).toLp (T x)‖ ≤ C * ‖x‖
      rw [Lp.norm_toLp]
      refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg C.coe_nonneg (norm_nonneg x))
        ((hC x).trans_eq ?_)
      rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ofReal_norm])

/-- `lpCLM T` agrees almost everywhere with the family it is built from. -/
theorem coeFn_lpCLM {X α : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] {T : X → α → ℝ}
    {hT : ∀ x, MemLp (T x) p μ} {hadd : ∀ x y, T (x + y) =ᵐ[μ] T x + T y}
    {hsmul : ∀ (c : ℝ) x, T (c • x) =ᵐ[μ] c • T x} {C : ℝ≥0}
    {hC : ∀ x, eLpNorm (T x) p μ ≤ C * ‖x‖ₑ} (x : X) :
    ⇑(lpCLM T hT hadd hsmul C hC x) =ᵐ[μ] T x :=
  MemLp.coeFn_toLp (hT x)

/-- **Inclusion of `Lq` into `Lp` on a finite measure space**, for `p ≤ q`. -/
def lpInclusion {α : Type*} {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) : Lp ℝ q μ →L[ℝ] Lp ℝ p μ :=
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos (Fact.out : 1 ≤ p)).ne'
  lpCLM (fun f : Lp ℝ q μ => ⇑f) (fun f => (Lp.memLp f).mono_exponent hpq)
    (fun f g => Lp.coeFn_add f g) (fun c f => Lp.coeFn_smul c f)
    (exists_const_eLpNorm_le_of_le (μ := μ) (E := ℝ) hp0 hpq).choose fun f =>
    ((exists_const_eLpNorm_le_of_le (μ := μ) (E := ℝ) hp0 hpq).choose_spec f
      (Lp.aestronglyMeasurable f)).trans_eq (by rw [Lp.enorm_def])

/-- The inclusion of `Lq` into `Lp` is the identity on representatives. -/
theorem coeFn_lpInclusion {α : Type*} {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) (f : Lp ℝ q μ) :
    ⇑(lpInclusion μ hpq f) =ᵐ[μ] ⇑f :=
  MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hpq)

/-- The inclusion of `Lq` into `Lp` is injective. -/
theorem lpInclusion_injective {α : Type*} {m : MeasurableSpace α} (μ : Measure α)
    [IsFiniteMeasure μ] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) :
    Function.Injective (lpInclusion μ hpq) := fun f g h =>
  Lp.ext ((coeFn_lpInclusion μ hpq f).symm.trans
    ((Lp.ext_iff.mp h).trans (coeFn_lpInclusion μ hpq g)))

end EllipticPdes.Embedding
