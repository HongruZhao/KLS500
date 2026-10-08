/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license; full license is distributed in
sources/licenses/EllipticPDE-Apache-2.0.txt.
Authors: Alejandro Soto Franco

The generic approximation proof is adapted from EllipticPDE revision
2138a84891e025a4e0ad3013f5b1041fac8dce5e,
lean/EllipticPdes/Embedding/Convolution.lean, lines 174-360.
Source: https://github.com/alejandro-soto-franco/EllipticPDE
Namespace, import wrapper, and final concrete-mollifier corollary are local.
-/
import KLS.ScalarMollification
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Strong L² approximation by the actual mollifiers

The probability-kernel bound and density of smooth compact functions imply
strong Lᵖ convergence, not merely almost-everywhere convergence. The concrete
shrinking sequence then has vanishing actual L² error.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution Topology Pointwise

noncomputable section
namespace KLS.ProbabilityKernel

variable {d : ℕ}
local notation:67 f:68 " ⋆ₛ " g:68 =>
  MeasureTheory.convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) volume

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


end KLS.ProbabilityKernel
namespace KLS

/-- Actual strong L² convergence of the fixed shrinking mollifier sequence. -/
theorem eLpNorm_mollify_sub_tendsto_zero {n : ℕ} {f : Space n → ℝ}
    (hf : MemLp f 2 volume) :
    Filter.Tendsto (fun k => eLpNorm (mollify k f - f) 2 volume) Filter.atTop (𝓝 0) := by
  have hr : Filter.Tendsto (fun k => (mollifierBump n k).rOut) Filter.atTop (𝓝 0) := by
    simpa only [mollifierBump, mul_zero] using cutoffScale_tendsto_zero.const_mul 2
  have he := ProbabilityKernel.tendsto_eLpNorm_convolution_sub (p := 2) (by norm_num)
    (by simpa using hf) hr (Filter.Eventually.of_forall (fun _ => le_rfl))
  simpa only [ENNReal.ofReal_ofNat, mollify, scalarConvolution, mollifierKernel] using he

end KLS
end

#print axioms KLS.ProbabilityKernel.tendsto_eLpNorm_convolution_sub
#print axioms KLS.eLpNorm_mollify_sub_tendsto_zero
