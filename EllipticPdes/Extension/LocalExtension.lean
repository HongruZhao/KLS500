/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.PartitionOfUnity
public import EllipticPdes.Extension.Patch
public import EllipticPdes.Extension.Motion
public import EllipticPdes.Extension.BoundaryChart

/-!
# Local boundary extension

Guo's Theorem III.2.2 reaches its third step with a local extension for each chart: a class on
the chart's neighbourhood agreeing with the original on the part of the domain that
neighbourhood meets. This file proves that statement, which is the whole content of his step 2
once the chart is in hand.

The extension is the composite of four linear maps on pairs of a class and a gradient: a cutoff
between two balls makes the class reach the whole region above the chart's graph, the rigid
motion of the chart takes it into the coordinates the graph is written in, the reflection
extends it across the graph, and the motion takes the result back. Each map is linear by
construction, so the extension is linear in the class. Guo's step 2 works with a function smooth
up to the boundary and reads the chain rule off it; here every step is a weak gradient.

Two points where the statement is narrower than the machinery. The chart asks nothing of the
gradient of its graph, as Evans' definition does not, so the construction runs on the truncated
graph `truncatedGraph`, whose region agrees with the chart's on exactly the ball in play. The
conclusion is on a ball strictly inside the chart's, which is where the cutoff is one, and is
what a partition of unity subordinate to the cover asks for anyway.

## Constant before the class

Clause (iii) of the theorem asks for a constant quantified before the class. The truncated
graph and the cutoff depend on the chart and the two radii alone, so the constant of
`localOp_bound` depends on them and not on the class.

## Main declarations

* `EllipticPdes.Extension.localOp`: the extension as a linear map on pairs.
* `EllipticPdes.Extension.localOp_spec` and `EllipticPdes.Extension.localOp_bound`: its weak
  gradient and its bound in every `Lᵖ` seminorm.
* `EllipticPdes.Extension.localExtension_bound`: the local boundary extension with a constant
  fixed before the class.
* `EllipticPdes.Extension.exists_localExtension`: the same with the constant discarded.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20), proof step 2 (p. 21); L. C. Evans, *Partial Differential Equations* (2nd ed.),
§5.4 Theorem 1 (p. 253).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### The extension as a linear map on pairs -/

/-- **Local extension, as a linear map on pairs.** The pair is cut off by `ξ`, moved into the
chart's coordinates, extended across the graph `γ`, and moved back. -/
def localOp (c : C1Chart d) (γ ξ : EuclideanSpace ℝ (Fin d) → ℝ) :
    SobolevPair d →ₗ[ℝ] SobolevPair d :=
  motionOp c.motion ∘ₗ chartOp c.dir γ ∘ₗ motionOp c.motion.symm ∘ₗ cutOp ξ

/-- The truncated graph the extension of chart `c` at `x` runs on. -/
def chartGraph (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) → ℝ :=
  truncatedGraph c.dir c.graph (c.motion x) c.radius_pos

/-- The cutoff between the ball of radius `r` and the chart's ball of radius `R > 0`: a bump equal
to one on the first and supported inside the second. -/
def chartBump (x : EuclideanSpace ℝ (Fin d)) {r R : ℝ} (hR : 0 < R) (hrR : r < R) :
    ContDiffBump x where
  rIn := (max r 0 + R) / 2
  rOut := ((max r 0 + R) / 2 + R) / 2
  rIn_pos := by have := le_max_right r 0; positivity
  rIn_lt_rOut := by linarith [max_lt hrR hR]

/-- **Local extension of a class.** -/
def localExt (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hrc : r < c.radius)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  (localOp c (chartGraph c x) (chartBump x c.radius_pos hrc) (u, 0)).1

/-- **Gradient of the local extension of a class.** -/
def localExtGrad (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hrc : r < c.radius)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) :
    Fin d → EuclideanSpace ℝ (Fin d) → ℝ :=
  (localOp c (chartGraph c x) (chartBump x c.radius_pos hrc) (u, g)).2

/-- `localOp` at the data of `x` is the pair of `localExt` and `localExtGrad`. -/
theorem localOp_chart_apply (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hrc : r < c.radius) (w : SobolevPair d) :
    localOp c (chartGraph c x) (chartBump x c.radius_pos hrc) w
      = (localExt c x hrc w.1, localExtGrad c x hrc w.1 w.2) := rfl

/-! ### The graph and the cutoff -/

/-- What `chartGraph` is: a `C¹` graph of bounded gradient, independent of the direction, and
describing the chart's region on the chart's ball. -/
theorem chartGraph_spec (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ M : ℝ, ContDiff ℝ 1 (chartGraph c x) ∧ IndepCoord c.dir (chartGraph c x) ∧
      (∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k (chartGraph c x) y‖ ≤ M) ∧
      aboveGraph c.dir (chartGraph c x) ∩ ball (c.motion x) c.radius
        = aboveGraph c.dir c.graph ∩ ball (c.motion x) c.radius := by
  obtain ⟨M, hM⟩ := exists_bound_partialD_truncatedGraph (z := c.motion x) c.radius_pos
    c.graph_contDiff c.graph_indep
  exact ⟨M, contDiff_truncatedGraph _ c.graph_contDiff,
    indepCoord_truncatedGraph _ c.graph_indep, hM, aboveGraph_truncatedGraph_inter _⟩

/-- What `chartBump` is: smooth, equal to one on the closed ball of radius `r`, and supported in
the open ball of radius `R`. -/
theorem chartBump_spec (x : EuclideanSpace ℝ (Fin d)) {r R : ℝ} (hR : 0 < R) (hrR : r < R) :
    ContDiff ℝ (⊤ : ℕ∞) (chartBump x hR hrR) ∧
      (∀ y ∈ closedBall x r, chartBump x hR hrR y = 1) ∧
      HasCompactSupport (chartBump x hR hrR) ∧ tsupport (chartBump x hR hrR) ⊆ ball x R := by
  refine ⟨(chartBump x hR hrR).contDiff, fun y hy => (chartBump x hR hrR).one_of_mem_closedBall
    (closedBall_subset_closedBall (by simp [chartBump]; linarith [le_max_left r 0]) hy),
    (chartBump x hR hrR).hasCompactSupport, ?_⟩
  rw [(chartBump x hR hrR).tsupport_eq]
  exact closedBall_subset_ball (by simp [chartBump]; linarith [max_lt hrR hR])

/-- On the ball of the chart, the region above the truncated graph, pulled back through the
motion, is the domain. -/
theorem region_chartGraph_inter {c : C1Chart d} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {x : EuclideanSpace ℝ (Fin d)} (hfits : c.Fits Ω x) :
    (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹'
        aboveGraph c.dir (chartGraph c x) ∩ ball x c.radius = Ω ∩ ball x c.radius := by
  obtain ⟨-, -, -, -, h⟩ := chartGraph_spec c x
  have h' := congrArg
    (fun s => (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' s) h
  rw [c.fits_ball hfits]
  simpa [Set.preimage_inter, c.motion.isometry.preimage_ball, C1Chart.region] using h'

/-! ### Weak gradient and integrability of the local extension -/

/-- **Weak gradient of the local extension.** For a graph `γ` with a bounded gradient and a
cutoff `ξ` supported in the chart's ball, on which the region above `γ` is the domain, the pair
`localOp c γ ξ (u, g)` has a weak gradient on the whole space and integrable components. -/
theorem localOp_spec {c : C1Chart d} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {x : EuclideanSpace ℝ (Fin d)} {γ ξ : EuclideanSpace ℝ (Fin d) → ℝ} {M : ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord c.dir γ)
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M)
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hξcs : HasCompactSupport ξ)
    (hξs : tsupport ξ ⊆ ball x c.radius)
    (hAW : (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹'
        aboveGraph c.dir γ ∩ ball x c.radius = Ω ∩ ball x c.radius)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u Ω volume) (hgi : ∀ k, IntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Set.univ (localOp c γ ξ (u, g)).1 (localOp c γ ξ (u, g)).2 ∧
      Integrable (localOp c γ ξ (u, g)).1 volume ∧
      ∀ k, Integrable ((localOp c γ ξ (u, g)).2 k) volume := by
  have hAopen : IsOpen (aboveGraph c.dir γ) := isOpen_aboveGraph hγ.continuous
  have hA'open := hAopen.preimage c.motion.continuous
  have hsub : (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹'
      aboveGraph c.dir γ ∩ ball x c.radius ⊆ Ω := hAW ▸ Set.inter_subset_left
  obtain ⟨hcw, hci, hcg⟩ := cutOp_spec hA'open.measurableSet measurableSet_ball hξ hξcs hξs
    (hu.mono_set hsub) (fun k => (hgi k).mono_set hsub) (hwg.mono hsub)
  obtain ⟨hmw, hmi, hmg⟩ := motionOp_spec hci hcg hcw c.motion.symm
  rw [show (c.motion.symm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹'
    ((c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' aboveGraph c.dir γ)
    = aboveGraph c.dir γ from by ext y; simp] at hmw hmi hmg
  have hint := integrable_chartExt hγ.differentiable_one hind hmi
  have hintg := integrable_chartExtGrad hγ hind hγb hmg
  obtain ⟨hfw, hfi, hfg⟩ := motionOp_spec (B := Set.univ) hint.integrableOn
    (fun k => (hintg k).integrableOn) (hasWeakGradOn_chartExt hγ hind hγb hmi hmg hmw) c.motion
  rw [Set.preimage_univ] at hfw hfi hfg
  exact ⟨hfw, integrableOn_univ.1 hfi, fun k => integrableOn_univ.1 (hfg k)⟩

/-! ### The bound -/

/-- **The constant of the local extension**, for a cutoff and its partials bounded by `B` and a
graph with partials bounded by `M`. -/
def localConst (d : ℕ) (B M : ℝ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal B + d * ((2 + 4 * ENNReal.ofReal M) * (d * ENNReal.ofReal B))

/-- The constant of the local extension is finite. -/
theorem localConst_ne_top (d : ℕ) (B M : ℝ) : localConst d B M ≠ ⊤ := by
  unfold localConst
  finiteness

/-- **A pair cut off and moved by an isometry.** Cutting by `ξ`, supported in `W` where the region
`A'` lies in `Ω`, and moving by `e` gives integrable components over the preimage of `A'`, whose
seminorms there are bounded by those of the pair over `Ω`: the function by `B` times the pair
seminorm, and each gradient component by `d` times that. -/
theorem eLpNorm_motionOp_cutOp_le {A' W Ω : Set (EuclideanSpace ℝ (Fin d))}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (hA'm : MeasurableSet A') (hW : MeasurableSet W) (hΩm : MeasurableSet Ω)
    (hsub : A' ∩ W ⊆ Ω) {ξ : EuclideanSpace ℝ (Fin d) → ℝ} {B : ℝ}
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hξcs : HasCompactSupport ξ) (hξs : tsupport ξ ⊆ W)
    (hξb : ∀ y, ‖ξ y‖ ≤ B) (hξdb : ∀ (k : Fin d) y, ‖partialD k ξ y‖ ≤ B)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : IntegrableOn u Ω volume)
    (hgi : ∀ k, IntegrableOn (g k) Ω volume) :
    IntegrableOn (motionOp e (cutOp ξ (u, g))).1
        ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' A') volume ∧
      (∀ k, IntegrableOn ((motionOp e (cutOp ξ (u, g))).2 k)
        ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' A') volume) ∧
      eLpNorm (motionOp e (cutOp ξ (u, g))).1 p
        (volume.restrict ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' A'))
          ≤ ENNReal.ofReal B * pairNorm p (volume.restrict Ω) u g ∧
      ∀ k, eLpNorm ((motionOp e (cutOp ξ (u, g))).2 k) p
        (volume.restrict ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' A'))
          ≤ d * (ENNReal.ofReal B * pairNorm p (volume.restrict Ω) u g) := by
  have hoff : ∀ y, y ∉ W → ξ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hc => hy (hξs hc)
  have h1u : eLpNorm (cutOp ξ (u, g)).1 p (volume.restrict A')
      ≤ ENNReal.ofReal B * pairNorm p (volume.restrict Ω) u g :=
    (eLpNorm_cutoff_mul_le hA'm hΩm hξb hξ.continuous.aestronglyMeasurable hu.1 hoff hsub).trans
      (mul_le_mul_right eLpNorm_le_pairNorm _)
  have h1g : ∀ i, eLpNorm ((cutOp ξ (u, g)).2 i) p (volume.restrict A')
      ≤ ENNReal.ofReal B * pairNorm p (volume.restrict Ω) u g := fun i =>
    (eLpNorm_cutOp_snd_le hA'm hΩm hξ hξs hξb i (hξdb i) hp hu.1 (hgi i).1 hsub).trans
      (mul_le_mul_right (by rw [add_comm]; exact eLpNorm_add_grad_le_pairNorm i) _)
  obtain ⟨hci, hcg⟩ := integrableOn_cutOp hA'm hW hξ hξcs hξs (hu.mono_set hsub)
    fun k => (hgi k).mono_set hsub
  obtain ⟨hmi, hmg⟩ := integrableOn_motionOp hci hcg e
  refine ⟨hmi, hmg, (eLpNorm_comp_linearIsometry hci.1 e).le.trans h1u, fun k => ?_⟩
  refine (eLpNorm_grad_comp_linearIsometry_le hp (fun i => (hcg i).1) e k).trans ?_
  calc _ ≤ ∑ _i : Fin d, ENNReal.ofReal B * pairNorm p (volume.restrict Ω) u g :=
        Finset.sum_le_sum fun i _ => h1g i
    _ = d * (ENNReal.ofReal B * pairNorm p (volume.restrict Ω) u g) := by simp

/-- **Bound on the local extension in every `Lᵖ` seminorm.** The cutoff multiplies the pair by a
factor of at most `B`, the motion preserves the seminorm and mixes the `d` components of the
gradient, the chart doubles and adds `4 M` times the normal component, and the motion back mixes
the components once more. -/
theorem localOp_bound {c : C1Chart d} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {x : EuclideanSpace ℝ (Fin d)} {γ ξ : EuclideanSpace ℝ (Fin d) → ℝ} {M B : ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord c.dir γ) (hM0 : 0 ≤ M)
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M)
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hξcs : HasCompactSupport ξ) (hξs : tsupport ξ ⊆ ball x c.radius)
    (hξb : ∀ y, ‖ξ y‖ ≤ B) (hξdb : ∀ (k : Fin d) y, ‖partialD k ξ y‖ ≤ B)
    (hΩm : MeasurableSet Ω)
    (hAW : (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹'
        aboveGraph c.dir γ ∩ ball x c.radius = Ω ∩ ball x c.radius)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : IntegrableOn u Ω volume)
    (hgi : ∀ k, IntegrableOn (g k) Ω volume) :
    eLpNorm (localOp c γ ξ (u, g)).1 p volume
        ≤ localConst d B M * pairNorm p (volume.restrict Ω) u g ∧
      ∀ k, eLpNorm ((localOp c γ ξ (u, g)).2 k) p volume
        ≤ localConst d B M * pairNorm p (volume.restrict Ω) u g := by
  set N := pairNorm p (volume.restrict Ω) u g with hN
  set A' := (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹'
    aboveGraph c.dir γ with hA'
  have hAopen : IsOpen (aboveGraph c.dir γ) := isOpen_aboveGraph hγ.continuous
  have hA'm : MeasurableSet A' := (hAopen.preimage c.motion.continuous).measurableSet
  have hsub : A' ∩ ball x c.radius ⊆ Ω := hAW ▸ Set.inter_subset_left
  have hAeq : (c.motion.symm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' A'
      = aboveGraph c.dir γ := by ext y; simp [hA']
  -- the cutoff pair, moved into the chart's coordinates, over the region above the graph
  obtain ⟨hmi, hmg, h2u, h2g⟩ := eLpNorm_motionOp_cutOp_le (B := B) c.motion.symm hA'm
    measurableSet_ball hΩm hsub hξ hξcs hξs hξb hξdb hp hu hgi
  rw [hAeq] at hmi hmg h2u h2g
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  -- the extension across the graph
  have h3u : eLpNorm (chartExt c.dir γ (motionOp c.motion.symm (cutOp ξ (u, g))).1) p volume
      ≤ 2 * (ENNReal.ofReal B * N) :=
    (eLpNorm_chartExt_le hγd hind hp hmi.1).trans (mul_le_mul_right h2u 2)
  have h3g : ∀ i, eLpNorm (chartExtGrad c.dir γ (motionOp c.motion.symm (cutOp ξ (u, g))).2 i)
      p volume ≤ (2 + 4 * ENNReal.ofReal M) * (d * (ENNReal.ofReal B * N)) := fun i =>
    (eLpNorm_chartExtGrad_le hγ hind hM0 hγb hp (fun k => (hmg k).1) i).trans (by
      calc _ ≤ 2 * (d * (ENNReal.ofReal B * N))
            + 4 * ENNReal.ofReal M * (d * (ENNReal.ofReal B * N)) :=
            add_le_add (mul_le_mul_right (h2g i) 2) (mul_le_mul_right (h2g c.dir) _)
        _ = _ := by ring)
  -- the motion back
  have hmp := c.motion.measurePreserving
  have hK1 : 2 * ENNReal.ofReal B ≤ localConst d B M := le_self_add
  have hK2 : (d : ℝ≥0∞) * ((2 + 4 * ENNReal.ofReal M) * (d * ENNReal.ofReal B))
      ≤ localConst d B M := le_add_self
  refine ⟨?_, fun k => ?_⟩
  · calc _ = eLpNorm (chartExt c.dir γ (motionOp c.motion.symm (cutOp ξ (u, g))).1) p volume :=
          eLpNorm_comp_measurePreserving (integrable_chartExt hγd hind hmi).1 hmp
      _ ≤ 2 * (ENNReal.ofReal B * N) := h3u
      _ = 2 * ENNReal.ofReal B * N := (mul_assoc _ _ _).symm
      _ ≤ _ := by gcongr
  · have hmg' : ∀ i, AEStronglyMeasurable
        (chartExtGrad c.dir γ (motionOp c.motion.symm (cutOp ξ (u, g))).2 i)
        (volume.restrict Set.univ) := fun i =>
      (integrable_chartExtGrad hγ hind hγb hmg i).1.mono_measure (by simp)
    have h := eLpNorm_grad_comp_linearIsometry_le hp hmg' c.motion k
    simp only [Set.preimage_univ, Measure.restrict_univ] at h
    refine h.trans ?_
    calc _ ≤ ∑ _i : Fin d, (2 + 4 * ENNReal.ofReal M) * (d * (ENNReal.ofReal B * N)) :=
          Finset.sum_le_sum fun i _ => h3g i
      _ = (d : ℝ≥0∞) * ((2 + 4 * ENNReal.ofReal M) * (d * ENNReal.ofReal B)) * N := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ _ := by gcongr

/-- **Agreement of the local extension with the class** on the part of the region where the
cutoff is one. -/
theorem localOp_fst_eq {c : C1Chart d} {γ ξ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hind : IndepCoord c.dir γ) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹'
      aboveGraph c.dir γ) (hξ : ξ y = 1) : (localOp c γ ξ (u, g)).1 y = u y := by
  change chartExt c.dir γ (fun z => ξ (c.motion.symm z) * u (c.motion.symm z)) (c.motion y) = u y
  rw [chartExt_eq_of_mem hind hy]
  simp [hξ]

/-- **Guo's local boundary extension with its constant** (Theorem III.2.2, proof step 2, p. 21).
Near a boundary point the class extends across the boundary: on any ball strictly inside the
chart's, `localExt` has a weak gradient there and agrees with the original on the part of the
domain the ball meets, and both it and its gradient are bounded in every `Lᵖ` seminorm by the
class and its gradient over the domain, with one constant taken before the class. -/
theorem localExtension_bound (c : C1Chart d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) {x : EuclideanSpace ℝ (Fin d)} (hfits : c.Fits Ω x) {r : ℝ}
    (hrc : r < c.radius) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
      HasWeakGradOn (ball x r) (localExt c x hrc u) (localExtGrad c x hrc u g) ∧
        Integrable (localExt c x hrc u) volume ∧
          (∀ k, Integrable (localExtGrad c x hrc u g k) volume) ∧
          (∀ y ∈ Ω ∩ ball x r, localExt c x hrc u y = u y) ∧
          eLpNorm (localExt c x hrc u) p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm (localExtGrad c x hrc u g k) p volume
            ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
              + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) := by
  obtain ⟨M, hγ, hind, hγb, -⟩ := chartGraph_spec c x
  obtain ⟨hξ, hξ1, hξcs, hξs⟩ := chartBump_spec x c.radius_pos hrc
  obtain ⟨B, -, hξb, hξdb⟩ := exists_bound_with_partials hξ hξcs
  have hAW := region_chartGraph_inter hfits
  refine ⟨(localConst d B M).toNNReal, fun u g hu hgi hwg => ?_⟩
  rw [ENNReal.coe_toNNReal (localConst_ne_top d B M)]
  obtain ⟨hw, hI, hIg⟩ := localOp_spec hγ hind hγb hξ hξcs hξs hAW hu hgi hwg
  obtain ⟨hb1, hb2⟩ := localOp_bound hγ hind ((norm_nonneg _).trans (hγb c.dir 0)) hγb hξ hξcs
    hξs hξb hξdb hΩm hAW hp hu hgi
  refine ⟨hw.mono (Set.subset_univ _), hI, hIg, fun y hy => localOp_fst_eq hind ?_ ?_, hb1, hb2⟩
  · have hy' : y ∈ Ω ∩ ball x c.radius := ⟨hy.1, ball_subset_ball hrc.le hy.2⟩
    rw [← hAW] at hy'
    exact hy'.1
  · exact hξ1 y (ball_subset_closedBall hy.2)

/-- **Guo's local boundary extension with its constant**, with the extension quantified away.
This is the form the gluing of step 3 consumes. -/
theorem exists_localExtension_bound (c : C1Chart d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) {x : EuclideanSpace ℝ (Fin d)} (hfits : c.Fits Ω x) {r : ℝ}
    (hrc : r < c.radius) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
      ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
        HasWeakGradOn (ball x r) U G ∧ Integrable U volume ∧
          (∀ k, Integrable (G k) volume) ∧ (∀ y ∈ Ω ∩ ball x r, U y = u y) ∧
          eLpNorm U p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm (G k) p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) := by
  obtain ⟨K, hK⟩ := localExtension_bound c hΩm hfits hrc hp
  refine ⟨K, fun u g hu hgi hwg => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hK u g hu hgi hwg
  exact ⟨_, _, h1, h2, h3, h4, h5, h6⟩

/-- **Guo's local boundary extension** (Theorem III.2.2, proof step 2, p. 21). Near a boundary
point the class extends across the boundary: on any ball strictly inside the chart's, there is a
class with a weak gradient there agreeing with the original on the part of the domain the ball
meets. -/
theorem exists_localExtension (c : C1Chart d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) {x : EuclideanSpace ℝ (Fin d)} (hfits : c.Fits Ω x) {r : ℝ}
    (hrc : r < c.radius) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u Ω volume) (hgi : ∀ k, IntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) :
    ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      HasWeakGradOn (ball x r) U G ∧ Integrable U volume ∧
        (∀ k, Integrable (G k) volume) ∧ ∀ y ∈ Ω ∩ ball x r, U y = u y := by
  obtain ⟨K, hK⟩ := exists_localExtension_bound c hΩm hfits hrc (p := 1) le_rfl
  obtain ⟨U, G, hwgU, hUint, hGint, hag, -, -⟩ := hK u g hu hgi hwg
  exact ⟨U, G, hwgU, hUint, hGint, hag⟩

end EllipticPdes.Extension
