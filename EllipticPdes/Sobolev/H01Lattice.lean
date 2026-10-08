/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.ChainRule
public import EllipticPdes.Regularity.WeakFormDense
public import EllipticPdes.Regularity.PointwiseEquation
public import EllipticPdes.Form.GeneralForm
public import EllipticPdes.Existence.WeakMaximum
public import EllipticPdes.Extension.C1Test
public import EllipticPdes.Sobolev.GraphLimits

/-!
# Truncation in `H₀¹`

`H₀¹(Ω)` is closed under the truncation `u ↦ (u - k)⁺` for `k ≥ 0`. Two steps. A class on the
whole space with an `L²` weak gradient and compact support inside the open set `Ω` lies in
`H₀¹(Ω)`: its mollifications are test functions of `Ω` once the radius is below the distance
from the support to the complement, and they converge to it in `H¹` together with their
gradients, which are the mollified weak gradient. Then, for `V ∈ H₀¹(Ω)` approximated by test
functions `φ_n`, the truncations `(φ_n - k)⁺` have compact support in `Ω` because `k ≥ 0`,
have the weak gradient `∇φ_n` on `{φ_n > k}` by the chain rule for the positive part, so lie in
`H₀¹(Ω)` by the first step, and converge in `H¹(Ω)` to `(v - k)⁺` with gradient `∇v` on
`{v > k}`: the function coordinates because truncation is `1`-Lipschitz, the gradient
coordinates along a subsequence converging almost everywhere by dominated convergence, the
level set `{v = k}` giving nothing because the weak gradient vanishes there.

This is the step the proof of the weak maximum principle takes for granted when it tests
against `(u - k)⁺`. With it, the principle applies to every subsolution in `H₀¹(Ω)`, and the
uniqueness of the generalised Dirichlet problem follows by applying it to the solution and to
its negative.

## Main declarations

* `EllipticPdes.Sobolev.mem_H01_of_hasCompactSupport`: a compactly supported class with `L²`
  weak gradient lies in `H₀¹`.
* `EllipticPdes.Sobolev.exists_mem_H01_posPart_sub_const`: `H₀¹` is closed under
  `u ↦ (u - k)⁺` for `k ≥ 0`.
* `EllipticPdes.Sobolev.weak_maximum_principle_H01`: a subsolution in `H₀¹` is nonpositive.
* `EllipticPdes.Sobolev.eq_zero_of_weakSolution_H01`: uniqueness of the generalised Dirichlet
  problem.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§8.1 Theorem 8.1 and Corollary 8.2 (pp. 179–180);
L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.3.1 Theorem 1 (p. 264).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Embedding EllipticPdes.Extension EllipticPdes.Regularity

local notation "Lsm" => ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Mollification -/

/-- A square-integrable function of compact support is integrable. -/
lemma integrable_of_memLp_hasCompactSupport {w : EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : MemLp w 2 volume) (hwcs : HasCompactSupport w) : Integrable w volume := by
  have : IsFiniteMeasure (volume.restrict (tsupport w)) :=
    isFiniteMeasure_restrict.2 hwcs.measure_lt_top.ne
  have : IntegrableOn w (tsupport w) volume :=
    (hw.mono_measure Measure.restrict_le_self).integrable one_le_two
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport w)).mp this

/-- **Mollifications are test functions.** The mollification of an integrable function of compact
support by a bump whose outer radius thickens the support inside `Ω` is a test function of `Ω`. -/
lemma isTestFn_convolution_normed {w : EuclideanSpace ℝ (Fin d) → ℝ} (hwint : Integrable w volume)
    (hwcs : HasCompactSupport w) (ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (hρ : cthickening ρ.rOut (tsupport w) ⊆ Ω) :
    IsTestFn Ω (w ⋆[Lsm, volume] ρ.normed volume) := by
  refine ⟨ρ.hasCompactSupport_normed.contDiff_convolution_right (L := Lsm)
      hwint.locallyIntegrable ρ.contDiff_normed,
    HasCompactSupport.convolution (L := Lsm) hwcs ρ.hasCompactSupport_normed,
    (closure_minimal (fun x hx => ?_) isClosed_cthickening).trans hρ⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp (support_convolution_subset Lsm hx)
  rw [ρ.support_normed_eq] at hb
  refine mem_cthickening_of_dist_le (a + b) a ρ.rOut _ (subset_tsupport w ha) ?_
  rw [dist_eq_norm, add_sub_cancel_left]
  exact (mem_ball_zero_iff.mp hb).le

/-- Mollifications of a square-integrable function by the bumps of `mollifier` converge to it in
`L²`. -/
lemma tendsto_eLpNorm_mollifier_sub {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : MemLp f 2 volume)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => eLpNorm (f ⋆[Lsm, volume] (mollifier r hr n : ContDiffBump
      (0 : EuclideanSpace ℝ (Fin d))).normed volume - f) 2 volume) atTop (𝓝 0) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have := tendsto_eLpNorm_convolution_sub one_le_two (by rwa [h2]) (tendsto_rOut_mollifier r hr)
    (K := 2) (Eventually.of_forall fun n => le_of_eq (by simp [mollifier]; ring))
  rwa [h2] at this

/-- **Compactly supported classes with `L²` weak gradient lie in `H₀¹`.** A class on the whole
space with an `L²` weak gradient whose support is a compact subset of the open set `Ω` is, with
its gradient, the `H¹(Ω)` limit of its mollifications, which are test functions of `Ω`. -/
theorem mem_H01_of_hasCompactSupport (hΩ : IsOpen Ω) {w : EuclideanSpace ℝ (Fin d) → ℝ}
    {h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hwg : HasWeakGradOn univ w h)
    (hw : MemLp w 2 volume) (hh : ∀ k, MemLp (h k) 2 volume) (hwcs : HasCompactSupport w)
    (hwΩ : tsupport w ⊆ Ω) :
    WithLp.toLp 2 (Fin.cons ((hw.mono_measure Measure.restrict_le_self).toLp w)
      fun k => ((hh k).mono_measure Measure.restrict_le_self).toLp (h k)) ∈ H01 Ω := by
  obtain ⟨δ, hδ, hK'⟩ := IsCompact.exists_cthickening_subset_open hwcs hΩ hwΩ
  have hwint := integrable_of_memLp_hasCompactSupport hw hwcs
  have hv : ∀ n, IsTestFn Ω (w ⋆[Lsm, volume] (mollifier δ hδ n :
      ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).normed volume) := fun n =>
    isTestFn_convolution_normed hwint hwcs _
      ((cthickening_mono (rOut_mollifier_le δ hδ n) _).trans hK')
  have hpartial : ∀ n k, partialD k (w ⋆[Lsm, volume] (mollifier δ hδ n :
      ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).normed volume)
        = h k ⋆[Lsm, volume] (mollifier δ hδ n : ContDiffBump
          (0 : EuclideanSpace ℝ (Fin d))).normed volume := fun n k => funext fun x => by
    simpa only [indicator_univ] using partialD_convolution_eq_of_hasWeakGradOn MeasurableSet.univ
      hwint.integrableOn hwg _ k (x := x) (subset_univ _)
  refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (b := atTop)
    (f := fun n => (hv n).testGraph) ?_ (Eventually.of_forall fun n => (hv n).testGraph_mem_H01)
  change Tendsto _ _ (𝓝 (H1amb.mk _ _))
  rw [tendsto_testGraph_iff hv]
  refine ⟨?_, fun k => ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_eLpNorm_mollifier_sub hw hδ) (fun _ => zero_le) fun n => ?_
    refine le_of_eq_of_le (eLpNorm_congr_ae (EventuallyEq.rfl.sub (by
      exact (hw.mono_measure Measure.restrict_le_self).coeFn_toLp))) ?_
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_eLpNorm_mollifier_sub (hh k) hδ) (fun _ => zero_le) fun n => ?_
    rw [hpartial n k]
    refine le_of_eq_of_le (eLpNorm_congr_ae (EventuallyEq.rfl.sub
      ((hh k).mono_measure Measure.restrict_le_self).coeFn_toLp)) ?_
    exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-! ### Truncation -/

/-- The truncation `t ↦ max (t - k) 0` is `1`-Lipschitz. -/
theorem abs_max_sub_le (a b k : ℝ) : |max (a - k) 0 - max (b - k) 0| ≤ |a - b| := by
  have := abs_max_sub_max_le_abs (a - k) (b - k) 0
  rwa [sub_sub_sub_cancel_right] at this

/-- The truncation `max (φ - k) 0` of a test function of `Ω` has compact support in `Ω`. -/
lemma IsTestFn.posPart_sub_const {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) {k : ℝ}
    (hk : 0 ≤ k) :
    HasCompactSupport (fun x => max (φ x - k) 0) ∧ tsupport (fun x => max (φ x - k) 0) ⊆ Ω := by
  have hsub : tsupport (fun x => max (φ x - k) 0) ⊆ tsupport φ :=
    closure_minimal (fun x hx => subset_tsupport _ fun h0 => Function.mem_support.mp hx (by
      simp only [h0, zero_sub]; exact max_eq_right (neg_nonpos.mpr hk))) (isClosed_tsupport _)
  exact ⟨h.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans h.2.2⟩

/-- At a point where `ψₙ → v` and `g = 0` on the level `v = k`, the truncated values
`1_{ψₙ > k} g` eventually equal `1_{v > k} g`. -/
lemma eventually_ite_lt_sub_eq_zero {ψ : ℕ → ℝ} {v g k : ℝ} (hψ : Tendsto ψ atTop (𝓝 v))
    (hl : v = k → g = 0) :
    ∀ᶠ n in atTop, (if k < ψ n then g else 0) - (if k < v then g else 0) = 0 := by
  rcases lt_trichotomy v k with hlt | heq | hgt
  · filter_upwards [hψ.eventually (gt_mem_nhds hlt)] with n hn
    simp [not_lt.mpr hn.le, not_lt.mpr hlt.le]
  · refine Eventually.of_forall fun n => ?_
    simp only [hl heq]
    split_ifs <;> simp
  · filter_upwards [hψ.eventually (lt_mem_nhds hgt)] with n hn
    simp [hn, hgt]

/-- **Convergence of a level-set indicator.** Let `ψₙ → v` almost everywhere and let `g` be
square integrable and vanish on `{v = k}`. Then `1_{ψₙ > k} g → 1_{v > k} g` in `L²`. -/
lemma tendsto_eLpNorm_indicator_lt_sub {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {ψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} {v g : EuclideanSpace ℝ (Fin d) → ℝ} {k : ℝ}
    (hψm : ∀ n, AEStronglyMeasurable (ψ n) μ) (hvm : AEStronglyMeasurable v μ)
    (hg : MemLp g 2 μ) (hae : ∀ᵐ x ∂μ, Tendsto (fun n => ψ n x) atTop (𝓝 (v x)))
    (hlev : ∀ᵐ x ∂μ, v x = k → g x = 0) :
    Tendsto (fun n => eLpNorm ((fun x => if k < ψ n x then g x else 0)
      - fun x => if k < v x then g x else 0) 2 μ) atTop (𝓝 0) := by
  have hBm : ∀ n, AEStronglyMeasurable ((fun x => if k < ψ n x then g x else 0)
      - fun x => if k < v x then g x else 0) μ := fun n =>
    (aestronglyMeasurable_ite_lt (hψm n) hg.aestronglyMeasurable k).sub
      (aestronglyMeasurable_ite_lt hvm hg.aestronglyMeasurable k)
  have hrepr : ∀ n, eLpNorm ((fun x => if k < ψ n x then g x else 0)
      - fun x => if k < v x then g x else 0) 2 μ = (∫⁻ x, ‖(if k < ψ n x then g x else 0)
        - (if k < v x then g x else 0)‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := fun n => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top (hBm n),
      ENNReal.toReal_ofNat]
    rfl
  simp only [hrepr]
  have hlim : Tendsto (fun n => ∫⁻ x, ‖(if k < ψ n x then g x else 0)
      - (if k < v x then g x else 0)‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖g x‖ₑ ^ (2 : ℝ))
      (fun n => (hBm n).enorm.pow_const _) (fun n => Eventually.of_forall fun x => ?_) ?_ ?_
    · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
        coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
      split_ifs <;> simp
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        hg.eLpNorm_lt_top).ne
    · filter_upwards [hae, hlev] with x hx hxl
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ite_lt_sub_eq_zero hx hxl] with n hn
      rw [hn, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [lintegral_zero] at hlim
  have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp hlim
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this

/-- **Convergence of truncated gradients.** Let `ψₙ → v` almost everywhere, let `Dψₙ → g` in `L²`,
and let `g` vanish on the level set `{v = k}`. Then `1_{ψₙ > k} Dψₙ → 1_{v > k} g` in `L²`. -/
lemma tendsto_eLpNorm_ite_lt_sub {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {ψ Dψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} {v g : EuclideanSpace ℝ (Fin d) → ℝ} {k : ℝ}
    (hψm : ∀ n, AEStronglyMeasurable (ψ n) μ) (hDm : ∀ n, AEStronglyMeasurable (Dψ n) μ)
    (hvm : AEStronglyMeasurable v μ) (hg : MemLp g 2 μ)
    (hD : Tendsto (fun n => eLpNorm (Dψ n - g) 2 μ) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => ψ n x) atTop (𝓝 (v x)))
    (hlev : ∀ᵐ x ∂μ, v x = k → g x = 0) :
    Tendsto (fun n => eLpNorm ((fun x => if k < ψ n x then Dψ n x else 0)
      - fun x => if k < v x then g x else 0) 2 μ) atTop (𝓝 0) := by
  have hA : Tendsto (fun n => eLpNorm (fun x => if k < ψ n x then Dψ n x - g x else 0) 2 μ)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD (fun _ => zero_le)
      fun n => eLpNorm_mono (aestronglyMeasurable_ite_lt (hψm n)
        ((hDm n).sub hg.aestronglyMeasurable) k) fun x => ?_
    simp only [Pi.sub_apply]
    split_ifs <;> simp
  have hsum := hA.add (tendsto_eLpNorm_indicator_lt_sub hψm hvm hg hae hlev)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => ?_
  have hsplit : ((fun x => if k < ψ n x then Dψ n x else 0) - fun x => if k < v x then g x else 0)
      = (fun x => if k < ψ n x then Dψ n x - g x else 0) + ((fun x => if k < ψ n x then g x else 0)
        - fun x => if k < v x then g x else 0) := funext fun x => by
    simp only [Pi.sub_apply, Pi.add_apply]
    split_ifs <;> ring
  rw [hsplit]
  exact eLpNorm_add_le one_le_two

/-- **Truncation in `H₀¹`.** For `V ∈ H₀¹(Ω)` and `k ≥ 0` there is `W ∈ H₀¹(Ω)` whose function
coordinate is `(v - k)⁺` and whose gradient coordinates are those of `V` on `{v > k}` and zero
elsewhere. -/
theorem exists_mem_H01_posPart_sub_const (hΩ : IsOpen Ω) {V : H1amb Ω} (hV : V ∈ H01 Ω)
    {k : ℝ} (hk : 0 ≤ k) :
    ∃ W ∈ H01 Ω,
      ((W 0 : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] (fun x => max ((V 0 x : ℝ) - k) 0) ∧
      ∀ i : Fin d, ((W i.succ : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => if k < (V 0 x : ℝ) then (V i.succ x : ℝ) else 0 := by
  classical
  obtain ⟨φ, hφ, hXt⟩ := exists_seq_isTestFn_tendsto hV
  obtain ⟨hX0, hXi⟩ := (tendsto_testGraph_iff hφ).mp hXt
  set v : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (V 0 x : ℝ) with hvdef
  set g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ := fun i x => (V i.succ x : ℝ) with hgdef
  have hvm : MemLp v 2 (volume.restrict Ω) := Lp.memLp _
  have hgm : ∀ i, MemLp (g i) 2 (volume.restrict Ω) := fun i => Lp.memLp _
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hX0).exists_seq_tendsto_ae
  have hlevel : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), v x = k → g i x = 0 := fun i =>
    ae_eq_zero_of_eq_const_of_hasWeakGradOn hΩ
      (locallyIntegrableOn_of_locallyIntegrable_restrict (hvm.locallyIntegrable one_le_two))
      (fun i => locallyIntegrableOn_of_locallyIntegrable_restrict
        ((hgm i).locallyIntegrable one_le_two))
      (hasWeakGradOn_of_mem_W12 (H01_le_W12 Ω hV)) k i
  -- the truncations of the approximants lie in `H₀¹`
  set ψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun i => φ (ns i) with hψdef
  have hψ : ∀ i, IsTestFn Ω (ψ i) := fun i => hφ (ns i)
  have hψc : ∀ i, Continuous (ψ i) := fun i => (hψ i).continuous
  have hψwg : ∀ i, HasWeakGradOn univ (fun x => max (ψ i x - k) 0)
      fun j x => if k < ψ i x then partialD j (ψ i) x else 0 := fun i =>
    hasWeakGradOn_posPart_sub_const isOpen_univ
      ((hψc i).locallyIntegrable.locallyIntegrableOn _)
      (fun j => ((hψ i).continuous_partialD j).locallyIntegrable.locallyIntegrableOn _)
      (hasWeakGradOn_of_contDiffOn isOpen_univ
        ((hψ i).1.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn) k
  have hwm : ∀ i, MemLp (fun x => max (ψ i x - k) 0) 2 volume := fun i =>
    (((hψc i).sub continuous_const).max continuous_const).memLp_of_hasCompactSupport
      ((hψ i).posPart_sub_const hk).1
  have hhm : ∀ i j, MemLp (fun x => if k < ψ i x then partialD j (ψ i) x else 0) 2 volume :=
    fun i j =>
      (((hψ i).continuous_partialD j).memLp_of_hasCompactSupport
        ((hψ i).hasCompactSupport_partialD j)).of_le
        (aestronglyMeasurable_ite_lt (hψc i).aestronglyMeasurable
          ((hψ i).continuous_partialD j).aestronglyMeasurable k)
        (Eventually.of_forall fun x => by split_ifs <;> simp)
  have hWmem : ∀ i, H1amb.mk (((hwm i).mono_measure Measure.restrict_le_self).toLp _)
      (fun j => ((hhm i j).mono_measure Measure.restrict_le_self).toLp _) ∈ H01 Ω := fun i =>
    mem_H01_of_hasCompactSupport hΩ (hψwg i) (hwm i) (hhm i) ((hψ i).posPart_sub_const hk).1
      ((hψ i).posPart_sub_const hk).2
  -- the limit
  have hwlim : MemLp (fun x => max (v x - k) 0) 2 (volume.restrict Ω) := by
    refine hvm.of_le (((continuous_id.sub continuous_const).max
      continuous_const).comp_aestronglyMeasurable hvm.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self (v x)]) (abs_nonneg _)
  have hhlim : ∀ i, MemLp (fun x => if k < v x then g i x else 0) 2 (volume.restrict Ω) :=
    fun i => (hgm i).of_le (aestronglyMeasurable_ite_lt hvm.aestronglyMeasurable
      (hgm i).aestronglyMeasurable k)
      (Eventually.of_forall fun x => by split_ifs <;> simp)
  refine ⟨H1amb.mk (hwlim.toLp _) fun i => (hhlim i).toLp _, ?_, hwlim.coeFn_toLp,
    fun i => (hhlim i).coeFn_toLp⟩
  refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (b := atTop) ?_
    (Eventually.of_forall hWmem)
  refine (H1amb.tendsto_iff_eLpNorm (f := fun i x => max (ψ i x - k) 0)
    (G := fun i j x => if k < ψ i x then partialD j (ψ i) x else 0)
    (fun i => ((hwm i).mono_measure Measure.restrict_le_self).coeFn_toLp)
    (fun i j => ((hhm i j).mono_measure Measure.restrict_le_self).coeFn_toLp)).mpr ⟨?_, fun j => ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hX0.comp hns.tendsto_atTop) (fun _ => zero_le) fun i => ?_
    refine le_of_eq_of_le (eLpNorm_congr_ae (EventuallyEq.rfl.sub hwlim.coeFn_toLp)) ?_
    refine eLpNorm_mono ((((hψc i).sub continuous_const).max
      continuous_const).aestronglyMeasurable.sub hwlim.aestronglyMeasurable) fun x => ?_
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    exact abs_max_sub_le _ _ _
  · have hae' : ∀ᵐ x ∂(volume.restrict Ω), Tendsto (fun i => ψ i x) atTop (𝓝 (v x)) := hae
    refine (tendsto_eLpNorm_ite_lt_sub (fun i => (hψc i).aestronglyMeasurable)
      (fun i => ((hψ i).continuous_partialD j).aestronglyMeasurable) hvm.aestronglyMeasurable
      (hgm j) ((hXi j).comp hns.tendsto_atTop) hae' (hlevel j)).congr fun i => ?_
    exact (eLpNorm_congr_ae (EventuallyEq.rfl.sub (hhlim j).coeFn_toLp)).symm

/-! ### The maximum principle in `H₀¹` -/

/-- **Weak maximum principle for a subsolution in `H₀¹`.** With the boundary inequality
`u ≤ 0` supplied by membership of the subsolution in `H₀¹(Ω)`, a subsolution of a
transport-free operator with nonnegative zeroth-order coefficient on a bounded open set is
nonpositive almost everywhere. -/
theorem weak_maximum_principle_H01 (hd : 0 < d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (Op : FullEllipticOp d) (hb : ∀ x i, Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), 0 ≤ Op.c x) (U : H01 Ω)
    (hsub : ∀ V : H01 Ω, (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ ((V : H1amb Ω) 0 x : ℝ)) →
      Op.fullBilin Ω U V ≤ 0) :
    ∀ᵐ x ∂(volume.restrict Ω), ((U : H1amb Ω) 0 x : ℝ) ≤ 0 := by
  obtain ⟨W, hW, hW0, -⟩ := exists_mem_H01_posPart_sub_const hΩopen U.2 (le_refl (0 : ℝ))
  refine weak_maximum_principle hd hΩopen hΩb Op hb hc (H01_le_W12 Ω U.2) (fun V hV => ?_)
    (le_refl (0 : ℝ))
    ⟨⟨W, hW⟩, ?_⟩
  · have := hsub V hV
    rwa [FullEllipticOp.fullBilin_apply, EllipticCoeff.bilin_apply, FullEllipticOp.lowerBilin_apply,
      ← add_assoc] at this
  · filter_upwards [hW0] with x hx
    simpa only [sub_zero] using hx

/-- **Uniqueness of the generalised Dirichlet problem** (Gilbarg and Trudinger Corollary 8.2,
transport-free case). A weak solution in `H₀¹(Ω)` of the homogeneous equation for a
transport-free operator with nonnegative zeroth-order coefficient on a bounded open set is
zero. -/
theorem eq_zero_of_weakSolution_H01 (hd : 0 < d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (Op : FullEllipticOp d) (hb : ∀ x i, Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), 0 ≤ Op.c x) (U : H01 Ω)
    (hsol : ∀ V : H01 Ω, Op.fullBilin Ω U V = 0) : U = 0 := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  -- the function coordinate vanishes, by the principle applied to `U` and to `-U`
  have hle := weak_maximum_principle_H01 hd hΩopen hΩb Op hb hc U fun V _ => (hsol V).le
  have hge := weak_maximum_principle_H01 hd hΩopen hΩb Op hb hc (-U) fun V _ => by
    rw [map_neg, _root_.neg_apply, hsol V, neg_zero]
  have h0 : ((U : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume.restrict Ω] 0 := by
    have hneg : ((-U : H01 Ω) : H1amb Ω) 0 = -((U : H1amb Ω) 0) := rfl
    rw [hneg] at hge
    filter_upwards [hle, hge, Lp.coeFn_neg ((U : H1amb Ω) 0)] with x hx1 hx2 hx3
    rw [hx3, Pi.neg_apply] at hx2
    simp only [Pi.zero_apply]
    linarith
  have hU0 : (U : H1amb Ω) 0 = 0 := by
    apply Lp.ext
    exact h0.trans (Lp.coeFn_zero _ _ _).symm
  -- the gradient coordinates vanish by uniqueness of the weak gradient
  have hwg := hasWeakGradOn_of_mem_W12 (H01_le_W12 Ω U.2)
  have hwg0 : HasWeakGradOn Ω (fun x => ((U : H1amb Ω) 0 x : ℝ)) fun _ _ => (0 : ℝ) :=
    hasWeakGradOn_zero.congr_ae (by
      filter_upwards [h0] with x hx
      simp only [Pi.zero_apply] at hx
      exact hx.symm) fun _ => EventuallyEq.rfl
  have hgrad : ∀ i : Fin d, (U : H1amb Ω) i.succ = 0 := fun i => by
    apply Lp.ext
    have := hasWeakGradOn_unique_ae hΩopen hΩopen.measurableSet
      (fun i => (Lp.memLp ((U : H1amb Ω) i.succ)).integrable one_le_two)
      (fun _ => integrableOn_zero) hwg hwg0 i
    exact this.trans (Lp.coeFn_zero _ _ _).symm
  apply Subtype.ext
  apply PiLp.ext
  intro j
  induction j using Fin.cases with
  | zero => simpa using hU0
  | succ i => simpa using hgrad i

end EllipticPdes.Sobolev
