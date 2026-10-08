/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.Operator
public import EllipticPdes.Embedding.Morrey
public import EllipticPdes.Embedding.WeakGradUnique
public import EllipticPdes.Embedding.DomainSobolev

/-!
# Global approximation by functions smooth up to the boundary

On a bounded domain with `C¹` boundary, a class with an `Lᵖ` weak gradient is the `W^{1,p}(Ω)`
limit of smooth compactly supported functions on the whole space. Evans proves this by shifting
the class into the domain near each boundary point, mollifying, and patching with a partition of
unity, and Guo follows him. The extension operator makes the shift unnecessary: the class
extends to a compactly supported class on `ℝᵈ` with a weak gradient there, the mollifications
of the extension are smooth, compactly supported, and converge to it in `Lᵖ(ℝᵈ)` together with
their gradients, and the extension agrees with the class on `Ω`. Restricting to `Ω` gives the
theorem, with approximants that are restrictions of `C_c^∞(ℝᵈ)` functions, which is a stronger
conclusion than membership of `C^∞` up to the boundary.

The gradient of the approximant is identified with the mollified weak gradient of the
extension by `EllipticPdes.Embedding.partialD_convolution_eq_of_hasWeakGradOn`, and the
mollified weak gradient is read back against the class's own gradient by uniqueness of the weak
gradient on the open set `Ω`.

## Main declarations

* `EllipticPdes.Extension.exists_smooth_tendsto_of_hasWeakGradOn`: the theorem for a class and
  its gradient given as functions.
* `EllipticPdes.Extension.hasWeakGradOn_of_mem_W12`: an element of the graph space `W12 Ω` has
  its gradient coordinates as a weak gradient.
* `EllipticPdes.Extension.exists_smooth_tendsto_of_mem_W12`: the theorem at `p = 2` for the
  graph space, which is density of the smooth functions in `H¹(Ω)`.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.3.3 Theorem 3 (p. 266);
Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.1.3.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn partialD_convolution_eq_of_hasWeakGradOn
  tendsto_eLpNorm_convolution_sub hasWeakGradOn_unique_ae isFiniteMeasure_restrict_of_isBounded)
open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- **The gradient of an extension is the gradient of the class on the domain.** If `(U, G)` has a
weak gradient on the whole space and `U` agrees with `u` on the open set `Ω`, then `G` agrees
with the weak gradient `g` of `u` there. -/
theorem ae_grad_eq_of_extension (hΩopen : IsOpen Ω) {u U : EuclideanSpace ℝ (Fin d) → ℝ}
    {g G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hgi : ∀ k, IntegrableOn (g k) Ω volume)
    (hGi : ∀ k, IntegrableOn (G k) Ω volume) (hwg : HasWeakGradOn Ω u g)
    (hU : HasWeakGradOn Set.univ U G) (hag : ∀ y ∈ Ω, U y = u y) (k : Fin d) :
    G k =ᵐ[volume.restrict Ω] g k := by
  have hue : u =ᵐ[volume.restrict Ω] U :=
    (ae_restrict_iff' hΩopen.measurableSet).mpr (Eventually.of_forall fun y hy => (hag y hy).symm)
  exact hasWeakGradOn_unique_ae hΩopen hΩopen.measurableSet hGi hgi
    ((hU.mono (subset_univ _)).congr_ae hue.symm fun _ => EventuallyEq.rfl) hwg k

/-- **Mollifications converge in `Lᵖ(Ω)` to anything that agrees with the class on `Ω`.** -/
theorem tendsto_eLpNorm_convolution_sub_restrict {p : ℝ} (hp : 1 ≤ p)
    {F f : EuclideanSpace ℝ (Fin d) → ℝ} (hF : MemLp F (ENNReal.ofReal p) volume)
    (hfF : f =ᵐ[volume.restrict Ω] F) {φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d))}
    (hrOut : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hratio : ∀ᶠ n in atTop, (φ n).rOut ≤ 2 * (φ n).rIn) :
    Tendsto (fun n => eLpNorm ((F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) - f)
      (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_eLpNorm_convolution_sub hp hF hrOut hratio) (fun _ => zero_le) fun n => ?_
  calc _ = eLpNorm ((F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) - F)
        (ENNReal.ofReal p) (volume.restrict Ω) :=
        eLpNorm_congr_ae (by filter_upwards [hfF] with x hx; simp [hx])
    _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self

/-- **Global approximation by functions smooth up to the boundary** (Evans §5.3.3 Theorem 3 at
order one, Guo Theorem III.1.3). On a bounded open domain with `C¹` boundary, a class with an
`Lᵖ` weak gradient on the domain, `1 ≤ p < ∞`, is the limit in `W^{1,p}(Ω)` of smooth
compactly supported functions on `ℝᵈ`: the functions converge to the class in `Lᵖ(Ω)` and their
partial derivatives to the components of the weak gradient. -/
theorem exists_smooth_tendsto_of_hasWeakGradOn (hd : 0 < d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) {p : ℝ} (hp : 1 ≤ p)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hmu : MemLp u (ENNReal.ofReal p) (volume.restrict Ω))
    (hmg : ∀ k, MemLp (g k) (ENNReal.ofReal p) (volume.restrict Ω))
    (hwg : HasWeakGradOn Ω u g) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
      Tendsto (fun n => eLpNorm (v n - u) (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) ∧
      ∀ k, Tendsto (fun n => eLpNorm (partialD k (v n) - g k) (ENNReal.ofReal p)
        (volume.restrict Ω)) atTop (𝓝 0) := by
  classical
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  -- an open ball containing the closure of the domain, to put the extension's support in
  obtain ⟨R₀, hR₀⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hsub : closure Ω ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) (R₀ + 1) :=
    (closure_minimal hR₀ isClosed_closedBall).trans (closedBall_subset_ball (by linarith))
  obtain ⟨K₀, hK₀⟩ := exists_extension_subset_bound hd hΩopen hΩb hC1 isOpen_ball hsub
    (p := ENNReal.ofReal p) hp1
  obtain ⟨U, G, hwgU, hUcs, -, hUint, hGint, hag, hUb, hGb⟩ :=
    hK₀ u g (hmu.integrable hp1) (fun k => (hmg k).integrable hp1) hwg
  -- the extension and its gradient are in `Lᵖ(ℝᵈ)`
  set N : ℝ≥0∞ := eLpNorm u (ENNReal.ofReal p) (volume.restrict Ω)
    + ∑ k, eLpNorm (g k) (ENNReal.ofReal p) (volume.restrict Ω) with hNdef
  have hNfin : N < ⊤ := by
    rw [hNdef]
    exact ENNReal.add_lt_top.mpr ⟨hmu.eLpNorm_lt_top,
      ENNReal.sum_lt_top.mpr fun k _ => (hmg k).eLpNorm_lt_top⟩
  have hbnd : (K₀ : ℝ≥0∞) * N < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hNfin
  have hMU : MemLp U (ENNReal.ofReal p) volume := lt_of_le_of_lt hUb hbnd
  have hMG : ∀ k, MemLp (G k) (ENNReal.ofReal p) volume :=
    fun k => lt_of_le_of_lt (hGb k) hbnd
  -- the extension agrees with the class on the domain, and so does its gradient
  have hue : u =ᵐ[volume.restrict Ω] U :=
    (ae_restrict_iff' hΩopen.measurableSet).mpr
      (Eventually.of_forall fun y hy => (hag y hy).symm)
  have hge : ∀ k, g k =ᵐ[volume.restrict Ω] G k := fun k =>
    (ae_grad_eq_of_extension hΩopen (fun k => (hmg k).integrable hp1)
      (fun k => (hGint k).integrableOn) hwg hwgU hag k).symm
  -- the mollifiers
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hL
  let φb : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := mollifier 1 one_pos
  have hφrOut : Tendsto (fun n => (φb n).rOut) atTop (𝓝 0) :=
    tendsto_rOut_mollifier 1 one_pos
  have hφratio : ∀ᶠ n in atTop, (φb n).rOut ≤ 2 * (φb n).rIn :=
    Eventually.of_forall fun n => le_of_eq (by simp [φb, mollifier]; ring)
  set v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => U ⋆[L, volume] (φb n).normed volume with hvdef
  have hUli : LocallyIntegrable U volume := hUint.locallyIntegrable
  have hvsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) := fun n =>
    (φb n).hasCompactSupport_normed.contDiff_convolution_right (L := L) hUli
      (φb n).contDiff_normed
  have hvcs : ∀ n, HasCompactSupport (v n) := fun n =>
    HasCompactSupport.convolution (L := L) hUcs (φb n).hasCompactSupport_normed
  -- the partials of a mollification are the mollified weak gradient
  have hpartial : ∀ (n : ℕ) (k : Fin d),
      partialD k (v n) = (G k ⋆[L, volume] (φb n).normed volume) := by
    intro n k
    funext x
    have h := partialD_convolution_eq_of_hasWeakGradOn MeasurableSet.univ
      hUint.integrableOn hwgU (φb n) k (x := x) (subset_univ _)
    simpa only [indicator_univ] using h
  refine ⟨v, hvsmooth, hvcs, tendsto_eLpNorm_convolution_sub_restrict hp hMU hue hφrOut hφratio,
    fun k => ?_⟩
  simp only [hpartial]
  exact tendsto_eLpNorm_convolution_sub_restrict hp (hMG k) (hge k) hφrOut hφratio

/-! ### The graph space -/

/-- The real inner product of two `L²(Ω)` classes is the integral of their product over `Ω`. -/
theorem inner_L2D_eq_integral (f h : L2D Ω) :
    inner ℝ f h = ∫ x in Ω, f x * h x := by
  rw [L2.real_inner_eq_integral]

/-- **Weak gradient of an element of the graph space.** The constraint defining `W12 Ω`
is integration by parts against every test function, read coordinate by coordinate: the
function coordinate has the gradient coordinates as its weak gradient on `Ω`. -/
theorem hasWeakGradOn_of_mem_W12 {U : H1amb Ω} (hU : U ∈ W12 Ω) :
    HasWeakGradOn Ω (fun x => (U 0 : L2D Ω) x) (fun (k : Fin d) x => (U k.succ : L2D Ω) x) := by
  intro φ hφc hφcs hφB k
  have h : IsTestFn Ω φ := ⟨hφc, hφcs, hφB⟩
  have key := (mem_W12_iff U).mp hU φ h k
  rw [inner_L2D_eq_integral, inner_L2D_eq_integral] at key
  have h1 : ∫ x in Ω, (h.partialCls k : EuclideanSpace ℝ (Fin d) → ℝ) x * (U 0 : L2D Ω) x
      = ∫ x in Ω, (U 0 : L2D Ω) x * partialD k φ x := by
    refine integral_congr_ae ?_
    filter_upwards [(h.memLp_partialD k).coeFn_toLp] with x hx
    simp only [IsTestFn.partialCls] at hx ⊢
    rw [hx, mul_comm]
  have h2 : ∫ x in Ω, (h.testCls : EuclideanSpace ℝ (Fin d) → ℝ) x * (U k.succ : L2D Ω) x
      = ∫ x in Ω, (U k.succ : L2D Ω) x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [h.mem_lp.coeFn_toLp] with x hx
    simp only [IsTestFn.testCls] at hx ⊢
    rw [hx, mul_comm]
  rw [h1, h2] at key
  linarith

/-- **Density of the smooth functions in `H¹(Ω)`** (Evans §5.3.3 Theorem 3 at `k = 1`,
`p = 2`). On a bounded open domain with `C¹` boundary, every element of the graph space
`W12 Ω` is the `H¹(Ω)` limit of smooth compactly supported functions on `ℝᵈ`: the functions
converge to its function coordinate in `L²(Ω)`, and their partial derivatives to its gradient
coordinates. -/
theorem exists_smooth_tendsto_of_mem_W12 (hd : 0 < d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) {U : H1amb Ω} (hU : U ∈ W12 Ω) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
      Tendsto (fun n => eLpNorm (v n - fun x => (U 0 : L2D Ω) x) 2 (volume.restrict Ω))
        atTop (𝓝 0) ∧
      ∀ k : Fin d, Tendsto (fun n => eLpNorm (partialD k (v n) - fun x => (U k.succ : L2D Ω) x) 2
        (volume.restrict Ω)) atTop (𝓝 0) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hmu : MemLp (fun x => (U 0 : L2D Ω) x) (ENNReal.ofReal 2) (volume.restrict Ω) := by
    rw [h2]; exact Lp.memLp (U 0)
  have hmg : ∀ k : Fin d, MemLp (fun x => (U k.succ : L2D Ω) x) (ENNReal.ofReal 2)
      (volume.restrict Ω) := fun k => by
    rw [h2]; exact Lp.memLp (U k.succ)
  obtain ⟨v, hvs, hvcs, hv0, hvk⟩ := exists_smooth_tendsto_of_hasWeakGradOn hd hΩopen hΩb hC1
    (p := 2) one_le_two hmu hmg (hasWeakGradOn_of_mem_W12 hU)
  rw [h2] at hv0 hvk
  exact ⟨v, hvs, hvcs, hv0, hvk⟩

end EllipticPdes.Extension
