/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.CoeffLip
public import EllipticPdes.Regularity.Interior.Support
public import EllipticPdes.Regularity.CoeffBridge

/-!
# Master interior difference-quotient energy estimate

The interior second-derivative estimate (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8) proceeds by testing
the weak formulation of `L u = f` with the difference-quotient test element
`v_h = -Dₖ^{-h}(ξ² Dₖ^h u)`, using discrete integration by parts to move the outer difference
quotient onto the coefficient factor, uniform ellipticity from below to control the leading
term, and Cauchy-Schwarz together with the Peter-Paul (Young) inequality to absorb the
commutator, cross, zeroth-order, and right-hand terms.

## Main declarations

* `evansTest`: the admissible test element `v_h = -Dₖ^{-h}(ξ² Dₖ^h u) ∈ H₀¹(Ω)`, whose
  membership is two applications of `cutoffMul_diffQuotG_mem_H01`.
* `hasWeakDeriv_extendL2_of_mem_H01`: extension by zero of an `H₀¹(Ω)` element has the extension
  of its gradient as weak gradient.
* `firstOrder_energy_le`: the first-order energy estimate.
* `norm_diffQuotD_le_grad`: `‖Dₖ^h u₀‖ ≤ ‖∂ₖu‖`.
* `interior_diffQuot_energy_bound`: the master energy estimate.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
  {ξ θ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### Admissible Evans test element -/

/-- **Admissible Evans test element** `v_h = -Dₖ^{-h}(ξ² Dₖ^h u) ∈ H₀¹(Ω)`. The inner
cutoff `ξ²` and the outer cutoff `θ` (which is `≡ 1` on `tsupport ξ`) localise the two
difference quotients so that the composite stays inside `H₀¹(Ω)`; membership is two
applications of the crux admissibility lemma `cutoffMul_diffQuotG_mem_H01`, together with
closure of the submodule under negation. -/
noncomputable def evansTest (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    {k : Fin d} {h : ℝ} (hS : ShiftAdmissible Ω ξ θ k h) (u : H01 Ω) : H01 Ω :=
  ⟨-(cutoffMul hθ (diffQuotG k (-h) hΩm
      (cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))))),
    Submodule.neg_mem _
      (cutoffMul_diffQuotG_mem_H01 hθ k hΩm hS.shift_out
        (cutoffMul_diffQuotG_mem_H01 (isTestFn_mul hξ hξ) k hΩm hS.shift_in u.2))⟩

/-- The ambient-graph value of `evansTest` is the negated cutoff of the outer difference
quotient of `ξ² Dₖ^h u`. -/
theorem evansTest_coe (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    {k : Fin d} {h : ℝ} (hS : ShiftAdmissible Ω ξ θ k h) (u : H01 Ω) :
    (evansTest hΩm hξ hθ hS u : H1amb Ω)
      = -(cutoffMul hθ (diffQuotG k (-h) hΩm
          (cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))))) :=
  rfl

/-! ### Support control and θ-invisibility -/

/-- **Support of the interior difference quotient.** If a class `g` has whole-space extension
a.e. supported in a measurable set `S`, then its interior difference quotient `diffQuotD k h g`
vanishes (a.e. on `Ω`) outside `S ∪ (S - h eₖ)`: the numerator
`extendL2 g (x + h eₖ) - g x` can be nonzero only when `x ∈ S` (through `g x`) or
`x + h eₖ ∈ S` (through the translate). -/
private lemma diffQuotD_ae_eq_zero_off (hΩm : MeasurableSet Ω) (k : Fin d) {h : ℝ}
    (g : L2D Ω) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hgS : ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S) :
    ∀ᵐ x ∂(volume.restrict Ω),
      x ∉ S → x + hshift k h ∉ S → (diffQuotD k h hΩm g x : ℝ) = 0 := by
  have hqmp : MeasureTheory.QuasiMeasurePreserving (· + hshift k h) volume volume :=
    (measurePreserving_add_right volume (hshift k h)).quasiMeasurePreserving
  have hgS_shift : ∀ᵐ x ∂volume,
      (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h) ≠ 0 →
        x + hshift k h ∈ S := hqmp.ae hgS
  filter_upwards [coeFn_diffQuotD k h hΩm g, ae_restrict_of_ae hgS,
    ae_restrict_of_ae hgS_shift, ae_restrict_of_ae (coeFn_extendL2 hΩm g),
    ae_restrict_mem hΩm] with x hdq hgx hgxs hext hmem hxS hxsS
  rw [hdq]
  have h1 : (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h) = 0 := by
    by_contra hne; exact hxsS (hgxs hne)
  have h2 : (g x : ℝ) = 0 := by
    by_contra hne
    refine hxS (hgx ?_)
    rw [hext, Set.indicator_of_mem hmem]; exact hne
  rw [h1, h2, sub_zero, zero_div]

/-- **θ-chop invisibility.** If `g`'s extension is a.e. supported in `S` and the outer cutoff
`θ ≡ 1` on the part of `Ω` reachable into `S` by the shift, then multiplying `θ` onto the
interior difference quotient of `g` is invisible: `θ · Dₖʰ g = Dₖʰ g`. This is what lets the
outer cutoff of the Evans test element drop out of the energy identity (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1). -/
private lemma mulTest_theta_diffQuotD (hΩm : MeasurableSet Ω) (hθ : IsTestFn Ω θ)
    (k : Fin d) {h : ℝ} (g : L2D Ω) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hgS : ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S)
    (hθ1 : ∀ x ∈ Ω, x ∈ S ∨ x + hshift k h ∈ S → θ x = 1) :
    mulTest hθ (diffQuotD k h hΩm g) = diffQuotD k h hΩm g := by
  apply Lp.ext
  filter_upwards [mulCutoff_coeFn hθ (diffQuotD k h hΩm g),
    diffQuotD_ae_eq_zero_off hΩm k g hgS, ae_restrict_mem hΩm] with x hmt hzero hmem
  rw [hmt]
  by_cases hd : (diffQuotD k h hΩm g x : ℝ) = 0
  · rw [hd, mul_zero]
  · have hmemS : x ∈ S ∨ x + hshift k h ∈ S := by
      by_contra hc; exact hd (hzero (not_or.mp hc).1 (not_or.mp hc).2)
    rw [hθ1 x hmem hmemS, one_mul]

/-- **θ-cross-term vanishing.** Under the same support and `θ ≡ 1` conditions (so that
`∂ⱼθ = 0` on the reachable part of `Ω`), the partial-cutoff multiplier annihilates the
interior difference quotient: `(∂ⱼθ) · Dₖʰ g = 0`. This kills the outer-cutoff cross term of
the Evans test element, which would otherwise be a second-order (double difference-quotient)
object beyond the reach of the data bound (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1). -/
private lemma mulTestPartial_theta_diffQuotD (hΩm : MeasurableSet Ω) (hθ : IsTestFn Ω θ)
    (j k : Fin d) {h : ℝ} (g : L2D Ω) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hgS : ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S)
    (hθ0 : ∀ x ∈ Ω, x ∈ S ∨ x + hshift k h ∈ S → partialD j θ x = 0) :
    mulTestPartial hθ j (diffQuotD k h hΩm g) = 0 := by
  apply Lp.ext
  filter_upwards [mulCutoffPartial_coeFn hθ j (diffQuotD k h hΩm g),
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict Ω),
    diffQuotD_ae_eq_zero_off hΩm k g hgS, ae_restrict_mem hΩm] with x hmtp hz hzero hmem
  rw [hmtp, hz, Pi.zero_apply]
  by_cases hd : (diffQuotD k h hΩm g x : ℝ) = 0
  · rw [hd, mul_zero]
  · have hmemS : x ∈ S ∨ x + hshift k h ∈ S := by
      by_contra hc; exact hd (hzero (not_or.mp hc).1 (not_or.mp hc).2)
    rw [hθ0 x hmem hmemS, zero_mul]

/-! ### Discrete integration by parts -/

/-- **Discrete integration by parts on the principal term.** For a class `p` whose whole-space
extension stays supported inside `Ω` after the backward shift, the restricted-domain pairing
of the coefficient action against the backward interior difference quotient of `p` transfers,
via the extension isometry and the whole-space adjoint relation `diffQuot_inner_adjoint`,
into minus the whole-space pairing of the *forward* difference quotient of the coefficient
action against `extendL2 p`. This is the discrete analogue of moving the derivative off the
test factor onto the coefficient factor (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1, proof of Theorem 1). -/
private lemma actL_diffQuotD_ibp (A : EllipticCoeff d) (hΩm : MeasurableSet Ω)
    (i j k : Fin d) {h : ℝ} (g p : L2D Ω)
    (hsupp : ∀ᵐ x ∂volume,
      (extendL2 hΩm p : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k (-h)) ≠ 0 → x ∈ Ω) :
    ⟪A.actL i j g, diffQuotD k (-h) hΩm p⟫
      = -⟪diffQuot k h (extendL2 hΩm (A.actL i j g)), extendL2 hΩm p⟫ := by
  rw [← (extendL2 hΩm).inner_map_map (A.actL i j g) (diffQuotD k (-h) hΩm p),
    extendL2_diffQuotD_eq k (-h) hΩm p hsupp,
    diffQuot_inner_adjoint k h (extendL2 hΩm (A.actL i j g)) (extendL2 hΩm p)]
  exact (neg_neg _).symm

/-! ### Support of the inner cutoff data and the Evans coordinate reduction -/

/-- **Support of the inner cutoff data.** Every ambient coordinate of the inner block `ξ² · Dₖ^h
u` has whole-space extension a.e. supported in `tsupport ξ²`: the zeroth coordinate is `ξ² ·
Dₖ^h u₀`, and the `i+1` coordinate is `ξ² · Dₖ^h ∂ᵢu + (∂ᵢξ²) · Dₖ^h u₀`, both of which have the
factor `ξ²` (or its partial, whose support is smaller). -/
private lemma diffQuotG_cutoffSq_supp (hξ : IsTestFn Ω ξ) (hΩm : MeasurableSet Ω)
    (k : Fin d) (h : ℝ) (u : H1amb Ω) (j : Fin (d + 1)) :
    ∀ᵐ x ∂volume,
      (extendL2 hΩm ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm u)) j)
          : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0
        → x ∈ tsupport (fun y => ξ y * ξ y) := by
  apply extendL2_supp_of_ae_restrict
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [cutoffMulOn_apply_zero, diffQuotG_apply]
    exact mulTest_ae_eq_zero_off_tsupport (isTestFn_mul hξ hξ) _
  · rw [cutoffMulOn_apply_succ, diffQuotG_apply, diffQuotG_apply]
    filter_upwards [Lp.coeFn_add
        (mulTest (isTestFn_mul hξ hξ) (diffQuotD k h hΩm (u i.succ)))
        (mulTestPartial (isTestFn_mul hξ hξ) i (diffQuotD k h hΩm (u 0))),
      mulCutoff_coeFn (isTestFn_mul hξ hξ) (diffQuotD k h hΩm (u i.succ)),
      mulCutoffPartial_coeFn (isTestFn_mul hξ hξ) i (diffQuotD k h hΩm (u 0))]
      with x hadd hmt hmtp hxS
    have hsq : ξ x * ξ x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => ξ y * ξ y) hxS
    have hpsq : partialD i (fun y => ξ y * ξ y) x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := partialD i (fun y => ξ y * ξ y))
        (fun hc => hxS (tsupport_partialD_subset i _ hc))
    rw [hadd, Pi.add_apply, hmt, hmtp, hsq, hpsq, zero_mul, zero_mul, add_zero]

/-- **Evans test element at the successor coordinate.** Under the outer-cutoff reachability
conditions, the `j+1` coordinate of the admissible test element reduces to a single backward
difference quotient of the inner block: `(v_h)_{j+1} = -Dₖ^{-h}((ξ²·Dₖ^h u)_{j+1})`. This is the
θ-chop invisibility together with the vanishing of the outer-cutoff cross term. -/
private lemma evansTest_succ_eq (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    {k : Fin d} {h : ℝ} (hS : ShiftAdmissible Ω ξ θ k h) (u : H01 Ω) (j : Fin d) :
    (evansTest hΩm hξ hθ hS u : H1amb Ω) j.succ
      = -diffQuotD k (-h) hΩm
          ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) j.succ) := by
  set Z : H1amb Ω := cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω)) with hZ
  have hcoe : (evansTest hΩm hξ hθ hS u : H1amb Ω) j.succ
      = -(cutoffMul hθ (diffQuotG k (-h) hΩm Z)) j.succ := by
    rw [evansTest_coe]; rfl
  rw [hcoe, cutoffMulOn_apply_succ, diffQuotG_apply, diffQuotG_apply,
    mulTest_theta_diffQuotD hΩm hθ k (Z j.succ)
      (diffQuotG_cutoffSq_supp hξ hΩm k h (u : H1amb Ω) j.succ) hS.theta_one,
    mulTestPartial_theta_diffQuotD hΩm hθ j k (Z 0)
      (diffQuotG_cutoffSq_supp hξ hΩm k h (u : H1amb Ω) 0) (hS.dtheta_zero j), add_zero]

/-- **Evans test element at the zeroth coordinate.** The function value of the test element is a
single backward difference quotient of the inner block, `(v_h)₀ = -Dₖ^{-h}((ξ²·Dₖ^h u)₀)`,
by θ-chop invisibility. -/
private lemma evansTest_zero_eq (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    {k : Fin d} {h : ℝ} (hS : ShiftAdmissible Ω ξ θ k h) (u : H01 Ω) :
    (evansTest hΩm hξ hθ hS u : H1amb Ω) 0
      = -diffQuotD k (-h) hΩm
          ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) 0) := by
  set Z : H1amb Ω := cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω)) with hZ
  have hcoe : (evansTest hΩm hξ hθ hS u : H1amb Ω) 0
      = -(cutoffMul hθ (diffQuotG k (-h) hΩm Z)) 0 := by rw [evansTest_coe]; rfl
  rw [hcoe, cutoffMulOn_apply_zero, diffQuotG_apply,
    mulTest_theta_diffQuotD hΩm hθ k (Z 0)
      (diffQuotG_cutoffSq_supp hξ hΩm k h (u : H1amb Ω) 0) hS.theta_one]

/-- **Evans bilinear identity in restricted-domain form.** Testing the principal bilinear form
with the Evans element, the coordinate reduction `evansTest_succ_eq` followed by discrete
integration by parts (`actL_diffQuotD_ibp`) moves the backward difference quotient off the test
factor onto the coefficient action: the principal form is the restricted-domain pairing of the
inner cutoff block against the interior difference quotient of the coefficient action. -/
private lemma evansTest_bilin_L2D (A : EllipticCoeff d) (hΩm : MeasurableSet Ω)
    (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ) {k : Fin d} {h : ℝ}
    (hS : ShiftAdmissible Ω ξ θ k h) (u : H01 Ω) :
    A.bilin Ω u (evansTest hΩm hξ hθ hS u)
      = ∑ i : Fin d, ∑ j : Fin d,
        ⟪(cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) j.succ,
          diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ))⟫ := by
  rw [EllipticCoeff.bilin_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  set Z : H1amb Ω := cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω)) with hZ
  have hsupp : ∀ᵐ x ∂volume,
      (extendL2 hΩm (Z j.succ) : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k (-h)) ≠ 0
        → x ∈ Ω := by
    have hqmp : MeasureTheory.QuasiMeasurePreserving
        (· + hshift k (-h)) volume volume :=
      (measurePreserving_add_right volume (hshift k (-h))).quasiMeasurePreserving
    filter_upwards [hqmp.ae (diffQuotG_cutoffSq_supp hξ hΩm k h (u : H1amb Ω) j.succ)]
      with x hx hne
    have hxeq : x = (x + hshift k (-h)) + hshift k h := by rw [hshift_neg]; abel
    rw [hxeq]; exact hS.shift_in _ (hx hne)
  rw [evansTest_succ_eq hΩm hξ hθ hS u j, inner_neg_right,
    actL_diffQuotD_ibp A hΩm i j k ((u : H1amb Ω) i.succ) (Z j.succ) hsupp, neg_neg,
    real_inner_comm, extendL2_inner_restrictL2, ← restrictL2_diffQuot_extendL2]

/-! ### Extension-by-zero weak derivative and the first-order global energy -/

/-- **Extension by zero of an `H₀¹` element preserves the weak gradient.** For `u ∈ H₀¹(Ω)`, the
whole-space extension by zero of the function value `u₀` has whole-space `L²` weak
`k`-derivative equal to the extension by zero of the gradient component `u_{k+1}`. Because `u`
vanishes at the boundary (it lies in the closure of the compactly supported test functions), no
boundary term appears when integrating against an arbitrary whole-space test function `φ`: the
identity `∫ (extendL2 u₀) ∂ₖφ = -∫ (extendL2 u_{k+1}) φ` is closed under `L²` limits and holds
on every test-function graph by classical integration by parts, hence on all of `H₀¹(Ω)` (Evans,
*Partial Differential Equations* (2nd ed.), §5.8.2). -/
theorem hasWeakDeriv_extendL2_of_mem_H01 (hΩm : MeasurableSet Ω) (k : Fin d)
    {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    HasWeakDeriv k (extendL2 hΩm (U 0)) (extendL2 hΩm (U k.succ)) := by
  intro φ hφcd hφcs
  have hφL2 : MemLp φ 2 volume := hφcd.continuous.memLp_of_hasCompactSupport hφcs
  have hφpL2 : MemLp (partialD k φ) 2 volume :=
    (contDiff_partialD hφcd k).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_partialD hφcs k)
  set a : EucL2 d := hφpL2.toLp (partialD k φ) with ha
  set b : EucL2 d := hφL2.toLp φ with hb
  set w₀ : H1amb Ω := PiLp.single 2 (0 : Fin (d + 1)) (restrictL2 a)
      + PiLp.single 2 k.succ (restrictL2 b) with hw₀
  -- The inner product against `w₀` extracts the two extension-by-zero pairings.
  have hΦ : ∀ V : H1amb Ω, ⟪w₀, V⟫
      = ⟪extendL2 hΩm (V 0), a⟫ + ⟪extendL2 hΩm (V k.succ), b⟫ := by
    intro V
    rw [extendL2_inner_restrictL2 hΩm (V 0) a, extendL2_inner_restrictL2 hΩm (V k.succ) b,
      hw₀, inner_add_left, inner_single_left, inner_single_left]
    congr 1 <;> exact real_inner_comm _ _
  -- On a test-function graph `w₀` is orthogonal: classical integration by parts.
  have hbase : ∀ V ∈ testGraphSet Ω, ⟪w₀, V⟫ = 0 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    have hI0 : ⟪extendL2 hΩm hψ.testCls, a⟫ = ∫ x, ψ x * partialD k φ x :=
      inner_Lp_eq_integral_of_ae (coeFn_extendL2_of_ae_restrict hΩm _ hψ.mem_lp.coeFn_toLp
        fun x hx => image_eq_zero_of_notMem_tsupport (fun hc => hx (hψ.2.2 hc)))
        hφpL2.coeFn_toLp
    have hIk : ⟪extendL2 hΩm (hψ.partialCls k), b⟫ = ∫ x, partialD k ψ x * φ x :=
      inner_Lp_eq_integral_of_ae (coeFn_extendL2_of_ae_restrict hΩm _
        (hψ.memLp_partialD k).coeFn_toLp fun x hx => image_eq_zero_of_notMem_tsupport
          (fun hc => hx (hψ.2.2 (tsupport_partialD_subset k ψ hc)))) hφL2.coeFn_toLp
    have hIBP := hasWeakPartial_partialD (hψ.1.of_le (by exact_mod_cast le_top)) k φ hφcd hφcs
    rw [hΦ, IsTestFn.testGraph_zero, IsTestFn.testGraph_succ, hI0, hIk]
    linarith only [hIBP]
  -- `w₀` is orthogonal to the span, hence to its closure `H₀¹(Ω)`.
  have hUperp : U ∈ (Submodule.span ℝ {w₀})ᗮ := by
    have hle : Submodule.span ℝ (testGraphSet Ω) ≤ (Submodule.span ℝ {w₀})ᗮ := by
      rw [Submodule.span_le]
      intro V hV
      rw [SetLike.mem_coe, Submodule.mem_orthogonal]
      intro u hu
      rw [Submodule.mem_span_singleton] at hu
      obtain ⟨c, rfl⟩ := hu
      rw [inner_smul_left, hbase V hV, mul_zero]
    exact (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure_minimal hle
      (Submodule.isClosed_orthogonal _) hU
  rw [Submodule.mem_orthogonal] at hUperp
  have hzero := hUperp w₀ (Submodule.mem_span_singleton_self w₀)
  rw [hΦ, inner_Lp_eq_integral_of_ae Filter.EventuallyEq.rfl hφpL2.coeFn_toLp,
    inner_Lp_eq_integral_of_ae Filter.EventuallyEq.rfl hφL2.coeFn_toLp] at hzero
  linarith only [hzero]

/-- **First-order global energy estimate.** For a weak solution `u ∈ H₀¹(Ω)` of
`L u = f`, the full gradient energy is bounded by the data:
`(λ/2) ∑ᵢ ‖u_{i+1}‖² ≤ ‖f‖ · ‖u₀‖ + γ ‖u₀‖²`, where `γ` is the Gårding shift. Testing the weak
formulation with `u` itself, Gårding's inequality bounds the form from below, and only the
right-hand pairing `⟪f, u₀⟫` survives (Evans, *Partial Differential Equations* (2nd ed.),
§6.2.2). -/
theorem firstOrder_energy_le (Op : FullEllipticOp d) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ v : H01 Ω, Op.fullBilin Ω u v
      = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) :
    Op.lam / 2 * ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2
      ≤ ‖f‖ * ‖(u : H1amb Ω) 0‖ + Op.gardingγ * ‖(u : H1amb Ω) 0‖ ^ 2 := by
  have hg := Op.garding Ω u
  have hnorm : ‖u‖ ^ 2
      = ‖(u : H1amb Ω) 0‖ ^ 2 + ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 := by
    rw [show ‖u‖ = ‖(u : H1amb Ω)‖ from rfl, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  have hfu : Op.fullBilin Ω u u ≤ ‖f‖ * ‖(u : H1amb Ω) 0‖ := by
    rw [hu u, ← inner_eq_setIntegral]; exact real_inner_le_norm _ _
  have hdrop : (0 : ℝ) ≤ Op.lam / 2 * ‖(u : H1amb Ω) 0‖ ^ 2 :=
    mul_nonneg (by have := Op.lam_pos; linarith) (sq_nonneg _)
  rw [hnorm] at hg
  nlinarith only [hg, hfu, hdrop]

/-- **Gradient control of the difference quotient of `u₀`.** For `u ∈ H₀¹(Ω)`,
the interior difference quotient of the function value is bounded in `L²` by the `k`-th
gradient component, uniformly in the step `h`: `‖Dₖ^h u₀‖ ≤ ‖u_{k+1}‖`. This composes the
weak-derivative difference-quotient bound `norm_diffQuot_le_of_hasWeakDeriv` with the
extension-by-zero weak gradient `hasWeakDeriv_extendL2_of_mem_H01`, through the non-expansive
restriction (Evans, *Partial Differential Equations* (2nd ed.), §5.8.2). -/
theorem norm_diffQuotD_le_grad (hΩm : MeasurableSet Ω) (k : Fin d) (u : H01 Ω) (h : ℝ) :
    ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖ ≤ ‖(u : H1amb Ω) k.succ‖ := by
  rw [← restrictL2_diffQuot_extendL2]
  refine (norm_restrictL2_le _).trans ?_
  rw [← norm_extendL2 hΩm ((u : H1amb Ω) k.succ)]
  exact norm_diffQuot_le_of_hasWeakDeriv k _ _ (hasWeakDeriv_extendL2_of_mem_H01 hΩm k u.2) h

/-- **`L²(Ω)` norm bound on the coefficient difference-quotient commutator.** The interior
difference quotient of a coefficient-multiplied field splits into the translated coefficient
acting on the field's difference quotient plus a commutator whose `L²(Ω)` norm is controlled
by the Lipschitz constant `A₁`: `‖Dₖʰ(aᵢⱼ g) − (τ_{h eₖ}aᵢⱼ) Dₖʰ g‖ ≤ A₁ ‖g‖`. This is the
discrete Leibniz split `coeFn_diffQuot_mul_coeff` measured at the restricted-domain level,
its commutator coefficient bounded pointwise by `IsLipCoeff.abs_diffQuot_coeff_le` (Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma norm_diffQuotD_actL_sub_le {A : EllipticCoeff d} (hA : IsLipCoeff A)
    (hΩm : MeasurableSet Ω) (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) (g : L2D Ω) :
    ‖diffQuotD k h hΩm (A.actL i j g)
        - (A.translate (hshift k h)).actL i j (diffQuotD k h hΩm g)‖ ≤ hA.A1 * ‖g‖ := by
  have hqmp : MeasureTheory.QuasiMeasurePreserving (· + hshift k h) volume volume :=
    (measurePreserving_add_right volume (hshift k h)).quasiMeasurePreserving
  set cf : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun x => (A.a (x + hshift k h) i j - A.a x i j) / h with hcf
  have hmeas : Measurable cf :=
    (((A.measurable i j).comp (measurable_add_const _)).sub (A.measurable i j)).div_const h
  have hbdd : ∀ᵐ x ∂(volume.restrict Ω), |cf x| ≤ hA.A1 :=
    ae_of_all _ (fun x => hA.abs_diffQuot_coeff_le i j k hh x)
  have hkey : diffQuotD k h hΩm (A.actL i j g)
        - (A.translate (hshift k h)).actL i j (diffQuotD k h hΩm g)
      = mulCoeffL hmeas hbdd g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (diffQuotD k h hΩm (A.actL i j g))
        ((A.translate (hshift k h)).actL i j (diffQuotD k h hΩm g)),
      coeFn_diffQuotD k h hΩm (A.actL i j g),
      (A.translate (hshift k h)).actL_coeFn i j (diffQuotD k h hΩm g),
      coeFn_diffQuotD k h hΩm g, mulCoeffL_coeFn hmeas hbdd g,
      ae_restrict_of_ae (hqmp.ae (extendL2_actL hΩm A i j g)),
      A.actL_coeFn i j g] with x hsub hdq1 hact' hdq0 hmul hsha hact0
    rw [hsub, Pi.sub_apply, hdq1, hact', EllipticCoeff.translate_a, hdq0, hmul, hact0, hsha]
    simp only [hcf]
    field_simp
    ring
  rw [hkey]; exact norm_mulCoeffL_le hmeas hbdd g

/-! ### Norm bounds for the master estimate -/

/-- Multiplying by `ξ²` is multiplying by `ξ` twice: `[ξ² · g] = [ξ · (ξ · g)]`. -/
private lemma mulTest_mul_eq (hξ : IsTestFn Ω ξ) (g : L2D Ω) :
    mulTest (isTestFn_mul hξ hξ) g = mulTest hξ (mulTest hξ g) := by
  apply Lp.ext
  filter_upwards [mulCutoff_coeFn (isTestFn_mul hξ hξ) g,
    mulCutoff_coeFn hξ (mulTest hξ g), mulCutoff_coeFn hξ g] with x h1 h2 h3
  rw [h1, h2, h3]; ring

/-- **Norm of a coordinate of the inner block.** The `j`-th gradient coordinate `ξ² g + ∂ⱼ(ξ²) p`
of the cutoff block is bounded by `‖ξ‖∞ ‖ξ g‖ + ‖∂ⱼ(ξ²)‖∞ ‖p‖`. -/
private lemma norm_cutoffSq_block_le (hξ : IsTestFn Ω ξ) (j : Fin d) (g p : L2D Ω) :
    ‖mulTest (isTestFn_mul hξ hξ) g + mulTestPartial (isTestFn_mul hξ hξ) j p‖
      ≤ hξ.supNorm * ‖mulTest hξ g‖
        + (isTestFn_mul hξ hξ).partialSupNorm j * ‖p‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mulTestPartial_le_supNorm _ _ _))
  rw [mulTest_mul_eq hξ g]; exact norm_mulTest_le_supNorm hξ _

/-- **Function value of the Evans element.** `‖(v_h)₀‖ ≤ ‖ξ‖∞ ‖ξ Dₖ^h ∂ₖu‖
+ ‖∂ₖ(ξ²)‖∞ ‖Dₖ^h u₀‖`: the function value is a backward difference quotient of the inner
block, which the weak-gradient bound `norm_diffQuotD_le_grad` controls by the `k`-th gradient
coordinate of the block. -/
private lemma norm_evansTest_zero_le (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ)
    (hθ : IsTestFn Ω θ) {k : Fin d} {h : ℝ} (hS : ShiftAdmissible Ω ξ θ k h) (u : H01 Ω) :
    ‖(evansTest hΩm hξ hθ hS u : H1amb Ω) 0‖
      ≤ hξ.supNorm * ‖mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) k.succ))‖
        + (isTestFn_mul hξ hξ).partialSupNorm k * ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖ := by
  rw [evansTest_zero_eq hΩm hξ hθ hS u, norm_neg]
  refine (norm_diffQuotD_le_grad hΩm k
    ⟨_, cutoffMul_diffQuotG_mem_H01 (isTestFn_mul hξ hξ) k hΩm hS.shift_in u.2⟩ (-h)).trans ?_
  change ‖(cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) k.succ‖ ≤ _
  rw [cutoffMulOn_apply_succ, diffQuotG_apply, diffQuotG_apply]
  exact norm_cutoffSq_block_le hξ k _ _

/-! ### The commutator term and the energy identity -/

/-- The `i`-th interior difference quotient `Dₖʰ ∂ᵢu` of the gradient. -/
private abbrev evansDg (hΩm : MeasurableSet Ω) (k : Fin d) (h : ℝ) (u : H01 Ω) (i : Fin d) :
    L2D Ω :=
  diffQuotD k h hΩm ((u : H1amb Ω) i.succ)

/-- The interior difference quotient `Dₖʰ u₀` of the function value. -/
private abbrev evansD0 (hΩm : MeasurableSet Ω) (k : Fin d) (h : ℝ) (u : H01 Ω) : L2D Ω :=
  diffQuotD k h hΩm ((u : H1amb Ω) 0)

/-- The coefficient commutator `Dₖʰ(aᵢⱼ ∂ᵢu) - aᵢⱼ(· + h eₖ) Dₖʰ ∂ᵢu`. -/
private abbrev evansComm (A : EllipticCoeff d) (hΩm : MeasurableSet Ω) (k : Fin d) (h : ℝ)
    (u : H01 Ω) (i j : Fin d) : L2D Ω :=
  diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ))
    - (A.translate (hshift k h)).actL i j (evansDg hΩm k h u i)

/-- The commutator term `∑ᵢⱼ ⟪ξ² pⱼ + ∂ⱼ(ξ²) q, sᵢⱼ⟫` of the Evans identity. -/
private def evansRest (hξ : IsTestFn Ω ξ) (p : Fin d → L2D Ω) (q : L2D Ω)
    (s : Fin d → Fin d → L2D Ω) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    ⟪mulTest (isTestFn_mul hξ hξ) (p j) + mulTestPartial (isTestFn_mul hξ hξ) j q, s i j⟫

/-- The commutator term is bounded by `c (∑ᵢ gᵢ) (‖ξ‖∞ ∑ⱼ ‖ξ pⱼ‖ + (∑ⱼ ‖∂ⱼ(ξ²)‖∞) ‖q‖)` when
`‖sᵢⱼ‖ ≤ c gᵢ`. -/
private lemma neg_evansRest_le (hξ : IsTestFn Ω ξ) (p : Fin d → L2D Ω) (q : L2D Ω)
    (s : Fin d → Fin d → L2D Ω) {c : ℝ} (g : Fin d → ℝ)
    (hs : ∀ i j, ‖s i j‖ ≤ c * g i) :
    -evansRest hξ p q s ≤ c * (∑ i : Fin d, g i)
      * (hξ.supNorm * ∑ j : Fin d, ‖mulTest hξ (p j)‖
        + (∑ j : Fin d, (isTestFn_mul hξ hξ).partialSupNorm j) * ‖q‖) := by
  calc -evansRest hξ p q s
      = ∑ i : Fin d, ∑ j : Fin d,
          -⟪mulTest (isTestFn_mul hξ hξ) (p j) + mulTestPartial (isTestFn_mul hξ hξ) j q,
            s i j⟫ := by
        simp only [evansRest, Finset.sum_neg_distrib]
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, (c * g i) * (hξ.supNorm * ‖mulTest hξ (p j)‖
          + (isTestFn_mul hξ hξ).partialSupNorm j * ‖q‖) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        refine (neg_real_inner_le_mul_norm _ _).trans ?_
        rw [mul_comm (c * g i)]
        exact mul_le_mul (norm_cutoffSq_block_le hξ j (p j) q) (hs i j) (norm_nonneg _)
          (add_nonneg (mul_nonneg hξ.supNorm_nonneg (norm_nonneg _))
            (mul_nonneg ((isTestFn_mul hξ hξ).partialSupNorm_nonneg j) (norm_nonneg _)))
    _ = (∑ i : Fin d, c * g i) * ∑ j : Fin d, (hξ.supNorm * ‖mulTest hξ (p j)‖
          + (isTestFn_mul hξ hξ).partialSupNorm j * ‖q‖) := (Finset.sum_mul_sum ..).symm
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- **Energy identity for the Evans element.** Testing the weak formulation with
`v_h = -Dₖ^{-h}(ξ² Dₖ^h u)`, moving the outer difference quotient onto the coefficient by
discrete integration by parts, splitting `Dₖʰ(aᵢⱼ ∂ᵢu)` into the translated coefficient acting on
`Dₖʰ ∂ᵢu` plus a commutator, and bounding the translated principal part from below by
ellipticity gives
`λ ∑ᵢ ‖ξ Dₖʰ ∂ᵢu‖² ≤ ⟪f, v₀⟫ - ∑ᵢ ⟪bᵢ ∂ᵢu, v₀⟫ - ⟪c u₀, v₀⟫ - CROSS - REST`. -/
private lemma evans_lower_bound (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω)
    (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ) {k : Fin d} {h : ℝ}
    (hS : ShiftAdmissible Ω ξ θ k h) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) :
    Op.lam * ∑ i : Fin d, ‖mulTest hξ (evansDg hΩm k h u i)‖ ^ 2
      ≤ ⟪f, (evansTest hΩm hξ hθ hS u : H1amb Ω) 0⟫
        - ∑ i : Fin d, ⟪Op.bAct i ((u : H1amb Ω) i.succ),
            (evansTest hΩm hξ hθ hS u : H1amb Ω) 0⟫
        - ⟪Op.cAct ((u : H1amb Ω) 0), (evansTest hΩm hξ hθ hS u : H1amb Ω) 0⟫
        - ∑ i : Fin d, ∑ j : Fin d, 2 * ⟪(Op.toEllipticCoeff.translate (hshift k h)).actL i j
            (mulTest hξ (evansDg hΩm k h u i)), mulTestPartial hξ j (evansD0 hΩm k h u)⟫
        - evansRest hξ (evansDg hΩm k h u) (evansD0 hΩm k h u)
            (evansComm Op.toEllipticCoeff hΩm k h u) := by
  classical
  set A := Op.toEllipticCoeff with hAdef
  set A' := A.translate (hshift k h) with hA'def
  set v : H01 Ω := evansTest hΩm hξ hθ hS u with hvdef
  have hLE : Op.lam * ∑ i : Fin d, ‖mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) i.succ))‖ ^ 2
      ≤ ∑ i : Fin d, ∑ j : Fin d,
          ⟪A'.actL i j (mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) i.succ))),
            mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) j.succ))⟫ :=
    energy_ge A' (fun i => mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) i.succ)))
  have hbil : A.bilin Ω u v
      = (∑ i : Fin d, ∑ j : Fin d,
          ⟪A'.actL i j (mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) i.succ))),
            mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) j.succ))⟫)
        + (∑ i : Fin d, ∑ j : Fin d, 2 * ⟪A'.actL i j
            (mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) i.succ))),
            mulTestPartial hξ j (diffQuotD k h hΩm ((u : H1amb Ω) 0))⟫)
        + evansRest hξ (fun i => diffQuotD k h hΩm ((u : H1amb Ω) i.succ))
            (diffQuotD k h hΩm ((u : H1amb Ω) 0)) (fun i j =>
              diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ))
                - A'.actL i j (diffQuotD k h hΩm ((u : H1amb Ω) i.succ))) := by
    rw [hvdef, evansTest_bilin_L2D A hΩm hξ hθ hS u, evansRest,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hsplit : diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ))
        = A'.actL i j (diffQuotD k h hΩm ((u : H1amb Ω) i.succ))
          + (diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ))
              - A'.actL i j (diffQuotD k h hΩm ((u : H1amb Ω) i.succ))) := by abel
    have hlead : ∀ p q : L2D Ω, ⟪mulTest (isTestFn_mul hξ hξ) q, A'.actL i j p⟫
        = ⟪A'.actL i j (mulTest hξ p), mulTest hξ q⟫ := fun p q => by
      rw [real_inner_comm, ← actL_mulTest_regroup A' hξ i j p q]
    have hcross : ∀ p q : L2D Ω, ⟪mulTestPartial (isTestFn_mul hξ hξ) j q, A'.actL i j p⟫
        = 2 * ⟪A'.actL i j (mulTest hξ p), mulTestPartial hξ j q⟫ := fun p q => by
      rw [real_inner_comm, actL_cross_regroup A' hξ i j p q]
    conv_lhs =>
      rw [cutoffMulOn_apply_succ, diffQuotG_apply, diffQuotG_apply, hsplit, inner_add_right,
        inner_add_left, hlead, hcross]
  have hweak : A.bilin Ω u v = ⟪f, (v : H1amb Ω) 0⟫
      - (∑ i : Fin d, ⟪Op.bAct i ((u : H1amb Ω) i.succ), (v : H1amb Ω) 0⟫)
      - ⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫ := by
    have hfull := hu v
    rw [Op.fullBilin_apply, Op.lowerBilin_apply, ← inner_eq_setIntegral] at hfull
    linarith only [hfull]
  linarith only [hLE, hbil, hweak]

/-! ### Master interior difference-quotient energy estimate -/

/-- The data norm `N = ‖f‖ + ‖u₀‖ + ∑ᵢ ‖∂ᵢu‖` of a weak solution satisfies
`N² ≤ κ (‖f‖² + ‖u₀‖²)`, with `κ` depending on `d`, `λ` and the Gårding shift alone. The
first-order energy estimate `firstOrder_energy_le` bounds the gradient. -/
private lemma sq_dataNorm_le (Op : FullEllipticOp d) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) :
    (‖f‖ + ‖(u : H1amb Ω) 0‖ + ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖) ^ 2
      ≤ 3 * (1 + d * (1 + 2 * Op.gardingγ) / Op.lam) * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) := by
  have hlam := Op.lam_pos
  have hγ := Op.gardingγ_nonneg
  have hfo := firstOrder_energy_le Op u f hu
  have hSg : (∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖) ^ 2
      ≤ d * ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i : Fin d => ‖(u : H1amb Ω) i.succ‖)
  set U1 := ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 with hU1
  have hU1' : U1 ≤ (1 + 2 * Op.gardingγ) / Op.lam * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    nlinarith only [hfo, sq_nonneg (‖f‖ - ‖(u : H1amb Ω) 0‖), mul_nonneg hγ (sq_nonneg ‖f‖),
      sq_nonneg ‖(u : H1amb Ω) 0‖, hγ, mul_nonneg hγ (sq_nonneg ‖(u : H1amb Ω) 0‖)]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h4 : (∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖) ^ 2
      ≤ d * ((1 + 2 * Op.gardingγ) / Op.lam * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2)) :=
    hSg.trans (mul_le_mul_of_nonneg_left hU1' hd)
  calc _ ≤ 3 * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2
          + (∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖) ^ 2) := by
        nlinarith only [sq_nonneg (‖f‖ - ‖(u : H1amb Ω) 0‖),
          sq_nonneg (‖f‖ - ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖),
          sq_nonneg (‖(u : H1amb Ω) 0‖ - ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖)]
    _ ≤ 3 * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2
          + d * ((1 + 2 * Op.gardingγ) / Op.lam * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2))) := by
        linarith only [h4]
    _ = _ := by ring

/-- The transport and zeroth-order pairings against a vector `w` are bounded by the first-order
data: `-∑ᵢ ⟪bᵢ ∂ᵢu, w⟫ - ⟪c u₀, w⟫ ≤ (B ∑ᵢ ‖∂ᵢu‖ + C ‖u₀‖) ‖w‖`. -/
private lemma neg_lowerOrder_le (Op : FullEllipticOp d) (U : H1amb Ω) (w : L2D Ω) :
    -∑ i : Fin d, ⟪Op.bAct i (U i.succ), w⟫ - ⟪Op.cAct (U 0), w⟫
      ≤ (Op.Bsup * ∑ i : Fin d, ‖U i.succ‖ + Op.Csup * ‖U 0‖) * ‖w‖ := by
  have hb : -∑ i : Fin d, ⟪Op.bAct i (U i.succ), w⟫
      ≤ Op.Bsup * (∑ i : Fin d, ‖U i.succ‖) * ‖w‖ := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => (neg_real_inner_le_mul_norm _ _).trans
      (mul_le_mul_of_nonneg_right (Op.norm_bAct_le i _) (norm_nonneg _))
  have hc : -⟪Op.cAct (U 0), w⟫ ≤ Op.Csup * ‖U 0‖ * ‖w‖ :=
    (neg_real_inner_le_mul_norm _ _).trans
      (mul_le_mul_of_nonneg_right (Op.norm_cAct_le _) (norm_nonneg _))
  linarith only [hb, hc]

/-- **Master interior difference-quotient energy estimate.** For a `W^{1,∞}`-coefficient
weak solution `u ∈ H₀¹(Ω)` of `L u = f`, an inner cutoff `ξ` and an
outer cutoff `θ ≡ 1` on the shift-reachable part of `tsupport ξ²`, the cutoff-weighted energy
of the interior difference quotient of the gradient is bounded by the data, uniformly in the
step `h`: `(λ/2) ∑ᵢ ‖ξ · Dₖ^h ∂ᵢu‖² ≤ C (‖f‖² + ‖u₀‖²)`. The constant is quantified before
the solution and the datum, so it depends only on
`λ, Λ, A₁, d, γ, ‖b‖∞, ‖c‖∞, ‖ξ‖∞, ‖∂ξ‖∞`, and on none of `u`, `f`, `h`. Testing the weak
formulation with the admissible Evans element `v_h = -Dₖ^{-h}(ξ² Dₖ^h u)`, discrete integration by
parts (`evansTest_bilin_L2D`) moves the outer difference quotient onto the coefficient action;
the discrete Leibniz split (`norm_diffQuotD_actL_sub_le`) exposes the translated-coefficient
leading term, controlled from below by ellipticity (`energy_ge`); Cauchy-Schwarz bounds the
remaining terms by `K₁ N e + K₂ N²` with `e² = ∑ᵢ ‖ξ Dₖ^h ∂ᵢu‖²` and `N` the data norm, and
absorption (`absorb_energy`) removes `e` from the right-hand side (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*,
Theorem 8.8). -/
theorem interior_diffQuot_energy_bound (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff)
    (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ) (k : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∀ (h : ℝ), h ≠ 0 → ShiftAdmissible Ω ξ θ k h →
      Op.lam / 2 * ∑ i : Fin d,
        ‖extendL2 hΩm (mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) i.succ)))‖ ^ 2
        ≤ C * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) := by
  classical
  set A := Op.toEllipticCoeff with hAdef
  have hlam := A.lam_pos
  have hX := hξ.supNorm_nonneg
  have hW := (isTestFn_mul hξ hξ).partialSupNorm_nonneg k
  have hSW : 0 ≤ ∑ j : Fin d, hξ.partialSupNorm j :=
    Finset.sum_nonneg fun j _ => hξ.partialSupNorm_nonneg j
  have hSW2 : 0 ≤ ∑ j : Fin d, (isTestFn_mul hξ hξ).partialSupNorm j :=
    Finset.sum_nonneg fun j _ => (isTestFn_mul hξ hξ).partialSupNorm_nonneg j
  have hA1 := hA.A1_nonneg
  have hΛ := A.Λ_nonneg
  have hB := Op.Bsup_nonneg
  have hCs := Op.Csup_nonneg
  have hγ := Op.gardingγ_nonneg
  set M : ℝ := 1 + Op.Bsup + Op.Csup with hM
  set K₁ : ℝ := (M * hξ.supNorm + 2 * A.Λ * (∑ j : Fin d, hξ.partialSupNorm j) * Real.sqrt d
    + hA.A1 * hξ.supNorm * Real.sqrt d) with hK₁
  set K₂ : ℝ := M * (isTestFn_mul hξ hξ).partialSupNorm k
    + hA.A1 * ∑ j : Fin d, (isTestFn_mul hξ hξ).partialSupNorm j with hK₂
  set κ : ℝ := 3 * (1 + d * (1 + 2 * Op.gardingγ) / Op.lam) with hκ
  refine ⟨(K₁ ^ 2 / (2 * A.lam) + K₂) * κ, by positivity, ?_⟩
  intro u f hu h hh hS
  have hlow := evans_lower_bound Op hΩm hξ hθ hS u f hu
  have hr0 : 0 ≤ ‖(u : H1amb Ω) 0‖ := norm_nonneg _
  have hf0 : 0 ≤ ‖f‖ := norm_nonneg _
  set r : ℝ := ‖(u : H1amb Ω) 0‖ with hr
  set Sg : ℝ := ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ with hSg
  set N : ℝ := ‖f‖ + r + Sg with hN
  set E : ℝ := ∑ i : Fin d, ‖mulTest hξ (evansDg hΩm k h u i)‖ ^ 2 with hE
  have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hev : ∀ i, ‖mulTest hξ (evansDg hΩm k h u i)‖ ≤ Real.sqrt E := fun i =>
    Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun i =>
      ‖mulTest hξ (evansDg hΩm k h u i)‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i))
  have hSe : ∑ i : Fin d, ‖mulTest hξ (evansDg hΩm k h u i)‖ ≤ Real.sqrt d * Real.sqrt E :=
    sum_le_sqrt_card_mul_sqrt_sum_sq _
  have hSe0 : 0 ≤ ∑ i : Fin d, ‖mulTest hξ (evansDg hΩm k h u i)‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hδ : ‖evansD0 hΩm k h u‖ ≤ N :=
    (norm_diffQuotD_le_grad hΩm k u h).trans (by
      have := Finset.single_le_sum (f := fun i : Fin d => ‖(u : H1amb Ω) i.succ‖)
        (fun i _ => norm_nonneg _) (Finset.mem_univ k)
      linarith)
  have hv0 := (norm_evansTest_zero_le hΩm hξ hθ hS u).trans (add_le_add
    (mul_le_mul_of_nonneg_left (hev k) hX) (mul_le_mul_of_nonneg_left hδ hW))
  have hTl := neg_lowerOrder_le Op (u : H1amb Ω) ((evansTest hΩm hξ hθ hS u : H1amb Ω) 0)
  have hTx : -∑ i : Fin d, ∑ j : Fin d, 2 * ⟪(A.translate (hshift k h)).actL i j
        (mulTest hξ (evansDg hΩm k h u i)), mulTestPartial hξ j (evansD0 hΩm k h u)⟫
      ≤ 2 * A.Λ * ‖evansD0 hΩm k h u‖ * ((∑ i : Fin d, ‖mulTest hξ (evansDg hΩm k h u i)‖)
        * ∑ j : Fin d, hξ.partialSupNorm j) :=
    neg_cross_sum_le (A.translate (hshift k h)) hξ (evansDg hΩm k h u) (evansD0 hΩm k h u)
  have hTr := neg_evansRest_le hξ (evansDg hΩm k h u) (evansD0 hΩm k h u)
    (evansComm A hΩm k h u) (c := hA.A1) (fun i => ‖(u : H1amb Ω) i.succ‖)
    (fun i j => norm_diffQuotD_actL_sub_le hA hΩm i j k hh _)
  have hTf := real_inner_le_norm f ((evansTest hΩm hξ hθ hS u : H1amb Ω) 0)
  have hfN : ‖f‖ ≤ N := by linarith
  have hrN : r ≤ N := by linarith
  have hSgN : Sg ≤ N := by linarith
  have hcoef : ‖f‖ + Op.Bsup * Sg + Op.Csup * r ≤ M * N := by
    rw [hM]
    nlinarith only [mul_le_mul_of_nonneg_left hSgN hB, mul_le_mul_of_nonneg_left hrN hCs, hfN]
  have hM0 : 0 ≤ M := by rw [hM]; linarith
  have hN0 : 0 ≤ N := by rw [hN]; linarith
  have h1 := mul_le_mul hcoef hv0 (norm_nonneg _) (mul_nonneg hM0 hN0)
  have h2 : 2 * A.Λ * ‖evansD0 hΩm k h u‖ * ((∑ i : Fin d, ‖mulTest hξ (evansDg hΩm k h u i)‖)
        * ∑ j : Fin d, hξ.partialSupNorm j)
      ≤ 2 * A.Λ * N * (Real.sqrt d * Real.sqrt E * ∑ j : Fin d, hξ.partialSupNorm j) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hδ (mul_nonneg zero_le_two hΛ))
      (mul_le_mul_of_nonneg_right hSe hSW) (mul_nonneg hSe0 hSW)
      (mul_nonneg (mul_nonneg zero_le_two hΛ) hN0)
  have h3 : hA.A1 * Sg * (hξ.supNorm * ∑ i : Fin d, ‖mulTest hξ (evansDg hΩm k h u i)‖
        + (∑ j : Fin d, (isTestFn_mul hξ hξ).partialSupNorm j) * ‖evansD0 hΩm k h u‖)
      ≤ hA.A1 * N * (hξ.supNorm * (Real.sqrt d * Real.sqrt E)
        + (∑ j : Fin d, (isTestFn_mul hξ hξ).partialSupNorm j) * N) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hSgN hA1)
      (add_le_add (mul_le_mul_of_nonneg_left hSe hX) (mul_le_mul_of_nonneg_left hδ hSW2))
      (add_nonneg (mul_nonneg hX hSe0) (mul_nonneg hSW2 (norm_nonneg _)))
      (mul_nonneg hA1 hN0)
  have hkey : A.lam * Real.sqrt E ^ 2 ≤ K₁ * N * Real.sqrt E + K₂ * N ^ 2 := by
    rw [Real.sq_sqrt hE0, hK₁, hK₂, hM]
    nlinarith only [hlow, hTf, hTl, hTx, hTr, h1, h2, h3]
  have habs := absorb_energy hlam hkey
  have hdata : N ^ 2 ≤ κ * (‖f‖ ^ 2 + r ^ 2) := sq_dataNorm_le Op u f hu
  have hnorm : ∑ i : Fin d, ‖extendL2 hΩm (mulTest hξ (diffQuotD k h hΩm
      ((u : H1amb Ω) i.succ)))‖ ^ 2 = E := by
    simp only [hE, norm_extendL2]
  rw [hnorm]
  calc A.lam / 2 * E = A.lam / 2 * Real.sqrt E ^ 2 := by rw [Real.sq_sqrt hE0]
    _ ≤ _ := habs
    _ ≤ (K₁ ^ 2 / (2 * A.lam) + K₂) * (κ * (‖f‖ ^ 2 + r ^ 2)) :=
        mul_le_mul_of_nonneg_left hdata (by positivity)
    _ = _ := by ring

end EllipticPdes.Regularity
