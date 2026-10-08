/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.Morrey
public import EllipticPdes.Embedding.Convolution
public import EllipticPdes.Regularity.CutoffTower
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
# Sobolev bootstrap from `Lᵖ` to the conjugate exponent

`morrey_ball` needs a gradient in `Lᵖ` with `p > d`, and the interior `H²` estimate delivers one
in `L²`, so the two compose directly only when `d = 1`. The Gagliardo-Nirenberg-Sobolev
inequality closes the gap in low dimension: an `Lᵖ` weak gradient with `1 ≤ p < d` upgrades to
`Lᵖ'` at the Sobolev conjugate `1/p' = 1/p - 1/d`, and Morrey then applies whenever `p' > d`.

## Dimensions the chain reaches

`p' > d` is equivalent to `p > d/2`, and `L²` data on a ball of finite measure is `Lᵖ` data
exactly when `p ≤ 2`, so a single Sobolev step feeds Morrey precisely when the window
`d/2 < p ≤ min 2 d` is inhabited.

* `d = 1`: Morrey applies to the first-order gradient at `p = 2 > 1`, so no bootstrap is needed.
* `d = 2`: `p = 4/3` has conjugate `4 > 2` (`exists_eLpNorm_four_le`).
* `d = 3`: `p = 2` has conjugate `6 > 3` (`exists_eLpNorm_six_le`).
* `d ≥ 4`: the window is empty, since `d/2 ≥ 2`, so one Sobolev step never reaches `p' > d`.

The bootstrap itself holds in every dimension. Only its composition with Morrey out of `L²` data
is limited, and `EllipticPdes.Embedding.memLp_of_gradClosed` lifts that limit by iterating the
step, at the price of a weak derivative per rung.

Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` asks for `ContDiff ℝ 1` and compact
support, neither of which an `Lᵖ` class with weak derivatives has. Two devices bridge that.

* A smooth cutoff `η` supported in the ball turns a weak gradient on the ball into a compactly
  supported weak gradient on the whole space, with the product-rule term `v ∂ₖη`
  (`hasWeakGradOn_univ_mul_cutoff`).
* Mollification turns that into a smooth compactly supported function whose classical partials
  are the mollified weak gradient (`partialD_convolution_eq_of_hasWeakGradOn` at `Set.univ`),
  whose `Lᵖ` seminorms Young's inequality (`eLpNorm_convolution_le`) keeps bounded uniformly in
  the mollifier radius, and which converges almost everywhere to the original function, so Fatou
  (`MeasureTheory.eLpNorm_le_of_ae_tendsto`) passes the `Lᵖ'` bound to the limit.

## Main declarations

* `HasWeakGradOn.mono`: a weak gradient restricts to a subset.
* `hasWeakGradOn_univ_mul_cutoff`: the product rule against a smooth cutoff.
* `exists_eLpNorm_sobolevConj_le`: the bootstrap in general dimension and at a general exponent
  pair, with a constant independent of the function.
* `exists_eLpNorm_sobolevConj_le_of_le`: the same, fed by data at a higher exponent.
* `exists_eLpNorm_six_le` and `exists_eLpNorm_four_le`: the `d = 3` and `d = 2` specialisations.

## References

Evans, *Partial Differential Equations* (2nd ed.), §5.6.1 Thm 1.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution Topology

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD tsupport_partialD_subset)

variable {d : ℕ}

/-! ### Restriction of a weak gradient -/

/-- **Restriction of a weak gradient to a subset.** Both integration-by-parts integrals localise to
the support of the test function, which lies in the smaller set, so the identity over the larger
set transfers verbatim. No measurability of either set is needed: each integrand vanishes off
`tsupport φ`, and `setIntegral_eq_integral_of_forall_compl_eq_zero` collapses both set integrals
to the same whole-space integral. -/
theorem HasWeakGradOn.mono {B B' : Set (EuclideanSpace ℝ (Fin d))} (hsub : B' ⊆ B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : HasWeakGradOn B u g) : HasWeakGradOn B' u g := by
  intro φ hφc hφcs hφB' k
  have key := h φ hφc hφcs (hφB'.trans hsub) k
  have hdk : ∀ x ∉ B', u x * partialD k φ x = 0 := by
    intro x hx
    rw [show partialD k φ x = 0 from image_eq_zero_of_notMem_tsupport
      (fun hc => hx (hφB' (tsupport_partialD_subset k φ hc))), mul_zero]
  have hphi : ∀ x ∉ B', g k x * φ x = 0 := by
    intro x hx
    rw [show φ x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hx (hφB' hc)), mul_zero]
  have hdkB : ∀ x ∉ B, u x * partialD k φ x = 0 := fun x hx => hdk x fun hc => hx (hsub hc)
  have hphiB : ∀ x ∉ B, g k x * φ x = 0 := fun x hx => hphi x fun hc => hx (hsub hc)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hdk,
    setIntegral_eq_integral_of_forall_compl_eq_zero hphi]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hdkB,
    setIntegral_eq_integral_of_forall_compl_eq_zero hphiB] at key
  exact key

/-- **Dependence of a weak gradient on the almost-everywhere classes alone.** Replacing `u` and
`g` by functions agreeing with them almost everywhere on `B` leaves the integration-by-parts
identity untouched. This moves a statement about a restricted `Lp` class onto whichever
representative is convenient, in particular onto the extension by zero, which is shared across
every set. -/
theorem HasWeakGradOn.congr_ae {B : Set (EuclideanSpace ℝ (Fin d))}
    {u u' : EuclideanSpace ℝ (Fin d) → ℝ} {g g' : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : HasWeakGradOn B u g) (hu : u =ᵐ[volume.restrict B] u')
    (hg : ∀ k, g k =ᵐ[volume.restrict B] g' k) : HasWeakGradOn B u' g' := by
  intro φ hφc hφcs hφB k
  rw [← integral_congr_ae (hu.mono fun x hx => by simp only; rw [hx] :
      (fun x => u x * partialD k φ x) =ᵐ[volume.restrict B] fun x => u' x * partialD k φ x),
    ← integral_congr_ae ((hg k).mono fun x hx => by simp only; rw [hx] :
      (fun x => g k x * φ x) =ᵐ[volume.restrict B] fun x => g' k x * φ x)]
  exact h φ hφc hφcs hφB k

/-! ### Product rule against a smooth cutoff -/

/-- The product rule for the coordinate partial derivative. -/
theorem partialD_mul {η φ : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d)
    {y : EuclideanSpace ℝ (Fin d)} (hη : DifferentiableAt ℝ η y)
    (hφ : DifferentiableAt ℝ φ y) :
    partialD k (fun x => η x * φ x) y = partialD k η y * φ y + η y * partialD k φ y := by
  have hfd : HasFDerivAt (fun x => η x * φ x)
      (η y • fderiv ℝ φ y + φ y • fderiv ℝ η y) y := hη.hasFDerivAt.mul hφ.hasFDerivAt
  rw [partialD, hfd.fderiv]
  simp only [_root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul, partialD]
  ring

/-- A function integrable on a set stays integrable after multiplication by a continuous
function of compact support. -/
theorem integrableOn_mul_of_hasCompactSupport {α : Type*} [TopologicalSpace α]
    {m : MeasurableSpace α} [OpensMeasurableSpace α] {μ : Measure α} {B : Set α} {f ψ : α → ℝ}
    (hf : IntegrableOn f B μ) (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) :
    IntegrableOn (fun x => f x * ψ x) B μ := by
  obtain ⟨C, hC⟩ := hψs.exists_bound_of_continuous hψ
  exact hf.mul_bdd hψ.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- **Cutting a weak gradient off.** If `g` is the weak gradient of `u` on `B` and `η` is a
smooth compactly supported function with `tsupport η ⊆ B`, then the extension by zero of `η u`
has a weak gradient on the whole space, namely `η gₖ + u ∂ₖη`. Testing against `φ` reduces to
testing the hypothesis against `η φ`, which is again a test function supported in `B`, and the
product rule supplies the extra term. This is what makes the mollification argument reach a
compactly supported function without a boundary contribution from `∂B`. -/
theorem hasWeakGradOn_univ_mul_cutoff {B : Set (EuclideanSpace ℝ (Fin d))}
    (hB : MeasurableSet B) {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hηc : ContDiff ℝ (⊤ : ℕ∞) η) (hηcs : HasCompactSupport η) (hηs : tsupport η ⊆ B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (h : HasWeakGradOn B u g) :
    HasWeakGradOn Set.univ (fun x => η x * B.indicator u x)
      (fun k x => η x * B.indicator (g k) x + partialD k η x * B.indicator u x) := by
  intro φ hφc hφcs _ k
  have hηd : Differentiable ℝ η := hηc.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφc.differentiable (by simp)
  -- The multipliers are continuous with compact support, hence bounded.
  have hηpc : Continuous (partialD k η) :=
    (hηc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hηpcs : HasCompactSupport (partialD k η) :=
    hηcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  -- The hypothesis applied to the test function `η φ`.
  have hψs : tsupport (fun x => η x * φ x) ⊆ B :=
    (closure_mono (Function.support_mul_subset_left η φ)).trans hηs
  have key := h (fun x => η x * φ x) (hηc.mul hφc) hφcs.mul_left hψs k
  have hprod : ∀ x, partialD k (fun z => η z * φ z) x
      = partialD k η x * φ x + η x * partialD k φ x :=
    fun x => partialD_mul k (hηd x) (hφd x)
  -- Integrability of the four products against the compactly supported smooth multipliers.
  have hi1 : IntegrableOn (fun x => u x * (partialD k η x * φ x)) B volume :=
    integrableOn_mul_of_hasCompactSupport hu (hηpc.mul hφc.continuous) hηpcs.mul_right
  have hi2 : IntegrableOn (fun x => u x * (η x * partialD k φ x)) B volume :=
    integrableOn_mul_of_hasCompactSupport hu (hηc.continuous.mul hφpc) hηcs.mul_right
  have hi3 : IntegrableOn (fun x => (η x * g k x) * φ x) B volume :=
    (integrableOn_mul_of_hasCompactSupport (hgi k) (hηc.continuous.mul hφc.continuous)
      hηcs.mul_right).congr (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hi4 : IntegrableOn (fun x => (partialD k η x * u x) * φ x) B volume :=
    hi1.congr (Filter.Eventually.of_forall fun x => by ring)
  -- Split the hypothesis by the product rule.
  have hsplit : (∫ x in B, u x * (partialD k η x * φ x))
      + ∫ x in B, u x * (η x * partialD k φ x)
      = - ∫ x in B, (η x * g k x) * φ x := by
    have hlhs : (∫ x in B, u x * (partialD k η x * φ x))
        + ∫ x in B, u x * (η x * partialD k φ x)
        = ∫ x in B, u x * partialD k (fun z => η z * φ z) x := by
      rw [← integral_add hi1 hi2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [hprod]; ring)
    rw [hlhs, key]
    exact congrArg Neg.neg
      (integral_congr_ae (Filter.Eventually.of_forall fun x => by ring))
  -- Collapse the two whole-space integrals of the goal onto `B`.
  have hzeroL : ∀ x ∉ B, (η x * B.indicator u x) * partialD k φ x = 0 := by
    intro x hx
    rw [Set.indicator_of_notMem hx, mul_zero, zero_mul]
  have hzeroR : ∀ x ∉ B,
      (η x * B.indicator (g k) x + partialD k η x * B.indicator u x) * φ x = 0 := by
    intro x hx
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, mul_zero, add_zero,
      zero_mul]
  have hL : ∫ x, (η x * B.indicator u x) * partialD k φ x
      = ∫ x in B, u x * (η x * partialD k φ x) := by
    rw [(setIntegral_eq_integral_of_forall_compl_eq_zero hzeroL).symm]
    exact setIntegral_congr_fun hB fun x hx => by
      rw [Set.indicator_of_mem hx]; ring
  have hR : ∫ x, (η x * B.indicator (g k) x + partialD k η x * B.indicator u x) * φ x
      = (∫ x in B, (η x * g k x) * φ x) + ∫ x in B, (partialD k η x * u x) * φ x := by
    rw [(setIntegral_eq_integral_of_forall_compl_eq_zero hzeroR).symm, ← integral_add hi3 hi4]
    exact setIntegral_congr_fun hB fun x hx => by
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
  have hswap : ∫ x in B, (partialD k η x * u x) * φ x
      = ∫ x in B, u x * (partialD k η x * φ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [Measure.restrict_univ, hL, hR, hswap]
  linarith [hsplit]

/-! ### Bootstrap -/

section Bootstrap

open EllipticPdes.Regularity (exists_isTestFn_one_nhdsSet_of_isCompact)

/-- **Gagliardo-Nirenberg-Sobolev for a compactly supported weak gradient.** A compactly
supported `w` on `ℝᵈ` whose weak gradient `G` lies in `Lᵖ` lies in `Lᵖ'`, where
`1/p' = 1/p - 1/d`, bounded by the gradient alone with a constant depending only on `d` and
`p`.

Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` asks for `ContDiff ℝ 1`, so a weak
gradient reaches it through a mollification, whose classical partials are the mollified weak
gradient (`partialD_convolution_eq_of_hasWeakGradOn`) and whose `Lᵖ` seminorms Young's
inequality keeps bounded uniformly in the mollifier radius. Fatou passes the bound to the
almost-everywhere limit.

No cutoff enters, so the conclusion is on the whole space and the bound has no `‖w‖_{Lᵖ}`
term. `exists_eLpNorm_sobolevConj_le` is this statement composed with a cutoff, and the cutoff
is what forces the smaller ball and the extra term. -/
theorem exists_eLpNorm_sobolevConj_le_compactSupport (hd : 0 < d)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹) :
    ∃ K : ℝ≥0, ∀ (w : EuclideanSpace ℝ (Fin d) → ℝ)
        (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      HasCompactSupport w → Integrable w volume → MemLp w p volume →
      (∀ k, MemLp (G k) p volume) → HasWeakGradOn Set.univ w G →
      MemLp w p' volume ∧
        eLpNorm w p' volume ≤ (K : ℝ≥0∞) * ∑ k, eLpNorm (G k) p volume := by
  classical
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hp
  have hpofReal : ENNReal.ofReal (p : ℝ) = (p : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  set Kg : ℝ≥0 :=
    SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin d))) (p : ℝ)
    with hKgdef
  refine ⟨Kg, fun w G hwcs hwint hwL hGL hwg' => ?_⟩
  have hGL2 : ∀ k, MemLp (G k) (ENNReal.ofReal (p : ℝ)) volume := by
    intro k; rw [hpofReal]; exact hGL k
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hLdef
  set φb : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := stdBump 1 one_pos with hφb
  have hφrOut : Filter.Tendsto (fun n => (φb n).rOut) Filter.atTop (𝓝 0) :=
    tendsto_rOut_stdBump one_pos
  have hφratio : ∀ n, (φb n).rOut ≤ 2 * (φb n).rIn := rOut_stdBump_le one_pos
  set W : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => w ⋆[L, volume] (φb n).normed volume with hWdef
  have hρ0 : ∀ n, (0 : EuclideanSpace ℝ (Fin d) → ℝ) ≤ (φb n).normed volume :=
    fun n x => (φb n).nonneg_normed x
  have hρcont : ∀ n, Continuous ((φb n).normed volume) :=
    fun n => ((φb n).contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous
  have hρm : ∀ n, AEStronglyMeasurable ((φb n).normed volume) volume :=
    fun n => (hρcont n).aestronglyMeasurable
  have hρ1 : ∀ n, ∫ y, (φb n).normed volume y ∂volume = 1 := fun n => (φb n).integral_normed
  have hwli : LocallyIntegrable w volume := hwint.locallyIntegrable
  have hWsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (W n) :=
    fun n => contDiff_convolution_normed (φb n) hwli
  have hWcs : ∀ n, HasCompactSupport (W n) :=
    fun n => hasCompactSupport_convolution_normed (φb n) hwcs
  have hWpartialCont : ∀ n k, Continuous (partialD k (W n)) :=
    fun n k => ((hWsmooth n).continuous_fderiv (by simp)).clm_apply continuous_const
  -- The classical partials of a mollification are the mollified weak gradient.
  have hpartial : ∀ (n : ℕ) (k : Fin d),
      partialD k (W n) = (G k ⋆[L, volume] (φb n).normed volume) := by
    intro n k
    funext x
    have hbridge := partialD_convolution_eq_of_hasWeakGradOn (B := Set.univ) MeasurableSet.univ
      (u := w) (g := G) (by rwa [IntegrableOn, Measure.restrict_univ]) hwg' (φb n) k
      (x := x) (subset_univ _)
    simpa only [Set.indicator_univ, hWdef] using hbridge
  -- Gagliardo-Nirenberg-Sobolev on each mollification, with Young keeping the bound uniform.
  have hbound : ∀ n, eLpNorm (W n) p' volume ≤ (Kg : ℝ≥0∞) * ∑ k, eLpNorm (G k) p volume := by
    intro n
    have hgns : eLpNorm (W n) p' volume ≤ (Kg : ℝ≥0∞) * eLpNorm (fderiv ℝ (W n)) p volume := by
      have h := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq (F := ℝ)
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (u := W n)
        ((hWsmooth n).of_le (by exact_mod_cast le_top)) (hWcs n) (p := p) (p' := p')
        hp (by rw [finrank_euclideanSpace_fin]; exact hd)
        (by rw [finrank_euclideanSpace_fin]; exact hpp')
      simpa [hKgdef] using h
    have hfd : eLpNorm (fderiv ℝ (W n)) p volume
        ≤ ∑ k, eLpNorm (partialD k (W n)) p volume :=
      eLpNorm_fderiv_le_sum_partialD ((hWsmooth n).continuous_fderiv (by simp)) hp1
        fun k => (hWpartialCont n k).aestronglyMeasurable
    have hyoung : ∀ k, eLpNorm (partialD k (W n)) p volume ≤ eLpNorm (G k) p volume := by
      intro k
      rw [hpartial n k]
      have h := eLpNorm_convolution_le (p := (p : ℝ)) hpR (hρ0 n) (hρm n) (hρ1 n) (hGL2 k)
      simpa [hpofReal] using h
    exact hgns.trans (mul_le_mul' le_rfl
      (hfd.trans (Finset.sum_le_sum fun k _ => hyoung k)))
  -- The mollifications converge to `w` almost everywhere, so Fatou passes the bound to `w`.
  have hae : ∀ᵐ x ∂volume, Filter.Tendsto (fun n => W n x) Filter.atTop (𝓝 (w x)) := by
    filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := volume) (g := w) hφrOut (Filter.Eventually.of_forall hφratio) hwli] with x hx
    exact hx.congr fun n => congrFun (convolution_lsmul_comm _ _) x
  have hwsix : eLpNorm w p' volume ≤ (Kg : ℝ≥0∞) * ∑ k, eLpNorm (G k) p volume :=
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound)
      (fun n => (hWsmooth n).continuous.aestronglyMeasurable) hwL.aestronglyMeasurable hae
  refine ⟨?_, hwsix⟩
  exact lt_of_le_of_lt hwsix (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (ENNReal.sum_lt_top.mpr fun k _ => (hGL k).eLpNorm_lt_top))


/-- **A cutoff with bounded gradient.** For `r < R` there is a smooth compactly supported `η` with
values in `[-1, 1]`, equal to `1` on `closedBall c r`, supported in `ball c R`, whose partial
derivatives are bounded by some `M`. -/
theorem exists_cutoff_with_bound (c : EuclideanSpace ℝ (Fin d)) {r R : ℝ} (hrR : r < R) :
    ∃ (η : EuclideanSpace ℝ (Fin d) → ℝ) (M : ℝ≥0), ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Metric.ball c R ∧ (∀ x ∈ Metric.closedBall c r, η x = 1) ∧
      (∀ x, ‖η x‖ ≤ 1) ∧ ∀ (k : Fin d) x, ‖partialD k η x‖ ≤ M := by
  obtain ⟨η, ⟨hηc, hηcs, hηs⟩, hη1, hηIcc⟩ := exists_isTestFn_one_nhdsSet_of_isCompact
    (K := Metric.closedBall c r) (U := Metric.ball c R) (isCompact_closedBall c r)
    Metric.isOpen_ball (Metric.closedBall_subset_ball hrR)
  obtain ⟨M, hM⟩ := (hηcs.fderiv ℝ).exists_bound_of_continuous
    (hηc.continuous_fderiv (by simp) : Continuous (fun x => fderiv ℝ η x))
  refine ⟨η, M.toNNReal, hηc, hηcs, hηs, hη1.self_of_nhdsSet, fun x => ?_, fun k x => ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hηIcc x).1]; exact (hηIcc x).2
  · calc ‖partialD k η x‖ ≤ ‖fderiv ℝ η x‖ * ‖EuclideanSpace.single k (1 : ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ η x‖ := by simp
      _ ≤ M := hM x
      _ ≤ M.toNNReal := Real.le_coe_toNNReal M

/-- The extension by zero of a function in `Lᵖ(B)`, cut off by a function bounded by one, has
`Lᵖ` seminorm at most that of the function over `B`. -/
theorem eLpNorm_cutoff_mul_le {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [OpensMeasurableSpace α] {μ : Measure α} {B : Set α} (hB : MeasurableSet B)
    {η f : α → ℝ} (hη : Continuous η)
    (hη1 : ∀ x, ‖η x‖ ≤ 1) {p : ℝ≥0∞} (hf : AEStronglyMeasurable f (μ.restrict B)) :
    eLpNorm (fun x => η x * B.indicator f x) p μ ≤ eLpNorm f p (μ.restrict B) :=
  (eLpNorm_mono (g := B.indicator f)
    (show AEStronglyMeasurable (fun x => η x * B.indicator f x) μ from
      hη.aestronglyMeasurable.mul ((aestronglyMeasurable_indicator_iff hB).mpr hf))
    fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hη1 x)).trans_eq
    (eLpNorm_indicator_eq_eLpNorm_restrict hB.nullMeasurableSet)

/-- **The cut-off weak gradient in `Lᵖ`.** The components `η gₖ + (∂ₖ η) v`, extended by zero,
have `Lᵖ(ℝᵈ)` seminorm at most `‖gₖ‖_{Lᵖ(B)} + M ‖v‖_{Lᵖ(B)}`. -/
theorem eLpNorm_cutoff_gradient_le {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B)
    {η v g : EuclideanSpace ℝ (Fin d) → ℝ} {M : ℝ≥0} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη1 : ∀ x, ‖η x‖ ≤ 1) (k : Fin d) (hM : ∀ x, ‖partialD k η x‖ ≤ M) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hv : MemLp v p (volume.restrict B)) (hg : MemLp g p (volume.restrict B)) :
    eLpNorm (fun x => η x * B.indicator g x + partialD k η x * B.indicator v x) p volume
      ≤ eLpNorm g p (volume.restrict B) + M * eLpNorm v p (volume.restrict B) := by
  have hpc : Continuous (partialD k η) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  refine (eLpNorm_add_le hp).trans
    (add_le_add (eLpNorm_cutoff_mul_le hB hη.continuous hη1 hg.aestronglyMeasurable) ?_)
  calc eLpNorm (fun x => partialD k η x * B.indicator v x) p volume
      ≤ eLpNorm (fun x => (M : ℝ) * B.indicator v x) p volume := by
        refine eLpNorm_mono (show AEStronglyMeasurable (fun x => partialD k η x * B.indicator v x)
          volume from hpc.aestronglyMeasurable.mul
            ((aestronglyMeasurable_indicator_iff hB).mpr hv.aestronglyMeasurable)) fun x => ?_
        rw [norm_mul, norm_mul, NNReal.norm_eq]
        exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    _ = M * eLpNorm v p (volume.restrict B) := by
        rw [show (fun x => (M : ℝ) * B.indicator v x) = (M : ℝ) • (B.indicator v) from rfl,
          eLpNorm_const_smul, eLpNorm_indicator_eq_eLpNorm_restrict hB.nullMeasurableSet, NNReal.enorm_eq]

/-- **From `Lᵖ` to the Sobolev conjugate `Lᵖ'` (Evans, *Partial Differential Equations*
(2nd ed.), §5.6.1 Thm 1).** On a ball `Metric.ball c R` of `ℝᵈ` with `d ≥ 1`, a function `v` with
an `Lᵖ` weak gradient `g` lies in `Lᵖ'` of the smaller ball `Metric.ball c r`, where the exponents
satisfy `1/p' = 1/p - 1/d`, with a bound linear in `‖v‖_{Lᵖ} + ∑ₖ ‖gₖ‖_{Lᵖ}` and a constant
depending only on `d`, `p`, `c`, `r` and `R`.

The inequality itself is Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`, which asks
for `ContDiff ℝ 1` and compact support. Two devices transport it to a weak gradient on a ball: a
smooth cutoff supported in `Metric.ball c R` and equal to `1` on `Metric.closedBall c r`, and a
mollification, whose classical partials are the mollified weak gradient and whose `Lᵖ` seminorms
Young's inequality keeps bounded uniformly in the mollifier radius. Fatou passes the resulting
`Lᵖ'` bound to the almost-everywhere limit.

Outside the range `1 ≤ p < d`, which is the range Evans' statement takes, the hypothesis
`1/p' = 1/p - 1/d` says nothing about a Sobolev conjugate. At `p = d` it forces `p' = 0` and
the conclusion degenerates, `eLpNorm` at exponent zero being zero; above `p = d` its right
side is negative while the left is a reciprocal of a nonnegative number, so no `p'` meets it
and the statement is vacuous. -/
theorem exists_eLpNorm_sobolevConj_le (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹)
    {r R : ℝ} (_hr : 0 < r) (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      MemLp v p (volume.restrict (Metric.ball c R)) →
      (∀ k, MemLp (g k) p (volume.restrict (Metric.ball c R))) →
      HasWeakGradOn (Metric.ball c R) v g →
      MemLp v p' (volume.restrict (Metric.ball c r)) ∧
        eLpNorm v p' (volume.restrict (Metric.ball c r))
          ≤ (K : ℝ≥0∞) * (eLpNorm v p (volume.restrict (Metric.ball c R))
              + ∑ k, eLpNorm (g k) p (volume.restrict (Metric.ball c R))) := by
  have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hp
  obtain ⟨η, M, hηc, hηcs, hηs, hηone, hη1, hM⟩ := exists_cutoff_with_bound c hrR
  obtain ⟨Kg, hKg⟩ := exists_eLpNorm_sobolevConj_le_compactSupport hd hp hpp'
  refine ⟨Kg * (1 + d * M), fun v g hv hg hwg => ?_⟩
  set B : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball c R with hBdef
  have hBm : MeasurableSet B := measurableSet_ball
  set V := eLpNorm v p (volume.restrict B) with hV
  set S := ∑ k, eLpNorm (g k) p (volume.restrict B) with hS
  -- The cut-off function and its whole-space weak gradient.
  have hwg' := hasWeakGradOn_univ_mul_cutoff hBm hηc hηcs hηs (hv.integrable hp1)
    (fun k => (hg k).integrable hp1) hwg
  have hwL2 : MemLp (fun x => η x * B.indicator v x) p volume :=
    lt_of_le_of_lt (eLpNorm_cutoff_mul_le hBm hηc.continuous hη1 hv.aestronglyMeasurable)
      hv.eLpNorm_lt_top
  have hGbound := fun k => eLpNorm_cutoff_gradient_le hBm hηc hη1 k (hM k) hp1 hv (hg k)
  have hGLp : ∀ k, MemLp (fun x => η x * B.indicator (g k) x + partialD k η x * B.indicator v x)
      p volume := fun k => lt_of_le_of_lt (hGbound k)
    (ENNReal.add_lt_top.mpr ⟨(hg k).eLpNorm_lt_top, ENNReal.mul_lt_top ENNReal.coe_lt_top
      hv.eLpNorm_lt_top⟩)
  -- The whole-space inequality, applied to the cut-off function, and the gradient terms.
  have hvint : IntegrableOn v B volume := hv.integrable hp1
  have hwsix := (hKg _ _ hηcs.mul_right ((hvint.integrable_indicator hBm).bdd_mul
    hηc.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hη1)) hwL2 hGLp hwg').2
  have hsum : ∑ k, eLpNorm (fun x => η x * B.indicator (g k) x + partialD k η x *
      B.indicator v x) p volume ≤ ((1 + d * M : ℝ≥0) : ℝ≥0∞) * (V + S) := by
    calc _ ≤ ∑ k, (eLpNorm (g k) p (volume.restrict B) + M * V) := Finset.sum_le_sum fun k _ =>
          hGbound k
      _ = S + (d * M : ℝ≥0) * V := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
      _ ≤ (V + S) + (d * M : ℝ≥0) * (V + S) :=
          add_le_add le_add_self (mul_le_mul' le_rfl le_self_add)
      _ = _ := by push_cast; ring
  -- On the inner ball the cutoff is `1`, so the cut-off function and `v` agree there.
  have hcongr : eLpNorm v p' (volume.restrict (Metric.ball c r))
      = eLpNorm (fun x => η x * B.indicator v x) p' (volume.restrict (Metric.ball c r)) :=
    (eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).mpr
      (Filter.Eventually.of_forall fun x hx => by
        rw [hηone x (Metric.ball_subset_closedBall hx),
          Set.indicator_of_mem (Metric.ball_subset_ball hrR.le hx), one_mul]))).symm
  have hfinal : eLpNorm v p' (volume.restrict (Metric.ball c r))
      ≤ ((Kg * (1 + d * M) : ℝ≥0) : ℝ≥0∞) * (V + S) := by
    rw [hcongr, ENNReal.coe_mul, mul_assoc]
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      (hwsix.trans (mul_le_mul' le_rfl hsum))
  exact ⟨lt_of_le_of_lt hfinal (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (ENNReal.add_lt_top.mpr ⟨hv.eLpNorm_lt_top,
      ENNReal.sum_lt_top.mpr fun k _ => (hg k).eLpNorm_lt_top⟩)), hfinal⟩

/-- **A Gagliardo-Nirenberg-Sobolev rung with its constant.** On the domains `D` and `D'`, a
function in `Lq(D)` whose weak gradient is in `Lq(D)` lies in `L^{p'}(D')`, bounded by `K` times
the sum of the `Lq(D)` seminorms of the function and its gradient. -/
def RungBound (D D' : Set (EuclideanSpace ℝ (Fin d))) (q p' K : ℝ≥0) : Prop :=
  ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
    MemLp v q (volume.restrict D) → (∀ k, MemLp (g k) q (volume.restrict D)) →
    HasWeakGradOn D v g →
    MemLp v p' (volume.restrict D') ∧
      eLpNorm v p' (volume.restrict D') ≤ (K : ℝ≥0∞) * (eLpNorm v q (volume.restrict D)
        + ∑ k, eLpNorm (g k) q (volume.restrict D))

/-- **A rung fed by a higher exponent.** On a domain of finite measure, `Lq` data with `p ≤ q` is
`Lᵖ` data at the price of a factor `|D|^{1/p - 1/q}` which the constant absorbs. -/
theorem RungBound.mono_exponent {D D' : Set (EuclideanSpace ℝ (Fin d))}
    [IsFiniteMeasure (volume.restrict D)] {p q p' K : ℝ≥0} (hp : 0 < p) (hpq : p ≤ q)
    (h : RungBound D D' p p' K) : ∃ K' : ℝ≥0, RungBound D D' q p' K' := by
  have hpqE : (p : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hpq
  obtain ⟨A, hA⟩ := exists_const_eLpNorm_le_of_le (μ := volume.restrict D) (E := ℝ)
    (by exact_mod_cast hp.ne') hpqE
  refine ⟨K * A, fun v g hv hg hwg => ?_⟩
  obtain ⟨hmem, hbd⟩ := h v g (hv.mono_exponent hpqE) (fun k => (hg k).mono_exponent hpqE) hwg
  refine ⟨hmem, hbd.trans ?_⟩
  calc (K : ℝ≥0∞) * (eLpNorm v (p : ℝ≥0∞) (volume.restrict D)
          + ∑ k, eLpNorm (g k) (p : ℝ≥0∞) (volume.restrict D))
      ≤ (K : ℝ≥0∞) * (A * eLpNorm v (q : ℝ≥0∞) (volume.restrict D)
          + ∑ k, A * eLpNorm (g k) (q : ℝ≥0∞) (volume.restrict D)) :=
        mul_le_mul' le_rfl (add_le_add (hA v hv.aestronglyMeasurable)
          (Finset.sum_le_sum fun k _ => hA (g k) (hg k).aestronglyMeasurable))
    _ = ((K * A : ℝ≥0) : ℝ≥0∞) * (eLpNorm v (q : ℝ≥0∞) (volume.restrict D)
          + ∑ k, eLpNorm (g k) (q : ℝ≥0∞) (volume.restrict D)) := by
        rw [← Finset.mul_sum, ← mul_add, ENNReal.coe_mul, mul_assoc]

/-- **Bootstrap fed by a higher exponent.** The ball has finite measure, so `Lq` data with
`p ≤ q` is `Lᵖ` data, at the price of a factor `|B|^{1/p - 1/q}` which the constant absorbs.
This is the form the dimension-two chain uses: the interior `H²` estimate delivers `L²` data,
while the exponent that reaches Morrey through `1/p' = 1/p - 1/d` is `p = 4/3`. -/
theorem exists_eLpNorm_sobolevConj_le_of_le (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {p q p' : ℝ≥0} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      MemLp v q (volume.restrict (Metric.ball c R)) →
      (∀ k, MemLp (g k) q (volume.restrict (Metric.ball c R))) →
      HasWeakGradOn (Metric.ball c R) v g →
      MemLp v p' (volume.restrict (Metric.ball c r)) ∧
        eLpNorm v p' (volume.restrict (Metric.ball c r))
          ≤ (K : ℝ≥0∞) * (eLpNorm v q (volume.restrict (Metric.ball c R))
              + ∑ k, eLpNorm (g k) q (volume.restrict (Metric.ball c R))) := by
  obtain ⟨K, hK⟩ := exists_eLpNorm_sobolevConj_le hd c hp hpp' hr hrR
  exact RungBound.mono_exponent (hp.trans_lt' one_pos) hpq (K := K) hK

/-- **From `L²` to `L⁶` in dimension three.** The Sobolev conjugate of `2` in dimension `3` is
`2·3/(3-2) = 6`, so a function with an `L²` weak gradient on `Metric.ball c R` lies in `L⁶` of
`Metric.ball c r`. Since `6 > 3`, this single step feeds `morrey_ball`. -/
theorem exists_eLpNorm_six_le (c : EuclideanSpace ℝ (Fin 3)) {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin 3) → ℝ)
        (g : Fin 3 → EuclideanSpace ℝ (Fin 3) → ℝ),
      MemLp v 2 (volume.restrict (Metric.ball c R)) →
      (∀ k, MemLp (g k) 2 (volume.restrict (Metric.ball c R))) →
      HasWeakGradOn (Metric.ball c R) v g →
      MemLp v 6 (volume.restrict (Metric.ball c r)) ∧
        eLpNorm v 6 (volume.restrict (Metric.ball c r))
          ≤ (K : ℝ≥0∞) * (eLpNorm v 2 (volume.restrict (Metric.ball c R))
              + ∑ k, eLpNorm (g k) 2 (volume.restrict (Metric.ball c R))) := by
  have h := exists_eLpNorm_sobolevConj_le (d := 3) (by norm_num) c (p := 2) (p' := 6)
    (by norm_num) (by push_cast; norm_num) hr hrR
  simpa using h

/-- **From `L²` to `L⁴` in dimension two.** At `d = 2` the Sobolev conjugate of `2` degenerates,
so the step is taken at `p = 4/3`, whose conjugate is `4`. The ball has finite measure, so the
`L²` data of the interior `H²` estimate is `L^{4/3}` data. Since `4 > 2`, the result feeds
`morrey_ball`, with Hölder exponent `1 - 2/4 = 1/2`. -/
theorem exists_eLpNorm_four_le (c : EuclideanSpace ℝ (Fin 2)) {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin 2) → ℝ)
        (g : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ),
      MemLp v 2 (volume.restrict (Metric.ball c R)) →
      (∀ k, MemLp (g k) 2 (volume.restrict (Metric.ball c R))) →
      HasWeakGradOn (Metric.ball c R) v g →
      MemLp v 4 (volume.restrict (Metric.ball c r)) ∧
        eLpNorm v 4 (volume.restrict (Metric.ball c r))
          ≤ (K : ℝ≥0∞) * (eLpNorm v 2 (volume.restrict (Metric.ball c R))
              + ∑ k, eLpNorm (g k) 2 (volume.restrict (Metric.ball c R))) := by
  have h := exists_eLpNorm_sobolevConj_le_of_le (d := 2) (by norm_num) c
    (p := 4 / 3) (q := 2) (p' := 4) (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    (by rw [← NNReal.coe_le_coe]; push_cast; norm_num) (by push_cast; norm_num) hr hrR
  simpa using h

end Bootstrap

end EllipticPdes.Embedding
