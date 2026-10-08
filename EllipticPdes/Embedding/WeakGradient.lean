/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Basic
public import EllipticPdes.Sobolev.WeakDeriv
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Pointwise weak gradients on a set

## Main declarations

* `EllipticPdes.Embedding.HasWeakGradOn`: the weak gradient of a function on a set.
* `EllipticPdes.Embedding.HasWeakDerivAlong`: the weak derivative along a direction of any normed
  space.
* `EllipticPdes.Embedding.hasWeakGradOn_iff`: a weak gradient is a family of weak derivatives.
* `EllipticPdes.Embedding.HasWeakDerivAlong.comp_affine`: transport through `x ↦ e x + c`.
* `EllipticPdes.Embedding.HasWeakDerivAlong.sum`: a weak derivative is linear in the direction.

The `Lᵖ`-scale, pointwise-function analogue of `HasWeakDerivOn`: a function `u` has weak
gradient `g = (gₖ)` on `B` when the integration by parts identity is satisfied against every
smooth test function supported in `B`. This is the interface the Morrey embedding consumes; it is
stated for functions (not `Lp` classes) and for a full gradient tuple so that a
general exponent `p > d` is expressible, which the `L²`-only `HasWeakDerivOn` cannot do.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Integrability against a bounded factor.** An integrable class stays integrable when
multiplied by a bounded measurable one, which is how every test function and every cutoff of
this development enters an integral. -/
theorem integrableOn_mul_bounded {B : Set (EuclideanSpace ℝ (Fin d))}
    {w h : EuclideanSpace ℝ (Fin d) → ℝ} (hw : IntegrableOn w B volume) (hc : Continuous h)
    {C : ℝ} (hC : ∀ x, ‖h x‖ ≤ C) : IntegrableOn (fun x => w x * h x) B volume := by
  have hbd := hw.bdd_mul (f := h) hc.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  exact hbd.congr (Filter.Eventually.of_forall fun x => mul_comm (h x) (w x))

/-- `g` is the pointwise weak gradient of `u` on `B`: integration by parts holds
against every smooth compactly supported test function whose support lies in `B`. This
mirrors `EllipticPdes.Regularity.HasWeakDerivOn` component-wise but for pointwise
functions `u, gₖ : EuclideanSpace ℝ (Fin d) → ℝ`. -/
def HasWeakGradOn (B : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ B → ∀ k : Fin d,
      ∫ x in B, u x * partialD k φ x = - ∫ x in B, g k x * φ x

/-! ### Gradient tuple as a functional -/

/-- The continuous linear functional whose coordinate values are the entries of `g` at `y`. It is
the Riesz dual of the vector `(g k y)ₖ` (`gradCLM_eq_toDual`), the coordinate form of the weak
Fréchet derivative of `EllipticPdes.HasWeakFDerivOn` (`hasWeakGradOn_iff_hasWeakFDerivOn`). -/
def gradCLM (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  ∑ k, g k y • (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)

/-- `gradCLM g y` is the Riesz dual of the vector `(g k y)ₖ`. -/
theorem gradCLM_eq_toDual (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    gradCLM g y = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))
      (WithLp.toLp 2 fun k => g k y) := by
  ext x
  simp [gradCLM, InnerProductSpace.toDual_apply_apply, PiLp.inner_apply, mul_comm]

/-- `gradCLM g y` evaluated on a vector is the inner product with `(g k y)ₖ`. -/
theorem gradCLM_apply (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (y x : EuclideanSpace ℝ (Fin d)) :
    gradCLM g y x = ⟪(WithLp.toLp 2 fun k => g k y : EuclideanSpace ℝ (Fin d)), x⟫ := by
  rw [gradCLM_eq_toDual, InnerProductSpace.toDual_apply_apply]

/-- `gradCLM g y` evaluated on the `j`-th basis vector is `g j y`. -/
@[simp]
theorem gradCLM_apply_single (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    gradCLM g y (EuclideanSpace.single j (1 : ℝ)) = g j y := by
  simp [gradCLM]

/-- `gradCLM g` is continuous on a set where every component of `g` is. -/
theorem continuousOn_gradCLM {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    {B : Set (EuclideanSpace ℝ (Fin d))} (hg : ∀ k, ContinuousOn (g k) B) :
    ContinuousOn (gradCLM g) B :=
  continuousOn_finsetSum _ fun k _ => (hg k).smul continuousOn_const

/-- `gradCLM g` is `Cⁿ` on a set where every component of `g` is. -/
theorem contDiffOn_gradCLM {n : WithTop ℕ∞} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    {B : Set (EuclideanSpace ℝ (Fin d))} (hg : ∀ k, ContDiffOn ℝ n (g k) B) :
    ContDiffOn ℝ n (gradCLM g) B :=
  ContDiffOn.sum fun k _ => (hg k).smul contDiffOn_const

/-- **Scalar multiple of a weak gradient.** A constant multiple of a class with a weak gradient
has the same multiple of the gradient. -/
theorem HasWeakGradOn.const_mul {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (c : ℝ)
    (h : HasWeakGradOn B u g) :
    HasWeakGradOn B (fun x => c * u x) (fun k x => c * g k x) := by
  intro φ hφc hφcs hφs k
  have e := h φ hφc hφcs hφs k
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, e, mul_neg]

/-- **Additivity of a weak gradient.** Two classes with weak gradients on the same set add, and
so do their gradients. The finite sum of local pieces the extension operator glues is built by
iterating this. -/
theorem HasWeakGradOn.add {B : Set (EuclideanSpace ℝ (Fin d))}
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} {g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hv : IntegrableOn v B volume)
    (hg : ∀ k, IntegrableOn (g k) B volume) (hh : ∀ k, IntegrableOn (h k) B volume)
    (hU : HasWeakGradOn B u g) (hV : HasWeakGradOn B v h) :
    HasWeakGradOn B (fun x => u x + v x) (fun k x => g k x + h k x) := by
  intro φ hφc hφcs hφs k
  have hφcont : Continuous φ := hφc.continuous
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  obtain ⟨N, hN⟩ := hφpcs.exists_bound_of_continuous hφpc
  obtain ⟨P, hP⟩ := hφcs.exists_bound_of_continuous hφcont
  have hL : ∫ x in B, (u x + v x) * partialD k φ x
      = (∫ x in B, u x * partialD k φ x) + ∫ x in B, v x * partialD k φ x := by
    rw [← integral_add (integrableOn_mul_bounded hu hφpc hN)
      (integrableOn_mul_bounded hv hφpc hN)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hR : ∫ x in B, (g k x + h k x) * φ x
      = (∫ x in B, g k x * φ x) + ∫ x in B, h k x * φ x := by
    rw [← integral_add (integrableOn_mul_bounded (hg k) hφcont hP)
      (integrableOn_mul_bounded (hh k) hφcont hP)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hL, hR, hU φ hφc hφcs hφs k, hV φ hφc hφcs hφs k]
  ring

/-- **Zero as its own weak gradient.** -/
theorem hasWeakGradOn_zero {B : Set (EuclideanSpace ℝ (Fin d))} :
    HasWeakGradOn B (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) := by
  intro φ _ _ _ k
  simp

/-- **Finite sum of classes with weak gradients**, whose gradient is the sum. This is
what glues the local pieces of the extension operator. -/
theorem hasWeakGradOn_finsetSum {ι : Type*} (s : Finset ι)
    {B : Set (EuclideanSpace ℝ (Fin d))} {U : ι → EuclideanSpace ℝ (Fin d) → ℝ}
    {G : ι → Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : ∀ i ∈ s, IntegrableOn (U i) B volume)
    (hG : ∀ i ∈ s, ∀ k, IntegrableOn (G i k) B volume)
    (h : ∀ i ∈ s, HasWeakGradOn B (U i) (G i)) :
    HasWeakGradOn B (fun y => ∑ i ∈ s, U i y) (fun k y => ∑ i ∈ s, G i k y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasWeakGradOn_zero (B := B)
  | insert a t ha ih =>
    have hUt : ∀ i ∈ t, IntegrableOn (U i) B volume := fun i hi =>
      hU i (Finset.mem_insert_of_mem hi)
    have hGt : ∀ i ∈ t, ∀ k, IntegrableOn (G i k) B volume := fun i hi =>
      hG i (Finset.mem_insert_of_mem hi)
    have hht : ∀ i ∈ t, HasWeakGradOn B (U i) (G i) := fun i hi =>
      h i (Finset.mem_insert_of_mem hi)
    have hsum : HasWeakGradOn B (fun y => U a y + ∑ i ∈ t, U i y)
        (fun k y => G a k y + ∑ i ∈ t, G i k y) :=
      (h a (Finset.mem_insert_self a t)).add
        (hU a (Finset.mem_insert_self a t))
        (MeasureTheory.integrable_finsetSum _ fun i hi => hUt i hi)
        (fun k => hG a (Finset.mem_insert_self a t) k)
        (fun k => MeasureTheory.integrable_finsetSum _ fun i hi => hGt i hi k)
        (ih hUt hGt hht)
    simpa [Finset.sum_insert ha] using hsum

/-- The topological support of `f ∘ e` for a homeomorphism `e` is the preimage of that
of `f`. -/
theorem tsupport_comp_homeomorph {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Zero Z] (e : X ≃ₜ Y) (f : Y → Z) : tsupport (f ∘ e) = e ⁻¹' tsupport f := by
  rw [tsupport, tsupport, Function.support_comp_eq_preimage, e.preimage_closure]

/-- The product of an integrable function with a continuous function of compact support is
integrable. -/
theorem _root_.MeasureTheory.IntegrableOn.mul_of_hasCompactSupport {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] {μ : Measure X}
    {B : Set X} {u h : X → ℝ}
    (hu : IntegrableOn u B μ) (hh : Continuous h) (hcs : HasCompactSupport h) :
    IntegrableOn (fun x => u x * h x) B μ := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hh
  exact hu.mul_bdd hh.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- The product of a continuous function of compact support with an integrable function,
the continuous factor written first. -/
theorem _root_.MeasureTheory.IntegrableOn.hasCompactSupport_mul {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] {μ : Measure X}
    {B : Set X} {u h : X → ℝ} (hu : IntegrableOn u B μ) (hh : Continuous h)
    (hcs : HasCompactSupport h) : IntegrableOn (fun x => h x * u x) B μ :=
  (hu.mul_of_hasCompactSupport hh hcs).congr (Filter.Eventually.of_forall fun _ => mul_comm _ _)

section WeakDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E}

/-- **Weak derivative along a direction.** `g` is the weak derivative of `u` along `v` on `B`
when `∫_B u ∂_v φ = -∫_B g φ` for every smooth test function `φ` supported in `B`. -/
def HasWeakDerivAlong (μ : Measure E) (v : E) (B : Set E) (u g : E → ℝ) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ B →
    ∫ x in B, u x * fderiv ℝ φ x v ∂μ = -∫ x in B, g x * φ x ∂μ

/-- A weak gradient is a family of weak derivatives along the standard directions. -/
theorem hasWeakGradOn_iff {d : ℕ} {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} :
    HasWeakGradOn B u g ↔
      ∀ k, HasWeakDerivAlong volume (EuclideanSpace.single k (1 : ℝ)) B u (g k) :=
  ⟨fun h k φ hφ hc hs => h φ hφ hc hs k, fun h φ hφ hc hs k => h k φ hφ hc hs⟩

/-- A weak derivative scales with the direction. -/
theorem HasWeakDerivAlong.smul {v : E} {B : Set E} {u g : E → ℝ}
    (h : HasWeakDerivAlong μ v B u g) (c : ℝ) :
    HasWeakDerivAlong μ (c • v) B u (fun x => c * g x) := by
  intro φ hφ hc hs
  have : ∀ x, u x * fderiv ℝ φ x (c • v) = c * (u x * fderiv ℝ φ x v) := fun x => by
    simp only [map_smul, smul_eq_mul]; ring
  simp_rw [this, mul_assoc]
  rw [integral_const_mul, integral_const_mul, h φ hφ hc hs, mul_neg]

/-- **A weak derivative is linear in the direction.** For integrable `u` and integrable
derivatives, the derivative along a combination of directions is the combination of the
derivatives. -/
theorem HasWeakDerivAlong.sum [OpensMeasurableSpace E] {ι : Type*} (s : Finset ι)
    {B : Set E} {u : E → ℝ} {v : ι → E} {g : ι → E → ℝ} (c : ι → ℝ) (hu : IntegrableOn u B μ)
    (hg : ∀ i ∈ s, IntegrableOn (g i) B μ) (h : ∀ i ∈ s, HasWeakDerivAlong μ (v i) B u (g i)) :
    HasWeakDerivAlong μ (∑ i ∈ s, c i • v i) B u (fun x => ∑ i ∈ s, c i * g i x) := by
  intro φ hφ hc hs
  have hφc : Continuous φ := hφ.continuous
  have hd : ∀ w, Continuous fun x => fderiv ℝ φ x w := fun w =>
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hu' : ∀ i, IntegrableOn (fun x => u x * fderiv ℝ φ x (v i)) B μ := fun i =>
    hu.mul_of_hasCompactSupport (hd _) (hc.fderiv_apply (𝕜 := ℝ) _)
  have hg' : ∀ i ∈ s, IntegrableOn (fun x => g i x * φ x) B μ := fun i hi =>
    (hg i hi).mul_of_hasCompactSupport hφc hc
  have h1 : ∫ x in B, u x * fderiv ℝ φ x (∑ i ∈ s, c i • v i) ∂μ
      = ∑ i ∈ s, c i * ∫ x in B, u x * fderiv ℝ φ x (v i) ∂μ := by
    have : ∀ x, u x * fderiv ℝ φ x (∑ i ∈ s, c i • v i)
        = ∑ i ∈ s, c i * (u x * fderiv ℝ φ x (v i)) := fun x => by
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [this]
    rw [integral_finsetSum _ fun i _ => (hu' i).const_mul (c i)]
    simp_rw [integral_const_mul]
  have h2 : ∫ x in B, (∑ i ∈ s, c i * g i x) * φ x ∂μ
      = ∑ i ∈ s, c i * ∫ x in B, g i x * φ x ∂μ := by
    have : ∀ x, (∑ i ∈ s, c i * g i x) * φ x = ∑ i ∈ s, c i * (g i x * φ x) := fun x => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [this]
    rw [integral_finsetSum _ fun i hi => (hg' i hi).const_mul (c i)]
    simp_rw [integral_const_mul]
  rw [h1, h2, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i hi => by rw [h i hi φ hφ hc hs, mul_neg]

/-- **Transport of a weak derivative through an affine automorphism.** If `x ↦ e x + c`
preserves `μ` and `u` has weak derivative `g` along `e v` on `B`, then `u ∘ (e · + c)` has weak
derivative `g ∘ (e · + c)` along `v` on the preimage of `B`. -/
theorem HasWeakDerivAlong.comp_affine [BorelSpace E] (e : E ≃L[ℝ] E) (c : E)
    (hmp : MeasurePreserving (fun x => e x + c) μ μ) {v : E} {B : Set E} {u g : E → ℝ}
    (h : HasWeakDerivAlong μ (e v) B u g) :
    HasWeakDerivAlong μ v ((fun x => e x + c) ⁻¹' B) (fun x => u (e x + c))
      (fun x => g (e x + c)) := by
  intro φ hφ hc hs
  let S : E ≃ₜ E := (Homeomorph.subRight c).trans e.symm.toHomeomorph
  have hS : ∀ y, S y = e.symm (y - c) := fun _ => rfl
  have hSd : ∀ y, HasFDerivAt S (e.symm : E →L[ℝ] E) y := fun y => by
    exact (e.symm.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const c)).congr_fderiv
      (ContinuousLinearMap.comp_id _)
  have hSc : ContDiff ℝ (⊤ : ℕ∞) S :=
    e.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hψd : ∀ y, fderiv ℝ (φ ∘ S) y (e v) = fderiv ℝ φ (S y) v := fun y => by
    rw [((hφ.differentiable (by simp) _).hasFDerivAt.comp y (hSd y)).fderiv]
    simp
  have key := h (φ ∘ S) (hφ.comp hSc) (hc.comp_homeomorph S) (by
    rw [tsupport_comp_homeomorph]
    intro y hy
    simpa [hS] using hs hy)
  simp only [hψd] at key
  have hme : MeasurableEmbedding (fun x => e x + c) :=
    (e.toHomeomorph.trans (Homeomorph.addRight c)).measurableEmbedding
  have cv := fun F : E → ℝ => hmp.setIntegral_preimage_emb hme F B
  rw [← cv, ← cv] at key
  simpa [hS] using key

/-- **Transport of a weak derivative through a linear automorphism.** -/
theorem HasWeakDerivAlong.comp_linear [BorelSpace E] (e : E ≃L[ℝ] E)
    (hmp : MeasurePreserving e μ μ) {v : E} {B : Set E} {u g : E → ℝ}
    (h : HasWeakDerivAlong μ (e v) B u g) :
    HasWeakDerivAlong μ v (e ⁻¹' B) (fun x => u (e x)) (fun x => g (e x)) := by
  simpa using h.comp_affine e 0 (by simpa using hmp)

omit [NormedSpace ℝ E] in
/-- Against a function with support in `B`, a set integral over `B` is an integral over the
whole space. -/
theorem setIntegral_mul_eq_integral_smul {B : Set E} {φ : E → ℝ} (hs : tsupport φ ⊆ B)
    (f : E → ℝ) : ∫ x in B, f x * φ x ∂μ = ∫ x, φ x • f x ∂μ := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]]
  simp_rw [smul_eq_mul, mul_comm]

/-- `HasWeakDerivAlong` in the integral form of `EllipticPdes.hasWeakLineDerivOn_iff`. -/
theorem hasWeakDerivAlong_iff_integral {v : E} {B : Set E} {u g : E → ℝ} :
    HasWeakDerivAlong μ v B u g ↔
      ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ B →
        ∫ x, fderiv ℝ φ x v • u x ∂μ = -∫ x, φ x • g x ∂μ := by
  refine forall₄_congr fun φ hφ hc hs => ?_
  rw [setIntegral_mul_eq_integral_smul ((tsupport_fderiv_apply_subset ℝ v).trans hs),
    setIntegral_mul_eq_integral_smul hs]

/-- **`HasWeakDerivAlong` is `HasWeakLineDerivOn`.** On an open set, for locally integrable `u`
and `g`, the weak derivative along `v` of this file is the weak derivative of
`EllipticPdes.HasWeakLineDerivOn`. -/
theorem hasWeakDerivAlong_iff_hasWeakLineDerivOn [OpensMeasurableSpace E] {B : Set E}
    (hB : IsOpen B) {v : E} {u g : E → ℝ} (hu : LocallyIntegrableOn u B μ)
    (hg : LocallyIntegrableOn g B μ) :
    HasWeakDerivAlong μ v B u g ↔ HasWeakLineDerivOn ⟨B, hB⟩ v u g μ := by
  rw [hasWeakLineDerivOn_iff, hasWeakDerivAlong_iff_integral]
  exact ⟨fun h => ⟨hu, hg, h⟩, fun h => h.2.2⟩

/-- **Uniqueness of the weak derivative along a direction.** On an open set, two locally
integrable weak derivatives of one function along one direction agree almost everywhere. -/
theorem HasWeakDerivAlong.ae_eq [BorelSpace E] [FiniteDimensional ℝ E] {B : Set E}
    (hB : IsOpen B) {v : E} {u g g' : E → ℝ} (hg : LocallyIntegrableOn g B μ)
    (hg' : LocallyIntegrableOn g' B μ) (h : HasWeakDerivAlong μ v B u g)
    (h' : HasWeakDerivAlong μ v B u g') : g =ᵐ[μ.restrict B] g' :=
  ae_eq_of_forall_integral_smul_eq (Ω := ⟨B, hB⟩) hg hg' fun φ hφ hc hs => neg_inj.1 <|
    (hasWeakDerivAlong_iff_integral.1 h φ hφ hc hs).symm.trans
      (hasWeakDerivAlong_iff_integral.1 h' φ hφ hc hs)

end WeakDeriv

/-- **`HasWeakGradOn` is `HasWeakFDerivOn`.** On an open set, for `u` and the components of
`g` locally integrable, `g` is a weak gradient of `u` exactly when the functional `gradCLM g`
(the Riesz dual of `(g k ·)ₖ`, `gradCLM_eq_toDual`) is the weak Fréchet derivative of `u`. -/
theorem hasWeakGradOn_iff_hasWeakFDerivOn {B : Set (EuclideanSpace ℝ (Fin d))} (hB : IsOpen B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u B volume) (hg : ∀ k, LocallyIntegrableOn (g k) B volume) :
    HasWeakGradOn B u g ↔ HasWeakFDerivOn ⟨B, hB⟩ u (gradCLM g) := by
  classical
  rw [hasWeakGradOn_iff, hasWeakFDerivOn_iff_basis (EuclideanSpace.basisFun (Fin d) ℝ).toBasis hu]
  refine forall_congr' fun k => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, gradCLM_apply_single]
  exact hasWeakDerivAlong_iff_hasWeakLineDerivOn hB hu (hg k)

/-- The Morrey/Hölder exponent `γ = 1 - d/p`, as a `ℝ≥0` (faithful when `p > d`). -/
def morreyExponent (d : ℕ) (p : ℝ) : ℝ≥0 := Real.toNNReal (1 - (d : ℝ) / p)

/-- When `p > d`, the Morrey exponent coerces back to `1 - d/p`. -/
theorem coe_morreyExponent {p : ℝ} (hp : (d : ℝ) < p) (hd : 0 < d) :
    (morreyExponent d p : ℝ) = 1 - (d : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (by positivity) hp
  have : 0 ≤ 1 - (d : ℝ) / p := by
    rw [sub_nonneg, div_le_one hp0]; exact hp.le
  simp [morreyExponent, Real.coe_toNNReal _ this]

end EllipticPdes.Embedding
