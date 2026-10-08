/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Weak derivatives

A function `u : E → F` has weak derivative `g` along `v` on an open set `Ω` when both are locally
integrable on `Ω` and the distributional derivative `∂_{v}` of `u` is the distribution of `g`.
It has weak Fréchet derivative `G : E → E →L[ℝ] F` when this holds along every direction with
`g = (G · v)`. Both are phrased through Mathlib's `Distribution.ofFun` and the line derivative
of distributions, so that uniqueness is `Distribution.ofFun_injective` and linearity is that of
`∂_{v}`.

`E` is any finite-dimensional real normed space where it matters (uniqueness, smooth functions),
`F` any real normed space (complete for uniqueness), `μ` any measure (an additive Haar measure
for the smooth case). The open set is an `Opens E`, which is how Mathlib indexes test functions
and distributions; a set with a proof of openness enters as `⟨Ω, hΩ⟩`.

## Main declarations

* `EllipticPdes.HasWeakLineDerivOn`: weak derivative along one direction.
* `EllipticPdes.HasWeakFDerivOn`: weak Fréchet derivative.
* `EllipticPdes.hasWeakLineDerivOn_iff`: the integration by parts form, against smooth
  compactly supported functions.
* `EllipticPdes.HasWeakLineDerivOn.ae_eq`, `EllipticPdes.HasWeakFDerivOn.ae_eq`: uniqueness
  almost everywhere on `Ω`.
* `EllipticPdes.HasWeakFDerivOn.of_basis`: a weak derivative along each vector of a basis is a
  weak Fréchet derivative.
* `EllipticPdes.hasWeakFDerivOn_fderiv`: a `C¹` function has its derivative as weak derivative.
-/

@[expose] public section

open MeasureTheory TopologicalSpace Set Filter
open scoped Distributions LineDeriv

noncomputable section

namespace EllipticPdes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω Ω' : Opens E} {μ : Measure E} {v w : E} {u u' g g' : E → F} {G G' : E → E →L[ℝ] F}

/-- `g` is the weak derivative of `u` along `v` on the open set `Ω`: `u` and `g` are locally
integrable on `Ω` and the derivative of the distribution of `u` along `v` is the distribution
of `g`. In integral form, `∫ ∂_{v} φ • u ∂μ = -∫ φ • g ∂μ` for every test function `φ` on `Ω`
(`hasWeakLineDerivOn_iff`). -/
def HasWeakLineDerivOn (Ω : Opens E) (v : E) (u g : E → F) (μ : Measure E := by volume_tac) :
    Prop :=
  LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn g Ω μ ∧
    ∂_{v} (Distribution.ofFun Ω u μ ⊤) = Distribution.ofFun Ω g μ ⊤

/-- `G` is the weak Fréchet derivative of `u` on the open set `Ω`: for every direction `v`, the
function `x ↦ G x v` is the weak derivative of `u` along `v`. -/
def HasWeakFDerivOn (Ω : Opens E) (u : E → F) (G : E → E →L[ℝ] F)
    (μ : Measure E := by volume_tac) : Prop :=
  ∀ v, HasWeakLineDerivOn Ω v u (fun x => G x v) μ

/-! ### The integral form -/

/-- The derivative along `v` of the distribution of a locally integrable function, evaluated on
a test function, is minus the integral against the derivative of the test function. -/
theorem lineDerivOp_ofFun_apply (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, ℝ)) :
    ∂_{v} (Distribution.ofFun Ω u μ ⊤) φ = -∫ x, fderiv ℝ φ x v • u x ∂μ := by
  rw [Distribution.lineDerivOp_apply_apply, Distribution.ofFun_apply hu, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hd := (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv (v := v)
  simp [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, hd]

/-- **Weak derivative as integration by parts.** `g` is the weak derivative of `u` along `v` on
`Ω` if and only if both are locally integrable on `Ω` and `∫ ∂_{v} φ • u = -∫ φ • g` for every
smooth function `φ` with compact support in `Ω`. -/
theorem hasWeakLineDerivOn_iff : HasWeakLineDerivOn Ω v u g μ ↔
    LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn g Ω μ ∧
      ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        ∫ x, fderiv ℝ φ x v • u x ∂μ = -∫ x, φ x • g x ∂μ := by
  refine and_congr_right fun hu => and_congr_right fun hg => ?_
  have key : ∀ φ : 𝓓(Ω, ℝ), (∂_{v} (Distribution.ofFun Ω u μ ⊤) φ =
      Distribution.ofFun Ω g μ ⊤ φ ↔ ∫ x, fderiv ℝ φ x v • u x ∂μ = -∫ x, φ x • g x ∂μ) :=
    fun φ => by rw [lineDerivOp_ofFun_apply hu, Distribution.ofFun_apply hg, neg_eq_iff_eq_neg]
  refine ⟨fun h φ hφ hc hs => (key ⟨φ, hφ, hc, hs⟩).1 congr($h _), fun h => ?_⟩
  ext φ
  exact (key φ).2 (h φ φ.contDiff φ.hasCompactSupport φ.tsupport_subset)

/-- The integration by parts identity of a weak derivative, against a smooth function with
compact support in `Ω`. -/
theorem HasWeakLineDerivOn.integral_eq (h : HasWeakLineDerivOn Ω v u g μ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x, fderiv ℝ φ x v • u x ∂μ = -∫ x, φ x • g x ∂μ :=
  (hasWeakLineDerivOn_iff.1 h).2.2 φ hφ hc hs

/-- A weak derivative is locally integrable on `Ω`. -/
theorem HasWeakLineDerivOn.locallyIntegrableOn (h : HasWeakLineDerivOn Ω v u g μ) :
    LocallyIntegrableOn g Ω μ :=
  h.2.1

/-- A function with a weak derivative is locally integrable on `Ω`. -/
theorem HasWeakLineDerivOn.locallyIntegrableOn_fun (h : HasWeakLineDerivOn Ω v u g μ) :
    LocallyIntegrableOn u Ω μ :=
  h.1

/-! ### Uniqueness -/

section Unique

variable [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F]

/-- **Fundamental lemma of the calculus of variations.** Two functions locally integrable on `Ω`
with the same integral against every smooth function of compact support in `Ω` agree almost
everywhere on `Ω`. -/
theorem ae_eq_of_forall_integral_smul_eq (hg : LocallyIntegrableOn g Ω μ)
    (hg' : LocallyIntegrableOn g' Ω μ)
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ x, φ x • g x ∂μ = ∫ x, φ x • g' x ∂μ) : g =ᵐ[μ.restrict Ω] g' := by
  refine Distribution.ofFun_injective (n := ⊤) hg hg' ?_
  ext φ
  rw [Distribution.ofFun_apply hg, Distribution.ofFun_apply hg']
  exact h φ φ.contDiff φ.hasCompactSupport φ.tsupport_subset

/-- **Uniqueness of the weak derivative.** Two weak derivatives of one function along one
direction agree almost everywhere on `Ω`. -/
theorem HasWeakLineDerivOn.ae_eq (h : HasWeakLineDerivOn Ω v u g μ)
    (h' : HasWeakLineDerivOn Ω v u g' μ) : g =ᵐ[μ.restrict Ω] g' :=
  Distribution.ofFun_injective h.2.1 h'.2.1 (h.2.2.symm.trans h'.2.2)

/-- **Uniqueness of the weak Fréchet derivative.** Two weak Fréchet derivatives of one function
agree almost everywhere on `Ω`. -/
theorem HasWeakFDerivOn.ae_eq (h : HasWeakFDerivOn Ω u G μ) (h' : HasWeakFDerivOn Ω u G' μ) :
    G =ᵐ[μ.restrict Ω] G' := by
  let b := Module.finBasis ℝ E
  filter_upwards [ae_all_iff.2 fun i => (h (b i)).ae_eq (h' (b i))] with x hx
  exact ContinuousLinearMap.coe_injective (b.ext fun i => hx i)

end Unique

/-! ### Algebraic operations -/

/-- A weak derivative is unchanged when `u` and `g` change on a null set of `Ω`. -/
theorem HasWeakLineDerivOn.congr_ae (h : HasWeakLineDerivOn Ω v u g μ)
    (hu : u =ᵐ[μ.restrict Ω] u') (hg : g =ᵐ[μ.restrict Ω] g') :
    HasWeakLineDerivOn Ω v u' g' μ :=
  ⟨h.1.congr hu, h.2.1.congr hg, by
    rw [← Distribution.ofFun_congr_ae hu, ← Distribution.ofFun_congr_ae hg]; exact h.2.2⟩

/-- A weak Fréchet derivative is unchanged when `u` and `G` change on a null set of `Ω`. -/
theorem HasWeakFDerivOn.congr_ae (h : HasWeakFDerivOn Ω u G μ)
    (hu : u =ᵐ[μ.restrict Ω] u') (hG : G =ᵐ[μ.restrict Ω] G') : HasWeakFDerivOn Ω u' G' μ :=
  fun v => (h v).congr_ae hu (hG.mono fun x hx => by simp [hx])

/-- The zero function has zero weak derivative. -/
theorem hasWeakLineDerivOn_zero : HasWeakLineDerivOn Ω v (0 : E → F) 0 μ :=
  ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, by simp⟩

/-- The zero function has zero weak Fréchet derivative. -/
theorem hasWeakFDerivOn_zero : HasWeakFDerivOn Ω (0 : E → F) 0 μ :=
  fun _ => hasWeakLineDerivOn_zero

/-- Weak derivatives add. -/
theorem HasWeakLineDerivOn.add (h : HasWeakLineDerivOn Ω v u g μ)
    (h' : HasWeakLineDerivOn Ω v u' g' μ) : HasWeakLineDerivOn Ω v (u + u') (g + g') μ :=
  ⟨h.1.add h'.1, h.2.1.add h'.2.1, by
    rw [Distribution.ofFun_add h.1 h'.1, Distribution.ofFun_add h.2.1 h'.2.1,
      LineDeriv.lineDerivOp_add, h.2.2, h'.2.2]⟩

/-- Weak Fréchet derivatives add. -/
theorem HasWeakFDerivOn.add (h : HasWeakFDerivOn Ω u G μ) (h' : HasWeakFDerivOn Ω u' G' μ) :
    HasWeakFDerivOn Ω (u + u') (G + G') μ :=
  fun v => (h v).add (h' v)

/-- A constant multiple of a function has the same multiple of its weak derivative. -/
theorem HasWeakLineDerivOn.const_smul (h : HasWeakLineDerivOn Ω v u g μ) (c : ℝ) :
    HasWeakLineDerivOn Ω v (c • u) (c • g) μ :=
  ⟨h.1.smul c, h.2.1.smul c, by
    rw [Distribution.ofFun_smul, Distribution.ofFun_smul, LineDeriv.lineDerivOp_smul, h.2.2]⟩

/-- A constant multiple of a function has the same multiple of its weak Fréchet derivative. -/
theorem HasWeakFDerivOn.const_smul (h : HasWeakFDerivOn Ω u G μ) (c : ℝ) :
    HasWeakFDerivOn Ω (c • u) (c • G) μ :=
  fun v => (h v).const_smul c

/-- The negative of a function has the negative weak derivative. -/
theorem HasWeakLineDerivOn.neg (h : HasWeakLineDerivOn Ω v u g μ) :
    HasWeakLineDerivOn Ω v (-u) (-g) μ := by
  simpa using h.const_smul (-1)

/-- The negative of a function has the negative weak Fréchet derivative. -/
theorem HasWeakFDerivOn.neg (h : HasWeakFDerivOn Ω u G μ) : HasWeakFDerivOn Ω (-u) (-G) μ :=
  fun v => (h v).neg

/-- Weak derivatives subtract. -/
theorem HasWeakLineDerivOn.sub (h : HasWeakLineDerivOn Ω v u g μ)
    (h' : HasWeakLineDerivOn Ω v u' g' μ) : HasWeakLineDerivOn Ω v (u - u') (g - g') μ := by
  simpa [sub_eq_add_neg] using h.add h'.neg

/-- Weak Fréchet derivatives subtract. -/
theorem HasWeakFDerivOn.sub (h : HasWeakFDerivOn Ω u G μ) (h' : HasWeakFDerivOn Ω u' G' μ) :
    HasWeakFDerivOn Ω (u - u') (G - G') μ :=
  fun v => (h v).sub (h' v)

/-- Finite sums of functions with weak derivatives have the sum of the weak derivatives. -/
theorem HasWeakLineDerivOn.sum {ι : Type*} (s : Finset ι) {u g : ι → E → F}
    (h : ∀ i ∈ s, HasWeakLineDerivOn Ω v (u i) (g i) μ) :
    HasWeakLineDerivOn Ω v (∑ i ∈ s, u i) (∑ i ∈ s, g i) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasWeakLineDerivOn_zero
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Finite sums of functions with weak Fréchet derivatives have the sum of the derivatives. -/
theorem HasWeakFDerivOn.sum {ι : Type*} (s : Finset ι) {u : ι → E → F} {G : ι → E → E →L[ℝ] F}
    (h : ∀ i ∈ s, HasWeakFDerivOn Ω (u i) (G i) μ) :
    HasWeakFDerivOn Ω (∑ i ∈ s, u i) (∑ i ∈ s, G i) μ := fun v => by
  convert HasWeakLineDerivOn.sum s fun i hi => h i hi v using 1
  ext x
  simp

/-! ### Dependence on the direction and on the set -/

/-- Along the zero direction, the weak derivative of a locally integrable function is zero. -/
theorem hasWeakLineDerivOn_zero_dir (hu : LocallyIntegrableOn u Ω μ) :
    HasWeakLineDerivOn Ω 0 u 0 μ :=
  ⟨hu, locallyIntegrableOn_zero, by simp⟩

/-- Weak derivatives add along a sum of directions. -/
theorem HasWeakLineDerivOn.add_dir (h : HasWeakLineDerivOn Ω v u g μ)
    (h' : HasWeakLineDerivOn Ω w u g' μ) : HasWeakLineDerivOn Ω (v + w) u (g + g') μ :=
  ⟨h.1, h.2.1.add h'.2.1, by
    rw [Distribution.ofFun_add h.2.1 h'.2.1, ← h.2.2, ← h'.2.2]
    exact LineDeriv.lineDerivOp_left_add v w _⟩

/-- A weak derivative scales with the direction. -/
theorem HasWeakLineDerivOn.smul_dir (h : HasWeakLineDerivOn Ω v u g μ) (c : ℝ) :
    HasWeakLineDerivOn Ω (c • v) u (c • g) μ :=
  ⟨h.1, h.2.1.smul c, by
    rw [Distribution.ofFun_smul, ← h.2.2]
    exact LineDeriv.lineDerivOp_left_smul c v _⟩

/-- **Weak derivatives along a basis.** If `x ↦ G x (b i)` is the weak derivative of `u` along
each vector `b i` of a finite basis, then `G` is the weak Fréchet derivative of `u`. -/
theorem HasWeakFDerivOn.of_basis {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ E)
    (hu : LocallyIntegrableOn u Ω μ)
    (h : ∀ i, HasWeakLineDerivOn Ω (b i) u (fun x => G x (b i)) μ) :
    HasWeakFDerivOn Ω u G μ := by
  intro v
  classical
  have := Fintype.ofFinite ι
  have hsum : ∀ s : Finset ι, HasWeakLineDerivOn Ω (∑ i ∈ s, b.repr v i • b i) u
      (∑ i ∈ s, b.repr v i • fun x => G x (b i)) μ := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using hasWeakLineDerivOn_zero_dir hu
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact ((h a).smul_dir _).add_dir ih
  have hv := hsum Finset.univ
  rw [b.sum_repr v] at hv
  convert hv using 1
  ext x
  have := congrArg (G x) (b.sum_repr v)
  rw [map_sum] at this
  simpa [map_smul] using this.symm

/-- A weak Fréchet derivative is a weak derivative along a basis, and conversely. -/
theorem hasWeakFDerivOn_iff_basis {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ E)
    (hu : LocallyIntegrableOn u Ω μ) :
    HasWeakFDerivOn Ω u G μ ↔ ∀ i, HasWeakLineDerivOn Ω (b i) u (fun x => G x (b i)) μ :=
  ⟨fun h i => h (b i), HasWeakFDerivOn.of_basis b hu⟩

/-- A weak derivative on `Ω` is a weak derivative on any smaller open set. -/
theorem HasWeakLineDerivOn.mono (h : HasWeakLineDerivOn Ω v u g μ) (hΩ : Ω' ≤ Ω) :
    HasWeakLineDerivOn Ω' v u g μ := by
  obtain ⟨hu, hg, hint⟩ := hasWeakLineDerivOn_iff.1 h
  exact hasWeakLineDerivOn_iff.2 ⟨hu.mono_set hΩ, hg.mono_set hΩ,
    fun φ hφ hc hs => hint φ hφ hc (hs.trans hΩ)⟩

/-- A weak Fréchet derivative on `Ω` is one on any smaller open set. -/
theorem HasWeakFDerivOn.mono (h : HasWeakFDerivOn Ω u G μ) (hΩ : Ω' ≤ Ω) :
    HasWeakFDerivOn Ω' u G μ :=
  fun v => (h v).mono hΩ

/-! ### Smooth functions -/

section Smooth

variable [BorelSpace E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A function locally integrable on `s`, multiplied by a continuous scalar function with
compact support in `s`, is integrable. -/
theorem _root_.MeasureTheory.LocallyIntegrableOn.integrable_smul_of_tsupport_subset {s : Set E}
    (hu : LocallyIntegrableOn u s μ) {φ : E → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ s) : Integrable (fun x => φ x • u x) μ := by
  refine (integrableOn_iff_integrable_of_support_subset fun x hx => ?_).1
    ((hu.integrableOn_compact_subset hs hc).continuousOn_smul hφ.continuousOn hc)
  exact subset_tsupport φ fun h0 => hx (by simp [h0])

omit [BorelSpace E] in
/-- **Product of a weak derivative with a smooth function.** If `g` is the weak derivative of
`u` along `v` on `Ω` and `ψ` is smooth, then `ψ • u` has weak derivative
`ψ • g + ∂_{v} ψ • u`. -/
theorem HasWeakLineDerivOn.smul_left (h : HasWeakLineDerivOn Ω v u g μ) {ψ : E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    HasWeakLineDerivOn Ω v (fun x => ψ x • u x) (fun x => ψ x • g x + fderiv ℝ ψ x v • u x) μ := by
  obtain ⟨hu, hg, hint⟩ := hasWeakLineDerivOn_iff.1 h
  have hψd : Continuous fun x => fderiv ℝ ψ x v :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hloc : ∀ {f : E → ℝ}, Continuous f → ∀ {w : E → F}, LocallyIntegrableOn w Ω μ →
      LocallyIntegrableOn (fun x => f x • w x) Ω μ := fun hf w hw =>
    (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2 fun K hK hKc =>
      (hw.integrableOn_compact_subset hK hKc).continuousOn_smul hf.continuousOn hKc
  refine hasWeakLineDerivOn_iff.2 ⟨hloc hψ.continuous hu,
    (hloc hψ.continuous hg).add (hloc hψd hu), fun φ hφ hc hs => ?_⟩
  have hφψ := hint (φ * ψ) (hφ.mul hψ) hc.mul_right (tsupport_mul_subset_left.trans hs)
  have hfd : ∀ x, fderiv ℝ (φ * ψ) x v = fderiv ℝ φ x v * ψ x + φ x * fderiv ℝ ψ x v :=
    fun x => by
      rw [fderiv_mul (hφ.differentiable (by simp) x) (hψ.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
  have hd' : Continuous fun x => fderiv ℝ (φ * ψ) x v :=
    ((hφ.mul hψ).continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 := hu.integrable_smul_of_tsupport_subset hd' (hc.mul_right.fderiv_apply (𝕜 := ℝ) v)
    ((tsupport_fderiv_apply_subset ℝ v).trans (tsupport_mul_subset_left.trans hs))
  have i2 : Integrable (fun x => (φ x * fderiv ℝ ψ x v) • u x) μ :=
    hu.integrable_smul_of_tsupport_subset (hφ.continuous.mul hψd) hc.mul_right
    (tsupport_mul_subset_left.trans hs)
  have i3 : Integrable (fun x => (φ * ψ) x • g x) μ :=
    hg.integrable_smul_of_tsupport_subset (hφ.continuous.mul hψ.continuous)
    hc.mul_right (tsupport_mul_subset_left.trans hs)
  have e1 : ∫ x, fderiv ℝ φ x v • ψ x • u x ∂μ =
      (∫ x, fderiv ℝ (φ * ψ) x v • u x ∂μ) - ∫ x, (φ x * fderiv ℝ ψ x v) • u x ∂μ := by
    rw [← integral_sub i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [hfd, add_smul, smul_smul])
  have e2 : ∫ x, φ x • (ψ x • g x + fderiv ℝ ψ x v • u x) ∂μ =
      (∫ x, (φ * ψ) x • g x ∂μ) + ∫ x, (φ x * fderiv ℝ ψ x v) • u x ∂μ := by
    rw [← integral_add i3 i2]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [smul_add, smul_smul])
  rw [e1, e2, hφψ]
  abel

omit [BorelSpace E] in
/-- **Product of a weak Fréchet derivative with a smooth function.** If `G` is the weak Fréchet
derivative of `u` on `Ω` and `ψ` is smooth, then `ψ • u` has weak Fréchet derivative
`ψ • G + Dψ ⊗ u`. -/
theorem HasWeakFDerivOn.smul_left (h : HasWeakFDerivOn Ω u G μ) {ψ : E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    HasWeakFDerivOn Ω (fun x => ψ x • u x)
      (fun x => ψ x • G x + (fderiv ℝ ψ x).smulRight (u x)) μ :=
  fun v => by simpa using (h v).smul_left hψ

variable [μ.IsAddHaarMeasure]

/-- **A `C¹` function has its derivative as weak derivative.** On an open set where `u` is
continuously differentiable, `fderiv ℝ u` is the weak Fréchet derivative of `u`. -/
theorem hasWeakFDerivOn_fderiv (hu : ContDiffOn ℝ 1 u Ω) :
    HasWeakFDerivOn Ω u (fderiv ℝ u) μ := by
  intro v
  have hd : ∀ x ∈ Ω, HasFDerivAt u (fderiv ℝ u x) x := fun x hx =>
    ((hu.differentiableOn one_ne_zero x hx).differentiableAt (Ω.isOpen.mem_nhds hx)).hasFDerivAt
  have hui : LocallyIntegrableOn u Ω μ := hu.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hgi : LocallyIntegrableOn (fun x => fderiv ℝ u x v) Ω μ :=
    ((hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).clm_apply
      continuousOn_const).locallyIntegrableOn Ω.isOpen.measurableSet
  refine hasWeakLineDerivOn_iff.2 ⟨hui, hgi, fun φ hφ hc hs => ?_⟩
  have hφd : Continuous fun x => fderiv ℝ φ x v :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (B := .lsmul ℝ ℝ)
    (hui.integrable_smul_of_tsupport_subset hφd (hc.fderiv_apply (𝕜 := ℝ) v)
      ((tsupport_fderiv_apply_subset ℝ v).trans hs))
    (hgi.integrable_smul_of_tsupport_subset hφ.continuous hc hs)
    (hui.integrable_smul_of_tsupport_subset hφ.continuous hc hs)
    (fun x _ => (hφ.differentiable (by simp) x).hasFDerivAt) fun x hx => hd x (hs hx)
  simp only [ContinuousLinearMap.lsmul_apply] at this
  rw [this, neg_neg]

end Smooth

end EllipticPdes
