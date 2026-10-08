/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Bounded measurable coefficients acting on `L²` (general elliptic operator)

To pass from the Poisson form `∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫` to the general divergence-form operator
`L u = -Dⱼ(aᵢⱼ Dᵢu) + bᵢ Dᵢu + c u` we need to *multiply* an `L²` gradient component by a
bounded measurable coefficient and still land in `L²`. This file provides

* `mulCoeffL` : a bounded measurable scalar `f` (`|f| ≤ M`) acting on `L²(Ω)` as a
  continuous linear map `g ↦ [f · g]`, the Hölder action of `L^∞` on `L²`;
* `mulCoeffL_coeFn` : its pointwise a.e. representative `x ↦ f x · g x`;
* `EllipticCoeff` : the bundle of a measurable, bounded, uniformly elliptic coefficient
  matrix `a` (Evans §6.1.1: `∑ aᵢⱼ ξᵢ ξⱼ ≥ λ |ξ|²`).

This mirrors, on the scalar `PiLp` encoding of `Sobolev/Basic.lean`, the coefficient action
`coeffMulLpL` that DeGiorgi (`WeakFormulation/CoefficientOperator.lean`) builds on the
vector-valued `L²(Ω; E)` encoding.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Pointwise multiplication by a bounded measurable coefficient -/

/-- A bounded measurable scalar function is a class of `L^∞(Ω)`. -/
def coeffLinfty {Ω : Set (EuclideanSpace ℝ (Fin d))} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) :
    Lp ℝ ∞ (volume.restrict Ω) :=
  (memLp_top_of_bound hf.aestronglyMeasurable M (hM.mono fun _ hx => by
    rwa [Real.norm_eq_abs])).toLp f

/-- A bounded measurable scalar `f` (`|f| ≤ M`) acting on `L²(Ω)` by pointwise
multiplication, as a continuous linear map: the Hölder action of `L^∞` on `L²`. -/
def mulCoeffL {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) : L2D Ω →L[ℝ] L2D Ω :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).holderL (volume.restrict Ω) ∞ 2 2
    (coeffLinfty hf hM)

/-- A representative of `coeffLinfty hf hM` is `f` almost everywhere. -/
lemma coeFn_coeffLinfty {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) :
    ⇑(coeffLinfty hf hM) =ᵐ[volume.restrict Ω] f :=
  MemLp.coeFn_toLp _

/-- The pointwise a.e. representative of the coefficient action. -/
lemma mulCoeffL_coeFn {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (g : L2D Ω) :
    mulCoeffL hf hM g =ᵐ[volume.restrict Ω] fun x => f x * (g x : ℝ) := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ))
    (coeffLinfty hf hM) g (r := 2), coeFn_coeffLinfty hf hM] with x h1 h2
  rw [mulCoeffL, ContinuousLinearMap.holderL_apply_apply, h1, h2]
  rfl

/-- Operator-norm bound for the coefficient action: `‖[f · g]‖ ≤ M ‖g‖`. -/
lemma norm_mulCoeffL_le {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (g : L2D Ω) :
    ‖mulCoeffL hf hM g‖ ≤ M * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulCoeffL_coeFn hf hM g, hM] with x hx hMx
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hMx (abs_nonneg _)

/-- The inner product of the coefficient action against `h` is the integral of the triple
product `∫_Ω f · g · h`. -/
lemma inner_mulCoeffL_eq {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (g h : L2D Ω) :
    ⟪mulCoeffL hf hM g, h⟫ = ∫ x in Ω, f x * (g x : ℝ) * (h x : ℝ) := by
  rw [L2.real_inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [mulCoeffL_coeFn hf hM g] with a ha
  rw [ha]

/-! ### Uniformly elliptic coefficient matrices (Evans §6.1.1) -/

/-- A measurable, bounded coefficient matrix `a` that is **uniformly elliptic** with
ellipticity constant `lam > 0` and sup bound `Λ`: `∑ᵢⱼ aᵢⱼ(x) ξᵢ ξⱼ ≥ lam · |ξ|²` and
`|aᵢⱼ(x)| ≤ Λ` for almost every `x` (Evans §6.1.1). The bounds hold `volume`-almost
everywhere on `ℝᵈ`, so they hold almost everywhere on every domain `Ω`.

The matrix need not be symmetric: `elliptic` constrains the quadratic form
`ξ ↦ ∑ᵢⱼ aᵢⱼ ξᵢ ξⱼ`, which the antisymmetric part annihilates, and `bdd` constrains the
entries one at a time. -/
structure EllipticCoeff (d : ℕ) where
  /-- The coefficient matrix entries. -/
  a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ
  /-- Ellipticity constant. -/
  lam : ℝ
  /-- Uniform sup bound on the entries. -/
  Λ : ℝ
  /-- The ellipticity constant is strictly positive. -/
  lam_pos : 0 < lam
  /-- The sup bound is nonnegative. -/
  Λ_nonneg : 0 ≤ Λ
  /-- Every entry of the matrix is measurable. -/
  measurable : ∀ i j, Measurable (fun x => a x i j)
  /-- Every entry is bounded by `Λ` almost everywhere. -/
  bdd : ∀ i j, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x i j| ≤ Λ
  /-- The quadratic form of `a x` dominates `lam · |ξ|²` for almost every `x`. -/
  elliptic : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
    ∀ ξ : Fin d → ℝ, lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j

namespace EllipticCoeff

variable (A : EllipticCoeff d)

/-- The `(i, j)` coefficient acting on `L²(Ω)`. -/
def actL {Ω : Set (EuclideanSpace ℝ (Fin d))} (i j : Fin d) : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL (A.measurable i j) (ae_restrict_of_ae (A.bdd i j))

/-- Simp lemma: `A.actL i j g` has pointwise representative `x ↦ A.a x i j · g x` a.e. -/
@[simp] lemma actL_coeFn {Ω : Set (EuclideanSpace ℝ (Fin d))} (i j : Fin d) (g : L2D Ω) :
    A.actL i j g =ᵐ[volume.restrict Ω] fun x => A.a x i j * (g x : ℝ) :=
  mulCoeffL_coeFn _ _ g

/-- `⟪A.actL i j g, h⟫ = ∫_Ω A.a x i j · g x · h x`. -/
lemma inner_actL_eq {Ω : Set (EuclideanSpace ℝ (Fin d))} (i j : Fin d) (g h : L2D Ω) :
    ⟪A.actL i j g, h⟫ = ∫ x in Ω, A.a x i j * (g x : ℝ) * (h x : ℝ) :=
  inner_mulCoeffL_eq _ _ g h

/-- Operator-norm bound: `‖A.actL i j g‖ ≤ Λ · ‖g‖`. -/
lemma norm_actL_le {Ω : Set (EuclideanSpace ℝ (Fin d))} (i j : Fin d) (g : L2D Ω) :
    ‖A.actL i j g‖ ≤ A.Λ * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

end EllipticCoeff

end EllipticPdes.Sobolev
