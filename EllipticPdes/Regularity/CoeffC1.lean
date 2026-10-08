/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Coefficients
public import EllipticPdes.Regularity.DifferenceQuotient
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# `C¹` coefficients and the coefficient difference-quotient bound

The interior `H²` estimate (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1;
Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Thm 8.8)
reads the hypothesis `aᵢⱼ ∈ C¹` only through one quantitative consequence: the difference
quotient of each coefficient entry is uniformly bounded by the sup of its gradient. This file
bundles the hypothesis as the structure `IsC1Coeff`, a mixin on top of `EllipticCoeff`, and
proves the coefficient difference-quotient bound `abs_diffQuot_coeff_le` by the segment
mean-value inequality.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace NNReal

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- A `C¹` ellipticity bundle: the coefficient matrix is continuously differentiable with a
global bound `A₁` on the first derivatives of every entry. Faithful to `aᵢⱼ ∈ C¹` for the
interior estimate, where only `a ∈ C¹(closure W)` with `W ⋐ Ω` bounded matters, so
`A₁ < ∞`. -/
structure IsC1Coeff (A : EllipticCoeff d) where
  /-- Every coefficient entry is continuously differentiable. -/
  contDiff : ∀ i j, ContDiff ℝ 1 (fun x => A.a x i j)
  /-- The uniform bound on the first derivatives of every entry. -/
  A1 : ℝ
  /-- `A1` is nonnegative. -/
  A1_nonneg : 0 ≤ A1
  /-- The Fréchet derivative of every coefficient entry is bounded by `A1` at every point. -/
  grad_bdd : ∀ i j, ∀ x, ‖fderiv ℝ (fun y => A.a y i j) x‖ ≤ A1

/-- **Difference quotient of a Lipschitz function.** `|(f(x + h eₖ) - f x)/h| ≤ K` for every
`h ≠ 0` when `f` is `K`-Lipschitz. -/
theorem abs_diffQuot_le_of_lipschitzWith {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (k : Fin d) {h : ℝ} (hh : h ≠ 0) (x : EuclideanSpace ℝ (Fin d)) :
    |(f (x + hshift k h) - f x) / h| ≤ K := by
  have hn : ‖hshift k h‖ = |h| := by simp [hshift, norm_smul]
  have := hf.dist_le_mul (x + hshift k h) x
  rw [Real.dist_eq, dist_eq_norm, show x + hshift k h - x = hshift k h by abel, hn] at this
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hh)]
  exact this

/-- The coefficient difference quotient is uniformly bounded: for the `(i, j)` coefficient
entry, `|Dₖʰ aᵢⱼ(x)| ≤ A₁` for every `x` and every `h ≠ 0`. This is the pointwise
commutator bound used in the master interior estimate to control the coefficient-
difference-quotient term `∑ ∫ (Dₖʰ aᵢⱼ) ∂ᵢu · ∂ⱼ(ζ² Dₖʰ u)` (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1). -/
theorem IsC1Coeff.abs_diffQuot_coeff_le {A : EllipticCoeff d} (hA : IsC1Coeff A)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) (x : EuclideanSpace ℝ (Fin d)) :
    |(A.a (x + hshift k h) i j - A.a x i j) / h| ≤ hA.A1 :=
  abs_diffQuot_le_of_lipschitzWith (K := ⟨hA.A1, hA.A1_nonneg⟩)
    (lipschitzWith_of_nnnorm_fderiv_le (fun y => (hA.contDiff i j).differentiable_one y)
      fun y => by exact_mod_cast hA.grad_bdd i j y) k hh x

end EllipticPdes.Regularity
