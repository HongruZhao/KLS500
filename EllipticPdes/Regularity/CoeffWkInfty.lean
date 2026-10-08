/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Coefficients
public import EllipticPdes.Regularity.CoeffCk

/-!
# `W^{k,∞}` coefficients

Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem VIII.3.2
(*Higher Interior Regularity*, p. 65) runs the induction over `a_{ij} ∈ W^{k+1,∞}(Ω)` and
`b_i, c ∈ W^{k,∞}(Ω)`, where Evans, *Partial Differential Equations* (2nd ed.), §6.3.1,
Theorem 2 asks for `C^{m+1}`. The development here asks `W^{k+1,∞}` for `a_{ij}` and
`W^{k,∞}` for `b_i, c` (`higher_interior_regularity`). This file states the hypothesis: weak
derivatives up to order `k`, each essentially bounded, with no continuity assumed anywhere.

## Choice of a new weak-derivative predicate

`HasWeakDerivOn` is typed on `Lp ℝ 2 (volume.restrict V)` classes, which suits a solution on a
bounded domain. A coefficient is a bounded measurable function on all of `EuclideanSpace ℝ (Fin
d)`, and on an unbounded domain such a function need not be `L²`, so it has no `Lp 2` class to
represent it. `HasWeakPartial` below is the same integration-by-parts identity stated for plain
functions, which is where a locally integrable coefficient lives.

## Indexing of the derivative family

The iterated derivative is indexed by a `List (Fin d)` of directions rather than by a
multi-index in `Fin d →₀ ℕ`. Guo's proof expands `D^α` through the Leibniz rule over
`β ≤ α`, and both indexings support that; a list is chosen because one step of the recursion
is `cons`, matching `D_step`, whereas a finitely-supported function would need the order of
differentiation to be quotiented out before the recursion could be stated. Equality of mixed
partials is a theorem about the family rather than part of its definition, so nothing here
presumes it.

The family is data, not an existential: `D α i j` names the chosen representative of the
order-`α.length` derivative of the `(i,j)` entry. `D_nil` pins the empty list to the
coefficient itself and `D_step` makes each successive entry a weak derivative of its parent.

## Main declarations

* `HasWeakPartial`: the weak partial derivative of a plain function.
* `IsWkInftyCoeff`: Guo's coefficient hypothesis at order `k`.
* `IsWkInftyCoeff.mono`: an order-`k` bundle is an order-`l` bundle for every `l ≤ k`.

## Relation to the classical hypotheses

`IsCkCoeff.toIsWkInftyCoeff` (in `CoeffBridge`) shows a `Cᵏ` bundle to be a `W^{k,∞}` bundle, and
`IsLipCoeff.toIsWkInftyCoeff` (in `CoeffLipWeakGrad`) does the same for a Lipschitz bundle. The
converse for `k = 1` is the statement that a `W^{1,∞}` function has a Lipschitz representative,
which Mathlib does not have. Rademacher's theorem
(`LipschitzWith.ae_differentiableAt`) is the opposite direction.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- `f'` is the weak `k`-th partial derivative of `f`: integration by parts against every
smooth compactly supported test function holds with no boundary term. Stated for plain
functions, so that a bounded measurable coefficient on `EuclideanSpace ℝ (Fin d)` is in
scope where the `Lp 2`-typed `HasWeakDerivOn` is not. -/
def HasWeakPartial (k : Fin d) (f f' : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∫ x, f x * partialD k φ x = - ∫ x, f' x * φ x

/-- A `W^{k,∞}` ellipticity bundle, in the sense of Guo, *Partial Differential Equations I and
II* (Course Lecture Notes), Theorem VIII.3.2 (p. 65): every coefficient entry has weak
derivatives up to order `k`, each measurable and essentially bounded, with no continuity
assumed. The derivative family is indexed by a list of directions, one `cons` per
differentiation. -/
structure IsWkInftyCoeff (A : EllipticCoeff d) (k : ℕ) where
  /-- The chosen representative of the iterated weak derivative of the `(i,j)` entry along a
  list of directions. -/
  D : List (Fin d) → Fin d → Fin d → EuclideanSpace ℝ (Fin d) → ℝ
  /-- The empty list of directions is the coefficient entry itself. -/
  D_nil : ∀ i j, D [] i j = fun x => A.a x i j
  /-- Every entry of the family is measurable. -/
  D_meas : ∀ i j α, α.length ≤ k → Measurable (D α i j)
  /-- Each successive entry is a weak partial derivative of its parent, up to order `k`. -/
  D_step : ∀ i j (l : Fin d) (α : List (Fin d)), α.length < k →
    HasWeakPartial l (D α i j) (D (l :: α) i j)
  /-- The uniform bound on the derivatives of each order. Only the values at `m ≤ k` are
  constrained by `ess_bdd`. -/
  bound : ℕ → ℝ
  /-- Every bound is nonnegative. -/
  bound_nonneg : ∀ m, 0 ≤ bound m
  /-- Each derivative of order `m ≤ k` is bounded by `bound m` almost everywhere. The bound
  is essential rather than pointwise, which is what `W^{k,∞}` asserts. -/
  ess_bdd : ∀ i j α, α.length ≤ k →
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |D α i j x| ≤ bound α.length

namespace IsWkInftyCoeff

variable {A : EllipticCoeff d} {k l : ℕ}

/-- An order-`k` bundle is an order-`l` bundle for every `l ≤ k`: the family and its bounds
are inherited, and each hypothesis is asked of fewer orders. -/
def mono (hA : IsWkInftyCoeff A k) (hlk : l ≤ k) : IsWkInftyCoeff A l where
  D := hA.D
  D_nil := hA.D_nil
  D_meas i j α hα := hA.D_meas i j α (hα.trans hlk)
  D_step i j m α hα := hA.D_step i j m α (lt_of_lt_of_le hα hlk)
  bound := hA.bound
  bound_nonneg := hA.bound_nonneg
  ess_bdd i j α hα := hA.ess_bdd i j α (hα.trans hlk)

end IsWkInftyCoeff

end EllipticPdes.Regularity
