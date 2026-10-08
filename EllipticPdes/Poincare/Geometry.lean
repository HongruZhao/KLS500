/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Poincare.Domain
public import EllipticPdes.Sobolev.Basic
public import EllipticPdes.Form.BilinearForm

/-!
# Wiring the test-function Poincaré bound from the box geometry

The density Poincaré inequality `poincare_H01` and the coercivity theorems
(`EllipticCoeff.bilin_coercive`) consume the bound

  `‖(h.testGraph 0 : L2D Ω)‖² ≤ C_P · ∑ᵢ ‖h.testGraph i.succ‖²`   (`hbase`)

as a hypothesis phrased through the **graph coordinates** (abstract `L²` norms). This file
discharges it from the **domain Poincaré inequality** `poincare_domain`, which lives at the
level of box integrals `∫_Ω φ²` and `∫_Ω (∂ᵢφ)²`. Two bridges do the work:

* `norm_testGraph_zero_sq_eq` / `norm_testGraph_succ_sq_eq`: the squared `L²` norm of a graph
  coordinate **is** the box integral of the corresponding classical quantity
  (`‖tg 0‖² = ∫_Ω φ²`, `‖tg i.succ‖² = ∫_Ω (∂ᵢφ)²`), via the `L²` self-inner product.
* `poincare_testfn`: feeding the per-direction slice bounds `∫_Ω φ² ≤ C ∫_Ω (∂ᵢφ)²` (the
  slab Poincaré inequality `integral_sq_le_of_tsupport_subset_slab`) into `poincare_domain`'s
  averaging yields `hbase` with `C_P = C / d`. For a box of maximal side `L` the slice bound
  holds with `C = L²/2`, giving the diameter constant `C_P = L²/(2d)`.

The per-direction slice bound on a coordinate box is `slice_bound_euclBox`
(`Poincare/BoxSlice.lean`); this file turns it into the abstract-norm `hbase` the Hilbert-space
layer wants.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Poincare

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- The squared `L²` norm of the function coordinate of a test-function graph is the box
integral of `φ²`. -/
lemma norm_testGraph_zero_sq_eq {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) :
    ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 = ∫ x in Ω, (φ x) ^ 2 := by
  rw [IsTestFn.testGraph_zero, L2.norm_sq_eq_integral_sq]
  exact integral_congr_ae (by filter_upwards [h.coeFn_testCls] with x hx using by rw [hx])

/-- The squared `L²` norm of the `i`-th gradient coordinate of a test-function graph is the
box integral of `(∂ᵢφ)²`. -/
lemma norm_testGraph_succ_sq_eq {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) (i : Fin d) :
    ‖(h.testGraph i.succ : L2D Ω)‖ ^ 2 = ∫ x in Ω, (partialD i φ x) ^ 2 := by
  rw [IsTestFn.testGraph_succ, L2.norm_sq_eq_integral_sq]
  exact integral_congr_ae (by filter_upwards [h.coeFn_partialCls i] with x hx using by rw [hx])

/-- **Test-function Poincaré bound from box geometry.** If on the box `Ω` every test
function obeys the per-direction slice bound `∫_Ω φ² ≤ C ∫_Ω (∂ᵢφ)²` (the slab Poincaré
inequality `integral_sq_le_of_tsupport_subset_slab`), then it obeys the graph-coordinate bound
`hbase` with Poincaré constant `C_P = C / d`. This is `poincare_domain` (averaging the `d`
directions) re-expressed through the `L²` self-inner products. -/
theorem poincare_testfn {Ω : Set (EuclideanSpace ℝ (Fin d))} (hd : 0 < d) (C : ℝ)
    (hslice : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (_h : IsTestFn Ω φ) (i : Fin d),
      ∫ x in Ω, (φ x) ^ 2 ≤ C * ∫ x in Ω, (partialD i φ x) ^ 2)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) :
    ‖(h.testGraph 0 : L2D Ω)‖ ^ 2
      ≤ (C / d) * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2 := by
  rw [norm_testGraph_zero_sq_eq h]
  refine le_trans (poincare_domain (μ := volume) (Ω := Ω) hd (u := φ)
    (d := fun i => partialD i φ) (c := fun _ => C) (fun i => hslice h i)) ?_
  have hconv : ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2
      = ∑ i : Fin d, ∫ x in Ω, (partialD i φ x) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => norm_testGraph_succ_sq_eq h i)
  rw [hconv, ← Finset.mul_sum]
  apply le_of_eq
  ring

end EllipticPdes.Poincare
