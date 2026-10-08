/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import EllipticPdes.Sobolev.Basic

/-!
# Translation on `L²(ℝⁿ)`

`transL2 h` is translation by `h` as a linear isometry of `L²(ℝⁿ)`. It is the action of
`DomAddAct.mk h` on `Lp`, bundled as a linear isometry.

## Main declarations

* `MeasureTheory.EucL2`: `L²(ℝⁿ)` with Lebesgue measure.
* `MeasureTheory.transL2`: translation as a linear isometry.
* `MeasureTheory.transL2_apply`: `transL2 h g` is `DomAddAct.mk h +ᵥ g`.
* `MeasureTheory.norm_sq_transL2_sub`: the squared norm of a translation difference.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace MeasureTheory

/-- `L²(ℝⁿ)` with Lebesgue measure. -/
abbrev EucL2 (n : ℕ) := Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))

variable {n : ℕ}

/-- The squared `L²` norm is the integral of the square. -/
theorem norm_sq_eq_integral_sq (g : EucL2 n) : ‖g‖ ^ 2 = ∫ x, (g x) ^ 2 :=
  L2.norm_sq_eq_integral_sq g

/-- Translation by `h` as a linear isometry of `L²(ℝⁿ)`. -/
def transL2 (h : EuclideanSpace ℝ (Fin n)) : EucL2 n →ₗᵢ[ℝ] EucL2 n :=
  Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (· + h) (measurePreserving_add_right volume h)

/-- A translate is represented almost everywhere by the shifted function. -/
theorem coeFn_transL2 (h : EuclideanSpace ℝ (Fin n)) (g : EucL2 n) :
    (transL2 h g : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] fun x => g (x + h) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Translation is the action of `DomAddAct.mk h` on `L²`. -/
theorem transL2_apply (h : EuclideanSpace ℝ (Fin n)) (g : EucL2 n) :
    transL2 h g = DomAddAct.mk h +ᵥ g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_transL2 h g, DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk h) g] with x h1 h2
  rw [h1, h2]
  simp [add_comm]

/-- Translation by `-h` inverts translation by `h`. -/
theorem transL2_transL2_neg (h : EuclideanSpace ℝ (Fin n)) (g : EucL2 n) :
    transL2 h (transL2 (-h) g) = g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_transL2 h (transL2 (-h) g),
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp
      (coeFn_transL2 (-h) g)] with x h1 h2
  rw [h1]
  simpa using h2

/-- The squared `L²` norm of a translation difference, as an integral. -/
theorem norm_sq_transL2_sub (h : EuclideanSpace ℝ (Fin n)) (g : EucL2 n) :
    ‖transL2 h g - g‖ ^ 2 = ∫ x, (g (x + h) - g x) ^ 2 := by
  rw [L2.norm_sq_eq_integral_sq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (transL2 h g) g, coeFn_transL2 h g] with x hx hx1
  rw [hx]; simp only [Pi.sub_apply]; rw [hx1]

end MeasureTheory
