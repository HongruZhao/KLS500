/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.FrechetKolmogorov

/-!
# Difference quotients on `L²(ℝⁿ)`

The difference quotient `Dₖʰ u(x) = (u(x + h eₖ) - u(x)) / h` drives the interior regularity
theory (Evans, *Partial Differential Equations* (2nd ed.), §5.8.2 and §6.3.1). It is realised
here as a continuous linear map on the whole-space space `EucL2 d`, built from the translation
isometry `transL2`, so that its adjoint and norm bounds descend from translation invariance of
Lebesgue measure.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

variable {d : ℕ}

/-- The shift vector `h • eₖ` in the `k`-th coordinate direction. -/
def hshift (k : Fin d) (h : ℝ) : EuclideanSpace ℝ (Fin d) :=
  h • EuclideanSpace.single k (1 : ℝ)

/-- The forward difference quotient `Dₖʰ u = (τ_{h eₖ} u - u) / h` as a
continuous linear map on `L²(ℝⁿ)`. For `h = 0` it is the zero map. -/
def diffQuot (k : Fin d) (h : ℝ) : EucL2 d →L[ℝ] EucL2 d :=
  h⁻¹ • ((transL2 (hshift k h)).toContinuousLinearMap - ContinuousLinearMap.id ℝ (EucL2 d))

/-- The difference quotient vanishes identically at `h = 0`. -/
@[simp] theorem diffQuot_zero (k : Fin d) : diffQuot k (0 : ℝ) = 0 := by
  simp [diffQuot]

/-- The difference quotient is the translation difference divided by the step. -/
theorem diffQuot_apply (k : Fin d) (h : ℝ) (u : EucL2 d) :
    diffQuot k h u = h⁻¹ • (transL2 (hshift k h) u - u) := by
  simp [diffQuot, LinearIsometry.coe_toContinuousLinearMap]

/-- The pointwise a.e. formula for the difference quotient:
`Dₖʰ u(x) = (u(x + h eₖ) - u(x)) / h`. -/
theorem coeFn_diffQuot (k : Fin d) (h : ℝ) (u : EucL2 d) :
    (diffQuot k h u : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume] fun x => (u (x + hshift k h) - u x) / h := by
  rw [diffQuot_apply]
  filter_upwards [Lp.coeFn_smul h⁻¹ (transL2 (hshift k h) u - u),
      Lp.coeFn_sub (transL2 (hshift k h) u) u, coeFn_transL2 (hshift k h) u]
    with x hx1 hx2 hx3
  simp only [hx1, Pi.smul_apply, hx2, Pi.sub_apply, hx3, smul_eq_mul, div_eq_inv_mul]

/-- Translation by `v` is adjoint to translation by `-v` in the real `L²` inner product:
`⟪τ_v u, w⟫ = ⟪u, τ_{-v} w⟫`. This is the continuous shadow of discrete summation by
parts, and rests on translation invariance of Lebesgue measure (Evans, *Partial
Differential Equations* (2nd ed.), §5.8.2). -/
theorem transL2_inner_adjoint (v : EuclideanSpace ℝ (Fin d)) (u w : EucL2 d) :
    ⟪transL2 v u, w⟫ = ⟪u, transL2 (-v) w⟫ := by
  rw [← (transL2 v).inner_map_map u (transL2 (-v) w), transL2_transL2_neg]

/-- The shift vector negates under negation of the step: `h eₖ ↦ -(h eₖ)` as `h ↦ -h`. -/
theorem hshift_neg (k : Fin d) (h : ℝ) : hshift k (-h) = - hshift k h := by
  simp [hshift, neg_smul]

/-- **Discrete integration by parts.** The difference quotient `Dₖʰ` is adjoint, up to a
sign, to the backward difference quotient `Dₖ⁻ʰ`: `⟪Dₖʰ u, w⟫ = -⟪u, Dₖ⁻ʰ w⟫`. This is
the discretised analogue of integration by parts underlying the Caccioppoli-type interior
estimate (Evans, *Partial Differential Equations* (2nd ed.), §5.8.2, proof of Theorem 3). -/
theorem diffQuot_inner_adjoint (k : Fin d) (h : ℝ) (u w : EucL2 d) :
    ⟪diffQuot k h u, w⟫ = -⟪u, diffQuot k (-h) w⟫ := by
  rw [diffQuot_apply, diffQuot_apply, real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right, transL2_inner_adjoint (hshift k h) u w,
    ← hshift_neg k h]
  ring

end EllipticPdes.Regularity
