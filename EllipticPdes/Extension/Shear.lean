/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.C1Test
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Shear of a `C¹` boundary chart

A bounded domain with `C¹` boundary is, near a boundary point and after relabelling the
coordinates, the region above the graph of a `C¹` function `γ` of the remaining coordinates.
The map that flattens the boundary is the shear `y ↦ y + γ(y) • eⱼ`, whose inverse is the shear
by `-γ`, and whose derivative is the identity plus a rank-one map that annihilates its own
direction. Its determinant is therefore `1`, so it preserves Lebesgue measure and the change of
variables leaves every integral unchanged.

## Main declarations

* `EllipticPdes.Extension.shear`: the map.
* `EllipticPdes.Extension.shear_shear_neg`: the shear by `-γ` inverts it.
* `EllipticPdes.Extension.det_shearDeriv`: the derivative has determinant `1`.
* `EllipticPdes.Extension.shearHomeomorph`: the shear as a homeomorphism of the whole space.
* `EllipticPdes.Extension.measurePreserving_shear`: the shear preserves Lebesgue measure.
* `EllipticPdes.Extension.partialD_comp_shear`: the chain rule through a shear.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4, and §C.1 for the boundary chart.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Shear of a boundary chart.** The point `y` moves along the `j`-th axis by `γ y`. -/
def shear (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  y + γ y • EuclideanSpace.single j (1 : ℝ)

/-- `γ` does not depend on the `j`-th coordinate, which is what makes the shear invertible by a
shear and its derivative nilpotent. -/
def IndepCoord (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ (y : EuclideanSpace ℝ (Fin d)) (t : ℝ), γ (y + t • EuclideanSpace.single j (1 : ℝ)) = γ y

/-- **Inversion of the shear by `γ`.** -/
theorem shear_shear_neg {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ)
    (y : EuclideanSpace ℝ (Fin d)) : shear j (fun z => -γ z) (shear j γ y) = y := by
  simp only [shear, hind y (γ y)]
  module

/-- **Inversion of the shear by `-γ`.** -/
theorem shear_neg_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ)
    (y : EuclideanSpace ℝ (Fin d)) : shear j γ (shear j (fun z => -γ z) y) = y := by
  simp only [shear]
  rw [hind y (-γ y)]
  module

/-- The shear is a bijection of the whole space. -/
theorem bijective_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ) :
    Function.Bijective (shear j γ) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨shear j (fun z => -γ z), shear_shear_neg hind, shear_neg_shear hind⟩

/-- **Vanishing `j`-th partial of a function independent of that coordinate.** -/
theorem partialD_eq_zero_of_indepCoord {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) (y : EuclideanSpace ℝ (Fin d)) :
    partialD j γ y = 0 := by
  rw [partialD, ← (hγ y).lineDeriv_eq_fderiv, lineDeriv,
    show (fun t : ℝ => γ (y + t • EuclideanSpace.single j (1 : ℝ))) = fun _ => γ y from
      funext (hind y), deriv_const]

/-- The derivative of the shear: the identity plus a rank-one map in the direction `eⱼ`. -/
def shearDeriv (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
    + (fderiv ℝ γ y).smulRight (EuclideanSpace.single j (1 : ℝ))

/-- **Derivative of the shear.** -/
theorem hasFDerivAt_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (y : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (shear j γ) (shearDeriv j γ y) y :=
  (hasFDerivAt_id y).add (((hγ y).hasFDerivAt).smul_const (EuclideanSpace.single j (1 : ℝ)))

/-- **Determinant `1` of the shear derivative.** It is the identity plus a rank-one map that
annihilates its own direction. -/
theorem det_shearDeriv {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) (y : EuclideanSpace ℝ (Fin d)) :
    (shearDeriv j γ y).det = 1 := by
  have h := LinearMap.det_id_add_smulRight (fderiv ℝ γ y : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ)
    (EuclideanSpace.single j (1 : ℝ))
  have h0 := partialD_eq_zero_of_indepCoord hγ hind y
  rw [partialD] at h0
  simpa [ContinuousLinearMap.det, shearDeriv, h0] using h

/-! ### The shear as a homeomorphism, and its measure -/

/-- The shear is continuous when the chart is. -/
theorem continuous_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : Continuous γ) :
    Continuous (shear j γ) :=
  continuous_id.add (hγ.smul continuous_const)

/-- The shear is `C^n` when the chart is. -/
theorem contDiff_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} {n : ℕ∞}
    (hγ : ContDiff ℝ n γ) : ContDiff ℝ n (shear j γ) :=
  contDiff_id.add (hγ.smul contDiff_const)

/-- Negating a chart preserves independence of the `j`-th coordinate. -/
theorem IndepCoord.neg {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ) :
    IndepCoord j fun z => -γ z := by
  intro y t
  change -γ (y + t • EuclideanSpace.single j (1 : ℝ)) = -γ y
  rw [hind y t]

/-- **Shear as a homeomorphism of the whole space**, inverted by the shear by `-γ`. -/
def shearHomeomorph {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : Continuous γ)
    (hind : IndepCoord j γ) : EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d) where
  toFun := shear j γ
  invFun := shear j fun z => -γ z
  left_inv := shear_shear_neg hind
  right_inv := shear_neg_shear hind
  continuous_toFun := continuous_shear hγ
  continuous_invFun := continuous_shear hγ.neg

/-- The shear is a measurable embedding, being a homeomorphism. -/
theorem measurableEmbedding_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Continuous γ) (hind : IndepCoord j γ) : MeasurableEmbedding (shear j γ) :=
  (shearHomeomorph hγ hind).measurableEmbedding

/-- **Preservation of Lebesgue measure by a shear.** Its inverse is the shear by `-γ`, whose
derivative has determinant `1`, so the image of a measurable set has the measure of the set. -/
theorem measurePreserving_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) :
    MeasurePreserving (shear j γ) volume volume := by
  have hcont : Continuous (shear j γ) := continuous_shear hγ.continuous
  refine ⟨hcont.measurable, Measure.ext fun s hs => ?_⟩
  have hpre : shear j γ ⁻¹' s = shear j (fun z => -γ z) '' s := by
    exact (congrFun (shearHomeomorph hγ.continuous hind).image_symm s).symm
  have hnd : Differentiable ℝ fun z => -γ z := hγ.neg
  rw [Measure.map_apply hcont.measurable hs, hpre,
    ← lintegral_abs_det_fderiv_eq_addHaar_image volume hs
      (fun x _ => (hasFDerivAt_shear hnd x).hasFDerivWithinAt)
      (bijective_shear hind.neg).injective.injOn]
  simp [det_shearDeriv hnd hind.neg]

/-! ### The chain rule through a shear -/

/-- **Partial derivatives through a shear.** The derivative of the shear is the identity plus a
rank-one map in the direction `eⱼ`, so a partial derivative of a composition adds to the
corresponding partial of the outer function the `j`-th one times the partial of the chart. -/
theorem partialD_comp_shear {j : Fin d} {γ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hφ : Differentiable ℝ φ) (k : Fin d)
    (y : EuclideanSpace ℝ (Fin d)) :
    partialD k (fun z => φ (shear j γ z)) y
      = partialD k φ (shear j γ y) + partialD j φ (shear j γ y) * partialD k γ y := by
  rw [partialD_comp (hφ _) (hasFDerivAt_shear hγ y)]
  simp [shearDeriv, partialD]
  ring

end EllipticPdes.Extension
