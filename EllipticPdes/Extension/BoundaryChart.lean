/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.ShearWeakGrad
public import EllipticPdes.Extension.EvenReflection

/-!
# Extension across a `C¹` boundary chart

Near a boundary point a domain with `C¹` boundary is, after relabelling the coordinates, the
region above the graph of a `C¹` function `γ` of the remaining ones. This file extends a
Sobolev class across that graph, which is the local half of Guo's extension operator.

The route is the composite of the three maps the chapter has built. The shear `S y = y + γ(y)eⱼ`
inverts the flattening, so the flattening `T = S⁻¹` sends the region above the graph onto the
half space; the class travels the other way, through `S`, and picks up the transpose of the
shear's derivative on its gradient. The flattened class is then reflected across the interface,
and the reflection returns through `T`.

## Main declarations

* `EllipticPdes.Extension.aboveGraph`: the region above the graph of a chart.
* `EllipticPdes.Extension.preimage_shear_aboveGraph`: the shear pulls that region back to the
  half space.
* `EllipticPdes.Extension.shearOp`, `EllipticPdes.Extension.evenOp` and
  `EllipticPdes.Extension.chartOp`: the shear, the reflection and their composite, as linear
  maps on pairs of a class and a gradient.
* `EllipticPdes.Extension.chartExt` and `EllipticPdes.Extension.chartExtGrad`: the extension
  and its gradient.
* `EllipticPdes.Extension.hasWeakGradOn_chartExt`: the extension has that weak gradient on the
  whole space.
* `EllipticPdes.Extension.integrable_chartExt` and
  `EllipticPdes.Extension.integrable_chartExtGrad`: the extension and its gradient are
  integrable.
* `EllipticPdes.Extension.chartExt_eq_of_mem`: the extension agrees with the class on the
  region it extends.
* `EllipticPdes.Extension.eLpNorm_chartExt_le` and
  `EllipticPdes.Extension.eLpNorm_chartExtGrad_le`: the extension and its gradient, bounded in
  every `Lᵖ` seminorm.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
steps 1 and 2 (p. 21); L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1
and §C.1.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn integrableOn_mul_bounded)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### The region above a graph -/

/-- **Region above the graph of a chart**, in the `j`-th coordinate. -/
def aboveGraph (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) := {y | γ y < y j}

/-- `aboveGraph j γ` is open for continuous `γ`. -/
theorem isOpen_aboveGraph {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : Continuous γ) :
    IsOpen (aboveGraph j γ) :=
  isOpen_lt hγ (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous

/-- The `j`-th coordinate of a sheared point. -/
theorem shear_coord {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (y : EuclideanSpace ℝ (Fin d)) : (shear j γ y) j = y j + γ y := by
  simp [shear]

/-- **Pull-back of the half space through the flattening.** -/
theorem aboveGraph_eq_preimage {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} :
    aboveGraph j γ = shear j (fun z => -γ z) ⁻¹' halfSpace j := by
  ext y
  have hc : (shear j (fun z => -γ z) y) j = y j - γ y := by
    rw [shear_coord]; ring
  simp only [aboveGraph, Set.mem_preimage, halfSpace, Set.mem_ofPred_eq, hc]
  constructor <;> intro h <;> linarith

/-- **Pull-back of the region above the graph through the shear.** -/
theorem preimage_shear_aboveGraph {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hind : IndepCoord j γ) : shear j γ ⁻¹' aboveGraph j γ = halfSpace j := by
  ext x
  have hγS : γ (shear j γ x) = γ x := hind x (γ x)
  simp only [Set.mem_preimage, aboveGraph, halfSpace, Set.mem_ofPred_eq, shear_coord, hγS]
  constructor <;> intro h <;> linarith

/-! ### Transport through the shear -/

/-- **Gradient of a class pulled back through the shear**, the transpose of the shear's
derivative applied to the gradient. -/
def shearGrad (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => g k (shear j γ x) + g j (shear j γ x) * partialD k γ x

/-- **Pull-back through the shear, as a linear map on pairs.** -/
def shearOp (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) : SobolevPair d →ₗ[ℝ] SobolevPair d where
  toFun w := (fun x => w.1 (shear j γ x), shearGrad j γ w.2)
  map_add' w w' := by
    refine Prod.ext rfl (funext fun k => funext fun x => ?_)
    simp only [shearGrad, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' a w := by
    refine Prod.ext rfl (funext fun k => funext fun x => ?_)
    simp only [shearGrad, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The partial derivative of a negated chart. -/
theorem partialD_neg {γ : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d)
    (y : EuclideanSpace ℝ (Fin d)) : partialD k (fun z => -γ z) y = -partialD k γ y := by
  simp only [partialD, fderiv_fun_neg, _root_.neg_apply]

/-- **Restriction of the shear to the half space**, preserving measure onto the region above
the graph. -/
theorem measurePreserving_shear_halfSpace {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) :
    MeasurePreserving (shear j γ) (volume.restrict (halfSpace j))
      (volume.restrict (aboveGraph j γ)) := by
  have h := (measurePreserving_shear hγ hind).restrict_preimage_emb
    (measurableEmbedding_shear hγ.continuous hind) (aboveGraph j γ)
  rwa [preimage_shear_aboveGraph hind] at h

/-- Integrability on the region above the graph is integrability of the pull-back on the half
space. -/
theorem integrableOn_comp_shear_halfSpace {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) {w : EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : IntegrableOn w (aboveGraph j γ) volume) :
    IntegrableOn (fun x => w (shear j γ x)) (halfSpace j) volume :=
  ((measurePreserving_shear_halfSpace hγ hind).integrable_comp hw.1).mpr hw

/-- **Normal component of the gradient through the shear**, untouched, the chart having no
partial derivative in the direction it is a graph in. -/
theorem shearGrad_normal {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) :
    shearGrad j γ g j = fun x => g j (shear j γ x) := by
  funext x
  simp [shearGrad, partialD_eq_zero_of_indepCoord hγ hind x]

/-- The pulled-back gradient is integrable on the half space. -/
theorem integrableOn_shearGrad {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} {M : ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ)
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M)
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hgi : ∀ k, IntegrableOn (g k) (aboveGraph j γ) volume) (k : Fin d) :
    IntegrableOn (shearGrad j γ g k) (halfSpace j) volume :=
  (integrableOn_comp_shear_halfSpace (hγ.differentiable (by simp)) hind (hgi k)).add
    (integrableOn_mul_bounded
      (integrableOn_comp_shear_halfSpace (hγ.differentiable (by simp)) hind (hgi j))
      (hγ.continuous_partialD one_ne_zero k) (hγb k))

/-- **Bound on the transported gradient**, componentwise. The shear contributes the chart's
bound against the normal component. -/
theorem eLpNorm_shearGrad_le {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ) {M : ℝ}
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hgm : ∀ k, AEStronglyMeasurable (g k) (volume.restrict (aboveGraph j γ))) (k : Fin d) :
    eLpNorm (shearGrad j γ g k) p (volume.restrict (halfSpace j))
      ≤ eLpNorm (g k) p (volume.restrict (aboveGraph j γ))
        + ENNReal.ofReal M * eLpNorm (g j) p (volume.restrict (aboveGraph j γ)) := by
  have hres := measurePreserving_shear_halfSpace (hγ.differentiable (by simp)) hind
  have heq : ∀ i, eLpNorm (fun x => g i (shear j γ x)) p (volume.restrict (halfSpace j))
      = eLpNorm (g i) p (volume.restrict (aboveGraph j γ)) := fun i =>
    eLpNorm_comp_measurePreserving (hgm i) hres
  refine (eLpNorm_add_le hp).trans ?_
  rw [heq k, ← heq j]
  exact add_le_add le_rfl (eLpNorm_mul_le_of_bound
    (((hgm j).comp_measurePreserving hres).mul
      (hγ.continuous_partialD one_ne_zero k).aestronglyMeasurable) (hγb k))

/-! ### The extension -/

/-- **Extension across a `C¹` boundary chart.** The chart is flattened by the shear, the
flattened class is reflected across the interface, and the reflection returns through the
inverse shear. -/
def chartExt (j : Fin d) (γ u : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => evenExt j (fun x => u (shear j γ x)) (shear j (fun z => -γ z) y)

/-- **Gradient of the extension across a `C¹` boundary chart.** The second term is the shear's
own contribution, with the sign of the inverse chart. -/
def chartExtGrad (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) : EuclideanSpace ℝ (Fin d) → ℝ :=
  shearGrad j (fun z => -γ z) (evenExtGrad j (shearGrad j γ g)) k

/-- **Reflection across the interface, as a linear map on pairs.** -/
def evenOp (j : Fin d) : SobolevPair d →ₗ[ℝ] SobolevPair d where
  toFun w := (evenExt j w.1, evenExtGrad j w.2)
  map_add' _ _ := Prod.ext (map_add _ _ _) (funext fun _ => (signedExt j _).map_add _ _)
  map_smul' _ _ := Prod.ext (map_smul _ _ _) (funext fun _ => (signedExt j _).map_smul _ _)

/-- **Extension across a chart, as a linear map on pairs**: flatten, reflect, return. -/
def chartOp (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) : SobolevPair d →ₗ[ℝ] SobolevPair d :=
  shearOp j (fun z => -γ z) ∘ₗ evenOp j ∘ₗ shearOp j γ

/-- `chartOp` is the pair of `chartExt` and `chartExtGrad`. -/
theorem chartOp_apply (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) (w : SobolevPair d) :
    chartOp j γ w = (chartExt j γ w.1, fun k => chartExtGrad j γ w.2 k) := rfl

/-- **Weak gradient of the extension across a `C¹` boundary chart**, on the whole space. The
class travels through the shear onto the half space, the reflection extends it across the
interface, and the inverse shear returns it, each of the three steps supplying its own half of
the gradient. -/
theorem hasWeakGradOn_chartExt {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ) {M : ℝ}
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u (aboveGraph j γ) volume)
    (hgi : ∀ k, IntegrableOn (g k) (aboveGraph j γ) volume)
    (hwg : HasWeakGradOn (aboveGraph j γ) u g) :
    HasWeakGradOn Set.univ (chartExt j γ u) (chartExtGrad j γ g) := by
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  have hnegb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)),
      ‖partialD k (fun z => -γ z) y‖ ≤ M := fun k y => by
    rw [partialD_neg, norm_neg]
    exact hγb k y
  have hS : HasWeakGradOn (halfSpace j) (fun x => u (shear j γ x)) (shearGrad j γ g) := by
    have h := hasWeakGradOn_comp_shear (isOpen_aboveGraph hγd.continuous) hu hgi hwg hγ hind hγb
    rwa [preimage_shear_aboveGraph hind] at h
  have hFinal := hasWeakGradOn_comp_shear (B := Set.univ) isOpen_univ
    (integrable_signedExt (integrableOn_comp_shear_halfSpace hγd hind hu)).integrableOn
    (fun k => (integrable_signedExt (integrableOn_shearGrad hγ hind hγb hgi k)).integrableOn)
    (hasWeakGradOn_evenExt (integrableOn_comp_shear_halfSpace hγd hind hu)
      (integrableOn_shearGrad hγ hind hγb hgi) hS) hγ.neg hind.neg hnegb
  rwa [Set.preimage_univ] at hFinal

/-- **Agreement of the extension with the class on the region it extends.** -/
theorem chartExt_eq_of_mem {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hind : IndepCoord j γ) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ aboveGraph j γ) : chartExt j γ u y = u y := by
  rw [aboveGraph_eq_preimage] at hy
  simp only [chartExt, evenExt, signedExt_of_nonneg (le_of_lt hy), shear_neg_shear hind y]

/-- **Integrability of the extension across a chart.** -/
theorem integrable_chartExt {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u (aboveGraph j γ) volume) : Integrable (chartExt j γ u) volume :=
  ((measurePreserving_shear hγ.neg hind.neg).integrable_comp_emb
    (measurableEmbedding_shear hγ.neg.continuous hind.neg)).mpr
    (integrable_signedExt (integrableOn_comp_shear_halfSpace hγ hind hu))

/-- **Integrability of the gradient of the extension across a chart.** -/
theorem integrable_chartExtGrad {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} {M : ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ)
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M)
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hgi : ∀ k, IntegrableOn (g k) (aboveGraph j γ) volume) (k : Fin d) :
    Integrable (chartExtGrad j γ g k) volume := by
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  have hback : ∀ i, Integrable (evenExtGrad j (shearGrad j γ g) i ∘ shear j fun z => -γ z)
      volume := fun i =>
    ((measurePreserving_shear hγd.neg hind.neg).integrable_comp_emb
      (measurableEmbedding_shear hγd.neg.continuous hind.neg)).mpr
      (integrable_signedExt (integrableOn_shearGrad hγ hind hγb hgi i))
  exact (hback k).add (integrableOn_univ.mp (integrableOn_mul_bounded
    (integrableOn_univ.mpr (hback j)) (hγ.neg.continuous_partialD one_ne_zero k)
    (fun y => by rw [partialD_neg, norm_neg]; exact hγb k y)))

/-- **Bound on the extension in every `Lᵖ` seminorm.** Both shears preserve measure and the
reflection doubles, so the extension over the whole space is bounded by twice the seminorm over
the region above the graph. -/
theorem eLpNorm_chartExt_le {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (aboveGraph j γ))) :
    eLpNorm (chartExt j γ u) p volume
      ≤ 2 * eLpNorm u p (volume.restrict (aboveGraph j γ)) := by
  have hres := measurePreserving_shear_halfSpace hγ hind
  have hvm := hu.comp_measurePreserving hres
  calc eLpNorm (chartExt j γ u) p volume
      = eLpNorm (evenExt j fun x => u (shear j γ x)) p volume :=
        eLpNorm_comp_measurePreserving (aestronglyMeasurable_signedExt hvm)
          (measurePreserving_shear hγ.neg hind.neg)
    _ ≤ 2 * eLpNorm (fun x => u (shear j γ x)) p (volume.restrict (halfSpace j)) :=
        eLpNorm_signedExt_le hp (by simp) hvm
    _ = 2 * eLpNorm u p (volume.restrict (aboveGraph j γ)) := by
        rw [← eLpNorm_comp_measurePreserving hu hres]
        rfl

/-- **Bound on the gradient of the extension across a `C¹` boundary chart.** Each of the three
maps plays its part: the shear contributes the chart's bound against the normal component, the
reflection doubles, and the inverse shear contributes the bound again. -/
theorem eLpNorm_chartExtGrad_le {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ) {M : ℝ} (_hM0 : 0 ≤ M)
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hgm : ∀ k, AEStronglyMeasurable (g k) (volume.restrict (aboveGraph j γ))) (k : Fin d) :
    eLpNorm (chartExtGrad j γ g k) p volume
      ≤ 2 * eLpNorm (g k) p (volume.restrict (aboveGraph j γ))
        + 4 * ENNReal.ofReal M * eLpNorm (g j) p (volume.restrict (aboveGraph j γ)) := by
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  have hres := measurePreserving_shear_halfSpace hγd hind
  have hmpT := measurePreserving_shear hγd.neg hind.neg
  have hsgm : ∀ i, AEStronglyMeasurable (shearGrad j γ g i) (volume.restrict (halfSpace j)) :=
    fun i => ((hgm i).comp_measurePreserving hres).add (((hgm j).comp_measurePreserving hres).mul
      (hγ.continuous_partialD one_ne_zero i).aestronglyMeasurable)
  -- the reflected gradient, returned through the inverse shear, and its bound on the half space
  have hH : ∀ i, eLpNorm (evenExtGrad j (shearGrad j γ g) i ∘ shear j fun z => -γ z) p volume
      ≤ 2 * eLpNorm (shearGrad j γ g i) p (volume.restrict (halfSpace j)) := fun i =>
    (eLpNorm_comp_measurePreserving (aestronglyMeasurable_signedExt (hsgm i)) hmpT).le.trans
      (eLpNorm_signedExt_le hp (abs_reflectSign j i) (hsgm i))
  have hjbound : eLpNorm (shearGrad j γ g j) p (volume.restrict (halfSpace j))
      = eLpNorm (g j) p (volume.restrict (aboveGraph j γ)) := by
    rw [shearGrad_normal hγd hind g]
    exact eLpNorm_comp_measurePreserving (hgm j) hres
  have hHm : AEStronglyMeasurable (evenExtGrad j (shearGrad j γ g) j ∘ shear j fun z => -γ z)
      volume := (aestronglyMeasurable_signedExt (hsgm j)).comp_measurePreserving hmpT
  refine (eLpNorm_add_le hp).trans ?_
  calc _ ≤ 2 * (eLpNorm (g k) p (volume.restrict (aboveGraph j γ))
          + ENNReal.ofReal M * eLpNorm (g j) p (volume.restrict (aboveGraph j γ)))
        + ENNReal.ofReal M * (2 * eLpNorm (g j) p (volume.restrict (aboveGraph j γ))) := by
        refine add_le_add ((hH k).trans ?_) ?_
        · exact mul_le_mul_right (eLpNorm_shearGrad_le hγ hind hγb hp hgm k) 2
        · refine (eLpNorm_mul_le_of_bound (hHm.mul
            (hγ.neg.continuous_partialD one_ne_zero k).aestronglyMeasurable)
            (fun y => by rw [partialD_neg, norm_neg]; exact hγb k y)).trans ?_
          exact mul_le_mul_right ((hH j).trans (by rw [hjbound])) _
    _ = _ := by ring

end EllipticPdes.Extension
