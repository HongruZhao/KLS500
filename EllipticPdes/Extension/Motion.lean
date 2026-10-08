/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.Basic

/-!
# Rigid motion of a boundary chart

A boundary chart relabels and reorients the coordinate axes before reading the domain off a
graph, and that relabelling and reorientation is a linear isometry of the whole space. This
file moves a weak gradient through one.

A linear isometry is its own derivative, so the weak derivative along `v` of `u ∘ e` is the weak
derivative of `u` along `e v`, composed with `e`. The `k`-th partial derivative is therefore a
sum over the directions that `e` sends the `k`-th one to, and the finite sum passes through an
integral, which is where the integrability hypotheses enter.

## Main declarations

* `EllipticPdes.Extension.motionOp`: the pull-back of a pair, as a linear map.
* `EllipticPdes.Extension.hasWeakGradOn_comp_linearIsometry`: the weak gradient through an
  isometry.
* `EllipticPdes.Extension.eLpNorm_grad_comp_linearIsometry_le`: its `Lᵖ` seminorm, bounded by
  the sum over the components the isometry mixes.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §C.1.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn HasWeakDerivAlong hasWeakGradOn_iff)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Weak gradient through a linear isometry.** The isometry is its own derivative, so the
gradient transforms by its transpose, which in coordinates is the sum over the directions the
isometry sends the `k`-th one to. -/
theorem hasWeakGradOn_comp_linearIsometry {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (hwg : HasWeakGradOn B u g)
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    HasWeakGradOn ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B)
      (fun y => u (e y))
      (fun k y => ∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * g i (e y)) := by
  rw [hasWeakGradOn_iff] at hwg ⊢
  intro k
  have h1 := HasWeakDerivAlong.sum Finset.univ (fun i => e (EuclideanSpace.single k (1 : ℝ)) i)
    hu (fun i _ => hgi i) (fun i _ => hwg i)
  rw [show ∑ i, (e (EuclideanSpace.single k (1 : ℝ))).ofLp i • EuclideanSpace.single i (1 : ℝ)
    = e (EuclideanSpace.single k (1 : ℝ)) by
      simpa using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (e (EuclideanSpace.single k 1))]
    at h1
  exact h1.comp_linear e.toContinuousLinearEquiv e.measurePreserving

/-! ### The motion on pairs -/

/-- **Pull-back through a linear isometry, as a linear map on pairs.** The gradient transforms by
the transpose of the isometry. -/
def motionOp (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    SobolevPair d →ₗ[ℝ] SobolevPair d where
  toFun w := (fun y => w.1 (e y),
    fun k y => ∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * w.2 i (e y))
  map_add' w w' := by
    refine Prod.ext rfl (funext fun k => funext fun y => ?_)
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a w := by
    refine Prod.ext rfl (funext fun k => funext fun y => ?_)
    simp [Finset.mul_sum, mul_left_comm]

/-- **Integrability of a pair through a linear isometry.** -/
theorem integrableOn_motionOp {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (motionOp e (u, g)).1
        ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B) volume ∧
      ∀ k, IntegrableOn ((motionOp e (u, g)).2 k)
        ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B) volume := by
  have hmp := e.measurePreserving
  have hme : MeasurableEmbedding (e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
    e.toHomeomorph.measurableEmbedding
  refine ⟨(hmp.integrableOn_comp_preimage hme).mpr hu, fun k => ?_⟩
  change Integrable (fun y => ∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * g i (e y)) _
  exact integrable_finsetSum _ fun i _ =>
    ((hmp.integrableOn_comp_preimage hme).mpr (hgi i)).const_mul _

/-- **A pair through a linear isometry.** If `(u, g)` has a weak gradient on `B` with integrable
components, so does `motionOp e (u, g)` on the preimage of `B`. -/
theorem motionOp_spec {B : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : IntegrableOn u B volume)
    (hgi : ∀ k, IntegrableOn (g k) B volume) (hwg : HasWeakGradOn B u g)
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    HasWeakGradOn ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B)
        (motionOp e (u, g)).1 (motionOp e (u, g)).2 ∧
      IntegrableOn (motionOp e (u, g)).1
        ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B) volume ∧
      ∀ k, IntegrableOn ((motionOp e (u, g)).2 k)
        ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B) volume :=
  ⟨hasWeakGradOn_comp_linearIsometry hu hgi hwg e, integrableOn_motionOp hu hgi e⟩

/-! ### The gradient's seminorm -/

/-- A seminorm over the preimage of a set under a linear isometry is the seminorm over the set. -/
theorem eLpNorm_comp_linearIsometry {B : Set (EuclideanSpace ℝ (Fin d))} {p : ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : AEStronglyMeasurable f (volume.restrict B))
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    eLpNorm (fun y => f (e y)) p
        (volume.restrict ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B))
      = eLpNorm f p (volume.restrict B) :=
  eLpNorm_comp_measurePreserving hf
    (e.measurePreserving.restrict_preimage_emb e.toHomeomorph.measurableEmbedding B)

/-- **Seminorm of the gradient through a linear isometry.** Each coordinate of the
image of a unit direction is at most one, so the transported component is bounded by the sum of
the components it mixes. -/
theorem eLpNorm_grad_comp_linearIsometry_le {p : ℝ≥0∞} (hp : 1 ≤ p)
    {B : Set (EuclideanSpace ℝ (Fin d))} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hgm : ∀ i, AEStronglyMeasurable (g i) (volume.restrict B))
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (k : Fin d) :
    eLpNorm (fun y => ∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * g i (e y)) p
        (volume.restrict ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B))
      ≤ ∑ i, eLpNorm (g i) p (volume.restrict B) := by
  have hmp := e.measurePreserving.restrict_preimage_emb e.toHomeomorph.measurableEmbedding B
  have hcoord : ∀ i, |e (EuclideanSpace.single k (1 : ℝ)) i| ≤ 1 := fun i => by
    simpa [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (e (EuclideanSpace.single k (1 : ℝ))) i).trans_eq (by simp)
  exact (eLpNorm_sum_mul_le hp hcoord fun i => (hgm i).comp_measurePreserving hmp).trans
    (Finset.sum_le_sum fun i _ => (eLpNorm_comp_measurePreserving (hgm i) hmp).le)

end EllipticPdes.Extension
