/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Reflection in a coordinate hyperplane

Reflecting the `j`-th coordinate is the first step of the extension operator: a function on a
half-ball is continued across the flat piece of its boundary by composing with the reflection.

The reflection is a linear isometry, so it preserves Lebesgue measure and is a measurable
embedding. It sends the `k`-th partial derivative to `±` the `k`-th partial derivative of the
composite, with the sign negative exactly at `k = j`, and therefore sends a weak gradient on a set
to a weak gradient on the preimage of that set.

## Main declarations

* `EllipticPdes.Extension.reflectLI`: the reflection, as a linear isometry equivalence.
* `EllipticPdes.Extension.partialD_comp_reflect`: the partial derivatives of a reflected
  function.
* `EllipticPdes.Extension.hasWeakGradOn_comp_reflect`: the weak gradient of a reflected
  function.
* `EllipticPdes.Extension.eLpNorm_comp_reflect`: reflection preserves every `Lᵖ` seminorm.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4, Theorem 1.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev EllipticPdes.Embedding

variable {d : ℕ}

/-! ### The reflection -/

/-- The sign the reflection in the `j`-th coordinate hyperplane attaches to the `k`-th
coordinate: negative exactly when the two agree. -/
def reflectSign (j k : Fin d) : ℝ := if k = j then -1 else 1

/-- `reflectSign j k` squares to one. -/
lemma reflectSign_mul_self (j k : Fin d) : reflectSign j k * reflectSign j k = 1 := by
  rw [reflectSign]
  split <;> norm_num

/-- `reflectSign j k` is nonzero. -/
lemma reflectSign_ne_zero (j k : Fin d) : reflectSign j k ≠ 0 := by
  rw [reflectSign]
  split <;> norm_num

/-- **Reflection in the `j`-th coordinate hyperplane**, as a linear isometry equivalence of
Euclidean space. -/
def reflectLI (j : Fin d) : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun k => if k = j then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

/-- The `k`-th coordinate of `reflectLI j x` is `reflectSign j k * x k`. -/
@[simp] lemma reflectLI_apply (j : Fin d) (x : EuclideanSpace ℝ (Fin d)) (k : Fin d) :
    reflectLI j x k = reflectSign j k * x k := by
  rw [reflectLI, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply, reflectSign]
  split <;> simp

/-- The reflection negates the `j`-th coordinate. -/
lemma reflectLI_apply_self (j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    reflectLI j x j = -x j := by
  simp [reflectSign]

/-- `reflectLI j` is involutive. -/
@[simp] lemma reflectLI_involutive (j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    reflectLI j (reflectLI j x) = x := by
  ext k
  rw [reflectLI_apply, reflectLI_apply, ← mul_assoc, reflectSign_mul_self, one_mul]

/-- Taking the preimage under `reflectLI j` twice returns the original set. -/
lemma reflectLI_preimage_preimage (j : Fin d) (B : Set (EuclideanSpace ℝ (Fin d))) :
    reflectLI j ⁻¹' (reflectLI j ⁻¹' B) = B := by
  ext x
  simp only [Set.mem_preimage, reflectLI_involutive]

/-- `reflectLI j` preserves Lebesgue measure. -/
lemma measurePreserving_reflectLI (j : Fin d) :
    MeasurePreserving (reflectLI j) volume volume :=
  (reflectLI j).measurePreserving

/-- `reflectLI j` is a measurable embedding. -/
lemma measurableEmbedding_reflectLI (j : Fin d) :
    MeasurableEmbedding (reflectLI j) :=
  (reflectLI j).toHomeomorph.measurableEmbedding

/-! ### Derivatives and supports -/

/-- The reflection sends the `k`-th standard direction to `reflectSign j k` times itself. -/
lemma reflectLI_single (j k : Fin d) :
    reflectLI j (EuclideanSpace.single k (1 : ℝ))
      = reflectSign j k • EuclideanSpace.single k (1 : ℝ) := by
  ext m
  rw [reflectLI_apply]
  by_cases hm : m = k
  · subst hm; simp
  · simp [hm]

/-- **Partial derivatives of a reflected function.** -/
theorem partialD_comp_reflect {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Differentiable ℝ φ)
    (j k : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD k (fun y => φ (reflectLI j y)) x
      = reflectSign j k * partialD k φ (reflectLI j x) := by
  have := partialD_comp (f := reflectLI j) (hφ _)
    (reflectLI j).toContinuousLinearEquiv.hasFDerivAt (x := x) k
  simpa [partialD, reflectLI_single] using this

/-- Composition with `reflectLI j` preserves smoothness. -/
lemma contDiff_comp_reflect {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (reflectLI j y)) :=
  hφ.comp (reflectLI j).toContinuousLinearEquiv.contDiff

/-- Composition with `reflectLI j` preserves compact support. -/
lemma hasCompactSupport_comp_reflect {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : HasCompactSupport φ) (j : Fin d) :
    HasCompactSupport (fun y => φ (reflectLI j y)) :=
  hφ.comp_homeomorph (reflectLI j).toHomeomorph

/-! ### The weak gradient of a reflected function -/

/-- **Reflection of a weak gradient.** If `u` has weak gradient `g` on `B`, then `u ∘ Rⱼ` has weak
gradient `k ↦ ±(gₖ ∘ Rⱼ)` on the preimage of `B`, with the sign negative exactly at `k = j`. -/
theorem hasWeakGradOn_comp_reflect {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : HasWeakGradOn B u g) (j : Fin d) :
    HasWeakGradOn (reflectLI j ⁻¹' B) (fun y => u (reflectLI j y))
      (fun k y => reflectSign j k * g k (reflectLI j y)) := by
  rw [hasWeakGradOn_iff] at h ⊢
  intro k
  have h1 := (h k).smul (reflectSign j k)
  rw [← reflectLI_single] at h1
  exact h1.comp_linear (reflectLI j).toContinuousLinearEquiv (measurePreserving_reflectLI j)

/-- **Reflection preserves every `Lᵖ` seminorm**, the reflection being measure preserving. This
is what makes the bound on an extension by reflection a bound with no loss. -/
theorem eLpNorm_comp_reflect {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : AEStronglyMeasurable f volume) (j : Fin d) (p : ℝ≥0∞) :
    eLpNorm (fun y => f (reflectLI j y)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_reflectLI j)

end EllipticPdes.Extension
