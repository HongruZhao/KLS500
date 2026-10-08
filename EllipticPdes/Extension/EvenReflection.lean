/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.HalfSpace

/-!
# Extension across a flat boundary by reflection

A Sobolev class on the half space extends across the interface by reflecting it: the value at a
point below the interface is the value at its mirror image. The gradient extends the same way,
with a sign in the normal direction, and the extended pair is a weak gradient on the whole
space.

The identity is tested against an arbitrary test function of the whole space. Splitting the
integral at the interface and reflecting the lower half turns it into an integral over the half
space, tested against `φ + s (φ ∘ R)` with `s` the sign of the direction. In the normal
direction that combination is odd, so it vanishes on the interface, which is exactly the
hypothesis under which the boundary term of `EllipticPdes.Extension.integral_partialD_of_eq`
disappears.

## Main declarations

* `EllipticPdes.Extension.signedExt`: the extension of a function by its signed reflection, as
  a linear map.
* `EllipticPdes.Extension.evenExt`, `EllipticPdes.Extension.evenExtGrad`: the extensions of a
  function and of its gradient.
* `EllipticPdes.Extension.integral_signedExt_mul`: an integral of a signed extension is an
  integral over the half space.
* `EllipticPdes.Extension.hasWeakGradOn_evenExt`: the weak gradient of the extension.
* `EllipticPdes.Extension.eLpNorm_signedExt_le`: the bound in every `Lᵖ` seminorm.
* `EllipticPdes.Extension.integrable_signedExt`: integrability on the whole space.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)
open EllipticPdes.Embedding (HasWeakGradOn)

variable {d : ℕ}

/-- The open half space below the interface. -/
def halfSpaceNeg (j : Fin d) : Set (EuclideanSpace ℝ (Fin d)) := {x | x j < 0}

/-- `halfSpaceNeg j` is measurable. -/
theorem measurableSet_halfSpaceNeg (j : Fin d) : MeasurableSet (halfSpaceNeg j) :=
  (isOpen_lt (EuclideanSpace.proj j).continuous continuous_const).measurableSet

/-- `halfSpace j` and `halfSpaceNeg j` are disjoint. -/
theorem disjoint_halfSpace (j : Fin d) : Disjoint (halfSpace j) (halfSpaceNeg j) :=
  Set.disjoint_left.2 fun x hx hx' => by
    simp only [halfSpace, halfSpaceNeg, Set.mem_ofPred_eq] at hx hx'
    linarith

/-- Up to the null interface, the whole space is the union of the two open half spaces. -/
theorem univ_ae_eq_union (j : Fin d) :
    (Set.univ : Set (EuclideanSpace ℝ (Fin d)))
      =ᵐ[volume] ((halfSpace j ∪ halfSpaceNeg j : Set (EuclideanSpace ℝ (Fin d)))) := by
  refine (MeasureTheory.ae_eq_set).mpr ⟨measure_mono_null (fun x hx => ?_) (volume_interface j),
    by simp⟩
  simp only [Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_union, halfSpace, halfSpaceNeg,
    Set.mem_ofPred_eq, not_or, not_lt] at hx
  exact le_antisymm hx.1 hx.2

/-- **Splitting of an integral over the whole space at the interface.** -/
theorem integral_split_interface {j : Fin d} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (h1 : IntegrableOn f (halfSpace j) volume) (h2 : IntegrableOn f (halfSpaceNeg j) volume) :
    ∫ x, f x = (∫ x in halfSpace j, f x) + ∫ x in halfSpaceNeg j, f x := by
  rw [← setIntegral_univ, setIntegral_congr_set (univ_ae_eq_union j),
    setIntegral_union (disjoint_halfSpace j) (measurableSet_halfSpaceNeg j) h1 h2]

/-- Reflection in the `j`-th coordinate maps `halfSpaceNeg j` onto `halfSpace j` under preimage. -/
theorem preimage_reflectLI_halfSpaceNeg (j : Fin d) :
    reflectLI j ⁻¹' halfSpaceNeg j = halfSpace j := by
  ext x
  simp only [Set.mem_preimage, halfSpaceNeg, halfSpace, Set.mem_ofPred_eq, reflectLI_apply_self,
    neg_lt_zero]

/-- **Integral over the lower half space as the reflected integral over the upper one.** -/
theorem setIntegral_halfSpaceNeg (j : Fin d) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ x in halfSpaceNeg j, f x = ∫ y in halfSpace j, f (reflectLI j y) := by
  have h := (measurePreserving_reflectLI j).setIntegral_preimage_emb
    (measurableEmbedding_reflectLI j) f (halfSpaceNeg j)
  rw [preimage_reflectLI_halfSpaceNeg] at h
  exact h.symm

/-- **Reflection of the lower half space onto the upper one**, preserving measure. -/
theorem measurePreserving_reflectLI_halfSpaceNeg (j : Fin d) :
    MeasurePreserving (reflectLI j) (volume.restrict (halfSpaceNeg j))
      (volume.restrict (halfSpace j)) := by
  have h := (measurePreserving_reflectLI j).restrict_preimage_emb
    (measurableEmbedding_reflectLI j) (halfSpace j)
  rwa [show reflectLI j ⁻¹' halfSpace j = halfSpaceNeg j from by
    rw [← preimage_reflectLI_halfSpaceNeg j, reflectLI_preimage_preimage]] at h

/-- The reflection fixes the interface. -/
theorem reflectLI_eq_self_of_interface {j : Fin d} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x j = 0) : reflectLI j x = x := by
  ext m
  rw [reflectLI_apply, reflectSign]
  by_cases hm : m = j
  · subst hm; simp [hx]
  · simp [hm]

/-- The sign a reflection attaches to a direction has absolute value `1`. -/
theorem abs_reflectSign (j k : Fin d) : |reflectSign j k| = 1 := by
  rw [reflectSign]
  split_ifs <;> norm_num

/-! ### The extension by a signed reflection -/

/-- **Extension by a signed reflection**: below the interface it takes `s` times the value at the
mirror image. It is linear in the function. -/
def signedExt (j : Fin d) (s : ℝ) :
    (EuclideanSpace ℝ (Fin d) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d) → ℝ) where
  toFun f x := if 0 ≤ x j then f x else s * f (reflectLI j x)
  map_add' f g := by funext x; by_cases h : 0 ≤ x j <;> simp [h, mul_add]
  map_smul' c f := by funext x; by_cases h : 0 ≤ x j <;> simp [h, mul_left_comm]

section signedExt

variable {j : Fin d} {s : ℝ} {f : EuclideanSpace ℝ (Fin d) → ℝ}

/-- On the closed upper half space the extension is the function. -/
theorem signedExt_of_nonneg {x : EuclideanSpace ℝ (Fin d)} (hx : 0 ≤ x j) :
    signedExt j s f x = f x := by simp [signedExt, hx]

/-- On the lower half space the extension is `s` times the function at the mirror image. -/
theorem signedExt_of_neg {x : EuclideanSpace ℝ (Fin d)} (hx : x j < 0) :
    signedExt j s f x = s * f (reflectLI j x) := by simp [signedExt, hx.not_ge]

/-- At the mirror image of a point of the upper half space, the extension is `s` times the
value at the point. -/
theorem signedExt_reflectLI {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ halfSpace j) :
    signedExt j s f (reflectLI j y) = s * f y := by
  rw [signedExt_of_neg (by rw [reflectLI_apply_self]; exact neg_lt_zero.2 hy),
    reflectLI_involutive]

/-- The extension is, almost everywhere, the sum of the function and its signed reflection, each
on its own side of the interface. -/
theorem signedExt_ae_eq : signedExt j s f =ᵐ[volume] fun x => (halfSpace j).indicator f x
    + (halfSpaceNeg j).indicator (fun y => s * f (reflectLI j y)) x := by
  refine measure_mono_null (fun x hx => ?_) (volume_interface j)
  by_contra hne
  refine hx ?_
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : x ∈ halfSpaceNeg j := h
    simp [signedExt_of_neg h, h', show x ∉ halfSpace j from fun hh => (hh.trans h).false]
  · have h' : x ∈ halfSpace j := h
    simp [signedExt_of_nonneg h.le, h', show x ∉ halfSpaceNeg j from fun hh => (h.trans hh).false]

/-- **Measurability of the extension.** -/
theorem aestronglyMeasurable_signedExt
    (hf : AEStronglyMeasurable f (volume.restrict (halfSpace j))) :
    AEStronglyMeasurable (signedExt j s f) volume := by
  have hf' : AEStronglyMeasurable (fun y => s * f (reflectLI j y))
      (volume.restrict (halfSpaceNeg j)) :=
    (hf.comp_measurePreserving (measurePreserving_reflectLI_halfSpaceNeg j)).const_mul s
  exact (((aestronglyMeasurable_indicator_iff (measurableSet_halfSpace j)).mpr hf).add
    ((aestronglyMeasurable_indicator_iff (measurableSet_halfSpaceNeg j)).mpr hf')).congr
    signedExt_ae_eq.symm

/-- **Integrability of the extension.** Each side of the interface contributes the integral over
the half space, the reflection preserving measure. -/
theorem integrable_signedExt (hf : IntegrableOn f (halfSpace j) volume) :
    Integrable (signedExt j s f) volume := by
  have hmp := measurePreserving_reflectLI_halfSpaceNeg j
  have hr : IntegrableOn (fun y => s * f (reflectLI j y)) (halfSpaceNeg j) volume :=
    ((hmp.integrable_comp_emb (measurableEmbedding_reflectLI j)).mpr hf).const_mul s
  exact ((hf.integrable_indicator (measurableSet_halfSpace j)).add
    (hr.integrable_indicator (measurableSet_halfSpaceNeg j))).congr signedExt_ae_eq.symm

/-- **Bound for the extension in every `Lᵖ` seminorm.** The reflection preserves measure and `s`
has absolute value `1`, so each side contributes the seminorm on the half space. -/
theorem eLpNorm_signedExt_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hs : |s| = 1)
    (hf : AEStronglyMeasurable f (volume.restrict (halfSpace j))) :
    eLpNorm (signedExt j s f) p volume ≤ 2 * eLpNorm f p (volume.restrict (halfSpace j)) := by
  have hmp := measurePreserving_reflectLI_halfSpaceNeg j
  have hf' : AEStronglyMeasurable (fun y => f (reflectLI j y))
      (volume.restrict (halfSpaceNeg j)) := hf.comp_measurePreserving hmp
  have hsign : eLpNorm (fun y => s * f (reflectLI j y)) p (volume.restrict (halfSpaceNeg j))
      ≤ eLpNorm f p (volume.restrict (halfSpace j)) := by
    rw [← eLpNorm_comp_measurePreserving hf hmp]
    refine eLpNorm_mono_ae (hf'.const_mul s) (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs, hs, one_mul]
    exact le_rfl
  calc eLpNorm (signedExt j s f) p volume
      = eLpNorm (fun x => (halfSpace j).indicator f x + (halfSpaceNeg j).indicator
          (fun y => s * f (reflectLI j y)) x) p volume := eLpNorm_congr_ae signedExt_ae_eq
    _ ≤ eLpNorm ((halfSpace j).indicator f) p volume
        + eLpNorm ((halfSpaceNeg j).indicator fun y => s * f (reflectLI j y)) p volume :=
        eLpNorm_add_le hp
    _ ≤ eLpNorm f p (volume.restrict (halfSpace j))
        + eLpNorm f p (volume.restrict (halfSpace j)) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_halfSpace j).nullMeasurableSet,
          eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_halfSpaceNeg j).nullMeasurableSet]
        exact add_le_add le_rfl hsign
    _ = 2 * eLpNorm f p (volume.restrict (halfSpace j)) := (two_mul _).symm

/-- **An integral against a test function, over the extension.** Splitting at the interface and
reflecting the lower half puts the integral on the upper half space, against `h + s (h ∘ R)`. -/
theorem integral_signedExt_mul {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : IntegrableOn f (halfSpace j) volume) (hh : Continuous h) (hhcs : HasCompactSupport h) :
    ∫ x, signedExt j s f x * h x
      = ∫ x in halfSpace j, f x * (h x + s * h (reflectLI j x)) := by
  have hI : IntegrableOn (fun x => signedExt j s f x * h x) Set.univ volume :=
    (integrable_signedExt hf).integrableOn.mul_of_hasCompactSupport hh hhcs
  have hR : Continuous fun x => s * h (reflectLI j x) :=
    continuous_const.mul (hh.comp (reflectLI j).continuous)
  have hRcs : HasCompactSupport fun x => s * h (reflectLI j x) :=
    (hhcs.comp_homeomorph (reflectLI j).toHomeomorph).mul_left
  have hsplit := integral_split_interface (j := j) (f := fun x => signedExt j s f x * h x)
    (hI.mono_set (Set.subset_univ _)) (hI.mono_set (Set.subset_univ _))
  have e1 : ∫ x in halfSpace j, signedExt j s f x * h x = ∫ x in halfSpace j, f x * h x :=
    setIntegral_congr_fun (measurableSet_halfSpace j) fun y hy => by
      rw [signedExt_of_nonneg (le_of_lt hy)]
  have e2 : ∫ y in halfSpace j, signedExt j s f (reflectLI j y) * h (reflectLI j y)
      = ∫ y in halfSpace j, f y * (s * h (reflectLI j y)) :=
    setIntegral_congr_fun (measurableSet_halfSpace j) fun y hy => by
      rw [signedExt_reflectLI hy]; ring
  rw [hsplit, setIntegral_halfSpaceNeg, e1, e2, ← integral_add
    (hf.mul_of_hasCompactSupport hh hhcs) (hf.mul_of_hasCompactSupport hR hRcs)]
  exact setIntegral_congr_fun (measurableSet_halfSpace j) fun y _ => by ring

end signedExt

/-! ### The reflected extension -/

/-- **Reflected extension of a function**: below the interface it takes the value at the
mirror image. -/
def evenExt (j : Fin d) : (EuclideanSpace ℝ (Fin d) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d) → ℝ) :=
  signedExt j 1

/-- **Reflected extension of a gradient**, with a sign in the normal direction. -/
def evenExtGrad (j : Fin d) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  signedExt j (reflectSign j k) (g k)

/-- **Weak gradient of the reflected extension on the whole space.** Splitting the integral
at the interface and reflecting the lower half tests the class against `φ + s (φ ∘ R)`, which in
the normal direction is odd and so vanishes on the interface. That is the hypothesis under which
no boundary term survives. -/
theorem hasWeakGradOn_evenExt {j : Fin d} {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u (halfSpace j) volume)
    (hg : ∀ k, IntegrableOn (g k) (halfSpace j) volume)
    (hwg : HasWeakGradOn (halfSpace j) u g) :
    HasWeakGradOn Set.univ (evenExt j u) (evenExtGrad j g) := by
  intro φ hφ hφcs _ k
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφR : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (reflectLI j y)) := contDiff_comp_reflect hφ j
  set s : ℝ := reflectSign j k with hs
  set ψ : EuclideanSpace ℝ (Fin d) → ℝ := fun x => φ x + s * φ (reflectLI j x) with hψ
  have hψsm : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.add (contDiff_const.mul hφR)
  have hψcs : HasCompactSupport ψ := hφcs.add (hasCompactSupport_comp_reflect hφcs j).mul_left
  -- the derivative of the combination
  have hpsi : ∀ x, partialD k ψ x = partialD k φ x + partialD k φ (reflectLI j x) := fun x => by
    have h1 : partialD k ψ x
        = partialD k φ x + s * partialD k (fun z => φ (reflectLI j z)) x := by
      rw [hψ, partialD, fderiv_fun_add (hφd x) ((hφR.differentiable (by simp) x).const_mul s),
        fderiv_const_mul (hφR.differentiable (by simp) x)]
      simp [partialD]
    rw [h1, partialD_comp_reflect hφd j k x, ← mul_assoc, hs, reflectSign_mul_self, one_mul]
  have hLHS : ∫ x in Set.univ, evenExt j u x * partialD k φ x
      = ∫ y in halfSpace j, u y * partialD k ψ y := by
    rw [setIntegral_univ, evenExt, integral_signedExt_mul hu (hφ.continuous_partialD (by simp) k)
      (hφcs.partialD k)]
    exact setIntegral_congr_fun (measurableSet_halfSpace j) fun y _ => by
      rw [hpsi, one_mul]
  have hRHS : ∫ x in Set.univ, evenExtGrad j g k x * φ x
      = ∫ y in halfSpace j, g k y * ψ y := by
    rw [setIntegral_univ, evenExtGrad, integral_signedExt_mul (hg k) hφ.continuous hφcs]
  rw [hLHS, hRHS]
  by_cases hk : k = j
  · subst hk
    exact integral_partialD_of_eq hu (hg k) hwg hψsm hψcs fun z hz => by
      simp [hψ, reflectLI_eq_self_of_interface hz, hs, reflectSign]
  · exact integral_partialD_of_ne hk hu (hg k) hwg hψsm hψcs

end EllipticPdes.Extension
