import KLS.ConvexSubgradient
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Affine covariance of actual subgradient images

Invertible affine changes of the input act on support slopes by the adjoint
linear map. Positive rescaling of the potential rescales its support slopes.
The resulting volume formulas concern the actual set-valued subgradient image
and require no differentiability or Monge--Ampere regularity hypothesis.
-/

open MeasureTheory InnerProductSpace Set
open scoped ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem mem_convexSubgradient_affine_iff
    {u : Space n → ℝ} (A : Space n ≃ₗ[ℝ] Space n) (b : Space n)
    (x p : Space n) :
    A.toLinearMap.adjoint p ∈ convexSubgradient (fun z => u (A z + b)) x ↔
      p ∈ convexSubgradient u (A x + b) := by
  constructor
  · intro hp y
    have hh := hp (A.symm (y - b))
    rw [LinearMap.adjoint_inner_left, map_sub] at hh
    simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
      sub_add_cancel, sub_sub, add_comm b (A x)] using hh
  · intro hp y
    have hh := hp (A y + b)
    rw [LinearMap.adjoint_inner_left, map_sub]
    simpa only [LinearEquiv.coe_toLinearMap, add_sub_add_right_eq_sub] using hh

theorem adjoint_linearEquiv_symm_apply (A : Space n ≃ₗ[ℝ] Space n)
    (p : Space n) :
    A.toLinearMap.adjoint (A.symm.toLinearMap.adjoint p) = p := by
  apply ext_inner_right ℝ
  intro z
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  simp

theorem convexSubgradientImage_affine
    (u : Space n → ℝ) (A : Space n ≃ₗ[ℝ] Space n) (b : Space n)
    (S : Set (Space n)) :
    convexSubgradientImage (fun z => u (A z + b)) S =
      A.toLinearMap.adjoint '' convexSubgradientImage u ((fun z => A z + b) '' S) := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    refine ⟨A.symm.toLinearMap.adjoint p, ?_, adjoint_linearEquiv_symm_apply A p⟩
    refine ⟨A x + b, ⟨x, hx, rfl⟩, ?_⟩
    apply (mem_convexSubgradient_affine_iff A b x _).mp
    simpa only [adjoint_linearEquiv_symm_apply] using hp
  · rintro ⟨q, ⟨z, ⟨x, hx, rfl⟩, hq⟩, rfl⟩
    exact ⟨x, hx, (mem_convexSubgradient_affine_iff A b x q).mpr hq⟩

theorem mem_convexSubgradient_pos_mul_iff
    {u : Space n → ℝ} {c : ℝ} (hc : 0 < c) (x p : Space n) :
    c • p ∈ convexSubgradient (fun z => c * u z) x ↔
      p ∈ convexSubgradient u x := by
  constructor
  · intro hp y
    have hh := hp y
    rw [real_inner_smul_left, ← mul_add] at hh
    exact (mul_le_mul_iff_right₀ hc).mp hh
  · intro hp y
    rw [real_inner_smul_left, ← mul_add]
    exact mul_le_mul_of_nonneg_left (hp y) hc.le

theorem convexSubgradientImage_pos_mul
    (u : Space n → ℝ) {c : ℝ} (hc : 0 < c) (S : Set (Space n)) :
    convexSubgradientImage (fun z => c * u z) S =
      (fun p => c • p) '' convexSubgradientImage u S := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    have heq : c • (c⁻¹ • p) = p := by simp [smul_smul, hc.ne']
    refine ⟨c⁻¹ • p, ⟨x, hx, ?_⟩, heq⟩
    apply (mem_convexSubgradient_pos_mul_iff hc x _).mp
    rwa [heq]
  · rintro ⟨q, ⟨x, hx, hq⟩, rfl⟩
    exact ⟨x, hx, (mem_convexSubgradient_pos_mul_iff hc x q).mpr hq⟩

/-- The real adjoint has the same determinant as the original linear map. -/
theorem det_adjoint_euclidean (A : Space n →ₗ[ℝ] Space n) :
    LinearMap.det A.adjoint = LinearMap.det A := by
  let e := stdOrthonormalBasis ℝ (Space n)
  rw [← LinearMap.det_toMatrix e.toBasis A.adjoint,
    LinearMap.toMatrix_adjoint e e, Matrix.det_conjTranspose,
    LinearMap.det_toMatrix]
  simp

/-- The volume factor for an invertible affine change of the input is
the absolute determinant of its linear part. -/
theorem volume_convexSubgradientImage_affine
    (u : Space n → ℝ) (A : Space n ≃ₗ[ℝ] Space n) (b : Space n)
    (S : Set (Space n)) :
    volume (convexSubgradientImage (fun z => u (A z + b)) S) =
      ENNReal.ofReal |LinearMap.det A.toLinearMap| *
        volume (convexSubgradientImage u ((fun z => A z + b) '' S)) := by
  rw [convexSubgradientImage_affine, Measure.addHaar_image_linearMap,
    det_adjoint_euclidean]

/-- Positive vertical rescaling acts with the dimension power on the
actual subgradient-image volume. -/
theorem volume_convexSubgradientImage_pos_mul
    (u : Space n → ℝ) {c : ℝ} (hc : 0 < c) (S : Set (Space n)) :
    volume (convexSubgradientImage (fun z => c * u z) S) =
      ENNReal.ofReal (c ^ n) * volume (convexSubgradientImage u S) := by
  rw [convexSubgradientImage_pos_mul u hc S]
  change volume ((c • (LinearMap.id : Space n →ₗ[ℝ] Space n)) ''
    convexSubgradientImage u S) = _
  rw [Measure.addHaar_image_linearMap, LinearMap.det_smul, LinearMap.det_id]
  simp only [Space, finrank_euclideanSpace_fin, mul_one, abs_of_nonneg (pow_nonneg hc.le _)]

/-- Combined affine and positive vertical rescaling, as needed when
normalizing convex sections. No section regularity is assumed. -/
theorem volume_convexSubgradientImage_pos_mul_affine
    (u : Space n → ℝ) {c : ℝ} (hc : 0 < c)
    (A : Space n ≃ₗ[ℝ] Space n) (b : Space n) (S : Set (Space n)) :
    volume (convexSubgradientImage (fun z => c * u (A z + b)) S) =
      ENNReal.ofReal (c ^ n) * ENNReal.ofReal |LinearMap.det A.toLinearMap| *
        volume (convexSubgradientImage u ((fun z => A z + b) '' S)) := by
  rw [volume_convexSubgradientImage_pos_mul _ hc,
    volume_convexSubgradientImage_affine, mul_assoc]

theorem mem_convexSubgradient_add_affine_iff
    {u : Space n → ℝ} (q : Space n) (r : ℝ) (x p : Space n) :
    q + p ∈ convexSubgradient (fun z => u z + inner ℝ q z + r) x ↔
      p ∈ convexSubgradient u x := by
  constructor
  · intro hp y
    have hh := hp y
    simp only [inner_add_left, inner_sub_right] at hh ⊢
    linarith
  · intro hp y
    have hh := hp y
    simp only [inner_add_left, inner_sub_right] at hh ⊢
    linarith

/-- Adding an affine function translates every support slope. -/
theorem convexSubgradientImage_add_affine
    (u : Space n → ℝ) (q : Space n) (r : ℝ) (S : Set (Space n)) :
    convexSubgradientImage (fun z => u z + inner ℝ q z + r) S =
      (fun p => q + p) '' convexSubgradientImage u S := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    have heq : q + (p - q) = p := by abel_nf
    refine ⟨p - q, ⟨x, hx, ?_⟩, heq⟩
    apply (mem_convexSubgradient_add_affine_iff q r x _).mp
    rwa [heq]
  · rintro ⟨p, ⟨x, hx, hp⟩, rfl⟩
    exact ⟨x, hx, (mem_convexSubgradient_add_affine_iff q r x p).mpr hp⟩

/-- Subtracting or adding a supporting affine plane does not change the
Lebesgue volume of the actual subgradient image. -/
theorem volume_convexSubgradientImage_add_affine
    (u : Space n → ℝ) (q : Space n) (r : ℝ) (S : Set (Space n)) :
    volume (convexSubgradientImage (fun z => u z + inner ℝ q z + r) S) =
      volume (convexSubgradientImage u S) := by
  rw [convexSubgradientImage_add_affine]
  have hset : (fun p => q + p) '' convexSubgradientImage u S =
      (fun p => -q + p) ⁻¹' convexSubgradientImage u S := by
    ext p
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa only [Set.mem_preimage, neg_add_cancel_left] using hs
    · intro hp
      exact ⟨-q + p, hp, by simp⟩
  rw [hset, measure_preimage_add]

end KLS
end

#print axioms KLS.mem_convexSubgradient_affine_iff
#print axioms KLS.convexSubgradientImage_affine
#print axioms KLS.convexSubgradientImage_pos_mul
#print axioms KLS.volume_convexSubgradientImage_affine
#print axioms KLS.volume_convexSubgradientImage_pos_mul
#print axioms KLS.volume_convexSubgradientImage_pos_mul_affine
#print axioms KLS.volume_convexSubgradientImage_add_affine
