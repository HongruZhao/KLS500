import KLS.SubgradientAffineCovariance
import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Affine section normalization formulas

These adapters express the exact subgradient and volume covariance using the
continuous affine equivalences returned by convex-body normalization. Their
Jacobian formulas apply to arbitrary sets, without a measurability hypothesis.
-/

open MeasureTheory InnerProductSpace Set
open scoped ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem continuousAffineEquiv_apply_eq_linear_add
    (e : Space n ≃ᴬ[ℝ] Space n) (z : Space n) :
    e z = e.linear z + e 0 := by
  simpa only [vadd_eq_add, add_zero, ContinuousAffineEquiv.coe_coe] using
    e.toAffineEquiv.map_vadd 0 z

theorem convexSubgradientImage_continuousAffineEquiv
    (u : Space n → ℝ) (e : Space n ≃ᴬ[ℝ] Space n) (S : Set (Space n)) :
    convexSubgradientImage (fun z => u (e z)) S =
      e.linear.toLinearMap.adjoint '' convexSubgradientImage u (e '' S) := by
  simpa only [← continuousAffineEquiv_apply_eq_linear_add e] using
    convexSubgradientImage_affine u e.linear (e 0) S

theorem volume_convexSubgradientImage_continuousAffineEquiv
    (u : Space n → ℝ) (e : Space n ≃ᴬ[ℝ] Space n) (S : Set (Space n)) :
    volume (convexSubgradientImage (fun z => u (e z)) S) =
      ENNReal.ofReal |LinearMap.det e.linear.toLinearMap| *
        volume (convexSubgradientImage u (e '' S)) := by
  rw [convexSubgradientImage_continuousAffineEquiv,
    Measure.addHaar_image_linearMap, det_adjoint_euclidean]

theorem volume_convexSubgradientImage_pos_mul_continuousAffineEquiv
    (u : Space n → ℝ) {c : ℝ} (hc : 0 < c)
    (e : Space n ≃ᴬ[ℝ] Space n) (S : Set (Space n)) :
    volume (convexSubgradientImage (fun z => c * u (e z)) S) =
      ENNReal.ofReal (c ^ n) * ENNReal.ofReal |LinearMap.det e.linear.toLinearMap| *
        volume (convexSubgradientImage u (e '' S)) := by
  rw [volume_convexSubgradientImage_pos_mul _ hc,
    volume_convexSubgradientImage_continuousAffineEquiv, mul_assoc]

/-- Lebesgue volume has the exact affine Jacobian on arbitrary sets. -/
theorem volume_image_continuousAffineEquiv
    (e : Space n ≃ᴬ[ℝ] Space n) (S : Set (Space n)) :
    volume (e '' S) =
      ENNReal.ofReal |LinearMap.det e.linear.toLinearMap| * volume S := by
  have hset : e '' S =
      (fun p => -(e 0) + p) ⁻¹' (e.linear.toLinearMap '' S) := by
    ext p
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s, hs, ?_⟩
      rw [continuousAffineEquiv_apply_eq_linear_add e s]
      change e.linear s = -e 0 + (e.linear s + e 0)
      abel_nf
    · rintro ⟨s, hs, heq⟩
      refine ⟨s, hs, ?_⟩
      rw [continuousAffineEquiv_apply_eq_linear_add e s]
      change e.linear s = -e 0 + p at heq
      rw [heq]
      abel_nf
  rw [hset, measure_preimage_add, Measure.addHaar_image_linearMap]

/-- The inverse affine Jacobian, also without a measurability hypothesis. -/
theorem volume_preimage_continuousAffineEquiv
    (e : Space n ≃ᴬ[ℝ] Space n) (S : Set (Space n)) :
    volume (e ⁻¹' S) =
      ENNReal.ofReal |LinearMap.det e.symm.linear.toLinearMap| * volume S := by
  rw [show e ⁻¹' S = e.symm '' S from by
    ext p
    constructor
    · intro hp
      exact ⟨e p, hp, e.symm_apply_apply p⟩
    · rintro ⟨s, hs, rfl⟩
      simpa only [Set.mem_preimage, e.apply_symm_apply] using hs]
  exact volume_image_continuousAffineEquiv e.symm S

/-- The product of a set's volume with its subgradient-image volume is
invariant under an invertible affine change of coordinates. -/
theorem volume_mul_subgradientImage_continuousAffineEquiv
    (u : Space n → ℝ) (e : Space n ≃ᴬ[ℝ] Space n) (S : Set (Space n)) :
    volume S * volume (convexSubgradientImage (fun z => u (e z)) S) =
      volume (e '' S) * volume (convexSubgradientImage u (e '' S)) := by
  rw [volume_convexSubgradientImage_continuousAffineEquiv,
    volume_image_continuousAffineEquiv]
  ac_rfl

end KLS
end

#print axioms KLS.convexSubgradientImage_continuousAffineEquiv
#print axioms KLS.volume_convexSubgradientImage_pos_mul_continuousAffineEquiv
#print axioms KLS.volume_image_continuousAffineEquiv
#print axioms KLS.volume_preimage_continuousAffineEquiv
#print axioms KLS.volume_mul_subgradientImage_continuousAffineEquiv
