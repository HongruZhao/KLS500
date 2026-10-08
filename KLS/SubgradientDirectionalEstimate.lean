import KLS.SubgradientPolarEstimate
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Directional Alexandrov maximum estimate

The anisotropic polar rectangle may be aligned with any unit supporting
direction. The estimate therefore depends on its actual width and a norm
bound, rather than the choice of ambient coordinates.
-/

open MeasureTheory InnerProductSpace Set
open scoped Topology ENNReal BigOperators

noncomputable section
namespace KLS

variable {n : ℕ}

theorem volume_image_linearIsometryEquiv
    (e : Space n ≃ₗᵢ[ℝ] Space n) (S : Set (Space n)) :
    volume (e '' S) = volume S := by
  calc
    _ = (volume.map e) (e '' S) := by rw [e.measurePreserving.map_eq]
    _ = volume S := by
      change (volume.map e.toHomeomorph) (e '' S) = volume S
      rw [e.toHomeomorph.measurableEmbedding.map_apply]
      change volume (e ⁻¹' (e '' S)) = volume S
      rw [Set.preimage_image_eq _ e.injective]

theorem anisotropic_coordinate_box_volume
    (i : Fin n) (m δ R : ℝ) :
    volume {p : Space n | ∀ j,
      p j ∈ Set.Ioo (if j = i then 0 else -(m / (2 * n * R)))
        (if j = i then m / (2 * δ) else m / (2 * n * R))} =
      ENNReal.ofReal (m / (2 * δ)) * ENNReal.ofReal (m / (n * R)) ^ (n - 1) := by
  classical
  rw [volume_euclidean_coordinate_box]
  let F : Fin n → ℝ≥0∞ := fun j => ENNReal.ofReal
    ((if j = i then m / (2 * δ) else m / (2 * n * R)) -
     (if j = i then 0 else -(m / (2 * n * R))))
  change (∏ j : Fin n, F j) = _
  rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ i)]
  have hrest : (∏ j ∈ Finset.univ.erase i, F j) =
      ENNReal.ofReal (m / (n * R)) ^ (n - 1) := by
    calc
      _ = ∏ _j ∈ Finset.univ.erase i, ENNReal.ofReal (m / (n * R)) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        simp only [F, ite_eq_right hji]
        congr 1
        ring
      _ = _ := by simp
  rw [hrest]
  simp [F]

/-- Coordinate-free width version of the anisotropic Alexandrov estimate.
The unit vector v is an arbitrary supporting direction. -/
theorem directional_alexandrov_maximum_estimate
    (i : Fin n) {u : Space n → ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ Set.univ u)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z) {x : Space n} (hx : x ∈ K)
    (hux : u x < 0) {v : Space n} (hv : ‖v‖ = 1)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hwidth : ∀ z ∈ K, inner ℝ v (z - x) ≤ δ)
    (hnorm : ∀ z ∈ K, ‖z - x‖ ≤ R) :
    ENNReal.ofReal (-u x / (2 * δ)) *
      ENNReal.ofReal (-u x / (n * R)) ^ (n - 1) ≤
        volume (convexSubgradientImage u (interior K)) := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ i
  let e : Space n ≃ₗᵢ[ℝ] Space n := (ℝ ∙ (b - v))ᗮ.reflection
  have he : e b = v :=
    Submodule.reflection_sub ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i |>.trans hv.symm)
  let B : Set (Space n) := {p | ∀ j,
    p j ∈ Set.Ioo (if j = i then 0 else -(-u x / (2 * n * R)))
      (if j = i then -u x / (2 * δ) else -u x / (2 * n * R))}
  have hB : e '' B ⊆ convexSubgradientImage u (interior K) := by
    rintro _ ⟨p, hp, rfl⟩
    apply strictPolar_subset_convexSubgradientImage hK hucont huconvex hboundary hx
    intro z hz
    have hzK : z ∈ K := hK.isClosed.closure_eq ▸ frontier_subset_closure hz
    have hpi := hp i
    simp only [Set.mem_Ioo, ite_true] at hpi
    rw [e.inner_map_eq_flip]
    apply inner_lt_of_anisotropic_coordinate_box i (neg_pos.mpr hux) hδ hR hpi.1.le hpi.2
    · intro j hji
      have hpj := hp j
      simpa only [ite_eq_right hji, Set.mem_Ioo, ← abs_lt] using hpj
    · have hi : (e.symm (z - x)) i = inner ℝ v (z - x) := by
        rw [← EuclideanSpace.basisFun_inner, ← e.inner_map_eq_flip]
        exact congrArg (fun w => inner ℝ w (z - x)) he
      rw [hi]
      exact hwidth z hzK
    · intro j _
      have hj := PiLp.norm_apply_le (e.symm (z - x)) j
      rw [Real.norm_eq_abs, e.symm.norm_map] at hj
      exact hj.trans (hnorm z hzK)
  calc
    _ = volume B := (anisotropic_coordinate_box_volume i (-u x) δ R).symm
    _ = volume (e '' B) := (volume_image_linearIsometryEquiv e B).symm
    _ ≤ _ := measure_mono hB

end KLS
end

#print axioms KLS.volume_image_linearIsometryEquiv
#print axioms KLS.anisotropic_coordinate_box_volume
#print axioms KLS.directional_alexandrov_maximum_estimate
