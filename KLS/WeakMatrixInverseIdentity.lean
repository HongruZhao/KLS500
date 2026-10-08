import KLS.WeakMatrixProduct
import KLS.WeakMatrixAdjugate

open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Differentiating the genuine matrix identity A A^-1 = I identifies the
inverse derivative with its ordered expression. -/
theorem weak_matrixInverse_derivative_eq
    {A DA DJ : Space n → Matrix (Fin n) (Fin n) ℝ} {k : Fin n}
    (hDA : ∀ i j, HasLocalWeakCoordinateDerivative (fun x => A x i j) (fun x => DA x i j) k)
    (hDJ : ∀ i j, HasLocalWeakCoordinateDerivative (fun x => (A x)⁻¹ i j) (fun x => DJ x i j) k)
    (hA : ∀ i j K, IsCompact K → MemLp (fun x => A x i j) ∞ (volume.restrict K))
    (hJ : ∀ i j K, IsCompact K → MemLp (fun x => (A x)⁻¹ i j) ∞ (volume.restrict K))
    (hDAloc : ∀ i j K, IsCompact K → MemLp (fun x => DA x i j) 2 (volume.restrict K))
    (hDJloc : ∀ i j K, IsCompact K → MemLp (fun x => DJ x i j) 2 (volume.restrict K))
    (hdet : ∀ᵐ x, (A x).det ≠ 0) :
    ∀ᵐ x, DJ x = -((A x)⁻¹ * DA x * (A x)⁻¹) := by
  have he (i j : Fin n) : ∀ᵐ x, (DA x * (A x)⁻¹ + A x * DJ x) i j = 0 := by
    have hp := hasLocalWeakCoordinateDerivative_matrixMul hDA hDJ hA hJ hDAloc hDJloc i j
    have hsource : (fun x => (A x * (A x)⁻¹) i j) =ᵐ[volume]
        (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) i j) := by
      filter_upwards [hdet] with x hx
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx)]
    have hpc := hp.congr_ae hsource Filter.EventuallyEq.rfl
    have hloc : LocallyIntegrable (fun x => (DA x * (A x)⁻¹ + A x * DJ x) i j) volume := by
      apply locallyIntegrable_of_memLp_two_on_compacts
      intro K hK
      exact (memLp_two_matrixMul_right (fun a b => hDAloc a b K hK) (fun a b => hJ a b K hK) i j).add
        (memLp_two_matrixMul_left (fun a b => hA a b K hK) (fun a b => hDJloc a b K hK) i j)
    exact hpc.unique (hasLocalWeakCoordinateDerivative_const ((1 : Matrix (Fin n) (Fin n) ℝ) i j) k)
      hloc continuous_const.locallyIntegrable
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => he i j)), hdet] with x hx hdx
  have hz : DA x * (A x)⁻¹ + A x * DJ x = 0 := by
    ext i j
    exact hx i j
  have hu : IsUnit (A x).det := isUnit_iff_ne_zero.mpr hdx
  have hsum : (A x)⁻¹ * DA x * (A x)⁻¹ + DJ x = 0 := by
    calc
      _ = (A x)⁻¹ * (DA x * (A x)⁻¹) + (A x)⁻¹ * (A x * DJ x) := by
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
      _ = (A x)⁻¹ * (DA x * (A x)⁻¹ + A x * DJ x) := (Matrix.mul_add _ _ _).symm
      _ = 0 := by rw [hz, Matrix.mul_zero]
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using hsum

end KLS
end
