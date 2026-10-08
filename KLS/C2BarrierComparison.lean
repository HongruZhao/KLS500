import KLS.MomentFullViscosity
import KLS.WeightedDiffusionLinear

/-! Comparison of an actual weak Alexandrov solution with arbitrary smooth
strict barriers. No Hessian or second differentiability of the weak solution
is assumed. The proof uses contact tests at an actual interior extremum. -/
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped Topology ContDiff
noncomputable section
namespace KLS

variable {n : ℕ}

lemma coordinateHessian_add_const (ψ : Space n → ℝ) (c : ℝ) (x : Space n) :
    coordinateHessian (fun y => ψ y + c) x = coordinateHessian ψ x := by
  have hd (i : Fin n) : coordinateDerivative (fun y => ψ y + c) i =
      coordinateDerivative ψ i := by
    funext y
    simp only [coordinateDerivative, fderiv_add_const]
  ext i j
  change coordinateDerivative (coordinateDerivative (fun y => ψ y + c) j) i x =
    coordinateDerivative (coordinateDerivative ψ j) i x
  rw [hd]

/-- A smooth strict upper barrier controls a weak Alexandrov solution on a
compact comparison set. Only the barrier has a Hessian. -/
theorem le_of_strict_c2_upper_barrier
    {u f ψ : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    (hf : Continuous f)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    {K : Set (Space n)} (hK : IsCompact K) (hψ : ContDiff ℝ 2 ψ)
    (hboundary : ∀ x ∈ frontier K, u x ≤ ψ x)
    (hstrict : ∀ x ∈ interior K, (coordinateHessian ψ x).det < f x) :
    ∀ x ∈ K, u x ≤ ψ x := by
  intro x hx
  by_contra hnot
  have hcross : 0 < u x - ψ x := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ (hu.sub hψ.continuous).continuousOn
  have hpos : 0 < u z - ψ z := hcross.trans_le (hmax hx)
  have hzint : z ∈ interior K := by
    by_contra hn
    have hb := hboundary z ((mem_frontier_iff_notMem_interior hz).mpr hn)
    linarith
  let d := u z - ψ z
  have htouch : ∀ᶠ y in 𝓝 z, u y ≤ ψ y + d := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hzint] with y hy
    have hm := hmax hy
    dsimp [d]
    change u y - ψ y ≤ u z - ψ z at hm
    linarith
  have hcontact : u z = ψ z + d := by dsimp [d]; ring
  have hdet := det_ge_density_of_convex_c2_upper_touch hu huc hf.continuousAt hMA
    (hψ.add contDiff_const).contDiffAt hcontact htouch
  rw [coordinateHessian_add_const] at hdet
  exact (not_le_of_gt (hstrict z hzint)) hdet

/-- A smooth strict lower barrier controls a weak Alexandrov solution. Its
positive semidefinite Hessian is ordinary comparator data, not regularity of u. -/
theorem le_of_strict_c2_lower_barrier
    {u f ψ : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    {K : Set (Space n)} (hK : IsCompact K) (hψ : ContDiff ℝ 2 ψ)
    (hboundary : ∀ x ∈ frontier K, ψ x ≤ u x)
    (hH : ∀ x ∈ interior K, (coordinateHessian ψ x).PosSemidef)
    (hstrict : ∀ x ∈ interior K, f x < (coordinateHessian ψ x).det) :
    ∀ x ∈ K, ψ x ≤ u x := by
  intro x hx
  by_contra hnot
  have hcross : 0 < ψ x - u x := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ (hψ.continuous.sub hu).continuousOn
  have hpos : 0 < ψ z - u z := hcross.trans_le (hmax hx)
  have hzint : z ∈ interior K := by
    by_contra hn
    have hb := hboundary z ((mem_frontier_iff_notMem_interior hz).mpr hn)
    linarith
  let d := u z - ψ z
  have htouch : ∀ᶠ y in 𝓝 z, ψ y + d ≤ u y := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hzint] with y hy
    have hm := hmax hy
    dsimp [d]
    change ψ y - u y ≤ ψ z - u z at hm
    linarith
  have hcontact : u z = ψ z + d := by dsimp [d]; ring
  have htestH : (coordinateHessian (fun y => ψ y + d) z).PosSemidef := by
    rw [coordinateHessian_add_const]
    exact hH z hzint
  have hdet := det_le_density_of_c2_semidefinite_lower_touch hu huc hf.continuousAt
    (hf0 z) hMA (hψ.add contDiff_const).contDiffAt htestH hcontact htouch
  rw [coordinateHessian_add_const] at hdet
  exact (not_le_of_gt (hstrict z hzint)) hdet

end KLS
end
