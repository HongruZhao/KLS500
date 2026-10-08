import KLS.LocalWeakAlgebra
import KLS.BoundedCompactH1Tests

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- A divergence identity known for actual smooth compact tests extends to
C1 compact tests by the genuine local L2 and bounded local L1 mollifier limits. -/
theorem integral_divergence_of_smooth_compact_tests
    {A : Fin n → Space n → ℝ} {b : Space n → ℝ}
    (hA : ∀ i S, IsCompact S → MemLp (A i) 2 (volume.restrict S))
    (hb : LocallyIntegrable b volume)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A i x * coordinateDerivative ψ i x) = ∫ x, b x * ψ x)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∑ i, ∫ x, A i x * coordinateDerivative ψ i x) = ∫ x, b x * ψ x := by
  have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hc
  have hd (i : Fin n) : ∀ S, IsCompact S →
      MemLp (coordinateDerivative ψ i) 2 (volume.restrict S) := by
    intro S _
    exact ((contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hc i)).restrict S
  have hp (i : Fin n) :=
    (hasLocalWeakCoordinateDerivative_of_contDiff hψ i).localL2_pairing_mollify
      hψ2 hc (hd i) (hA i)
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hc
  have hr := bounded_compact_mollify_localL1_pairing hψ.continuous.locallyIntegrable hc
    (Eventually.of_forall hC) hb
  have hl := tendsto_finsetSum Finset.univ (fun i _ => (hp i).2)
  have he : (fun k => ∑ i, ∫ x, A i x * coordinateDerivative (mollify k ψ) i x) =
      fun k => ∫ x, b x * mollify k ψ x := by
    funext k
    exact hdiv _ (mollify_contDiff hψ.continuous.locallyIntegrable k) (hasCompactSupport_mollify hc k)
  rw [he] at hl
  exact tendsto_nhds_unique hl hr.2

/-- Differentiating a genuine divergence identity commutes distributional
 derivatives. All second derivatives fall on smooth compact tests only. -/
theorem integral_divergence_coordinateDerivative
    {A DA : Fin n → Space n → ℝ} {b db : Space n → ℝ} {k : Fin n}
    (hDA : ∀ i, HasLocalWeakCoordinateDerivative (A i) (DA i) k)
    (hdb : HasLocalWeakCoordinateDerivative b db k)
    (hDAl : ∀ i S, IsCompact S → MemLp (DA i) 2 (volume.restrict S))
    (hdbl : LocallyIntegrable db volume)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A i x * coordinateDerivative ψ i x) = ∫ x, b x * ψ x)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∑ i, ∫ x, DA i x * coordinateDerivative ψ i x) = ∫ x, db x * ψ x := by
  apply integral_divergence_of_smooth_compact_tests hDAl hdbl _ hψ hc
  intro φ hφ hφc
  have hd (i : Fin n) : ContDiff ℝ 1 (coordinateDerivative φ i) :=
    contDiff_coordinateDerivative hφ (by simp) i
  have he (i : Fin n) : coordinateDerivative (coordinateDerivative φ k) i =
      coordinateDerivative (coordinateDerivative φ i) k := by
    funext x
    exact (coordinateHessian_symmetric (hφ.of_le (by simp)) x).apply k i
  have hAi (i : Fin n) : (∫ x, A i x * coordinateDerivative (coordinateDerivative φ k) i x) =
      -(∫ x, DA i x * coordinateDerivative φ i x) := by
    rw [he i]
    exact hDA i _ (hd i) (hasCompactSupport_coordinateDerivative hφc i)
  have hh := hdiv _ (hd k) (hasCompactSupport_coordinateDerivative hφc k)
  simp_rw [hAi] at hh
  rw [Finset.sum_neg_distrib, hdb φ (hφ.of_le (by simp)) hφc] at hh
  exact neg_injective hh

end KLS
end
