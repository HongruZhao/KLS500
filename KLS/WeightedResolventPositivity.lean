import KLS.WeightedResolventSmoothOrder
import KLS.WeightedDistributionPositivity

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Nonnegative smooth forcing has a nonnegative actual resolvent, with
its classical representative constructed by elliptic regularity. -/
theorem weightedMassResolvent_nonneg_smooth_forcing
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    {g : Space n → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 (potentialMeasure φ))
    (hg0 : ∀ᵐ x ∂potentialMeasure φ, 0 ≤ g x) :
    ∀ᵐ x ∂potentialMeasure φ, 0 ≤ weightedMassResolvent φ ht (hg2.toLp g) x := by
  obtain ⟨f, hf, _, _, _, hfμ, _, _⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht hg hg2
  have hin : ∀ᵐ x ∂potentialMeasure φ, 0 ≤ hg2.toLp g x := by
    filter_upwards [hg0, hg2.coeFn_toLp] with x hx hy
    simpa only [hy] using hx
  have hnonneg := weightedMassResolvent_lower_bound_of_representative
    (hφ.of_le (by simp)) ht (hg2.toLp g) (hf.of_le (by simp)) hfμ hin
  filter_upwards [hfμ] with x hx
  rw [← hx]
  exact hnonneg x

/-- The actual full resolvent preserves positivity for arbitrary weighted-L2
forcing. Self-adjointness transfers the proved smooth-domain positivity to
compact nonnegative tests, and actual mollifiers recover the almost-everywhere sign. -/
theorem weightedMassResolvent_nonneg
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ))
    (hg0 : ∀ᵐ x ∂potentialMeasure φ, 0 ≤ g x) :
    ∀ᵐ x ∂potentialMeasure φ, 0 ≤ weightedMassResolvent φ ht g x := by
  apply ae_nonneg_of_weighted_integral_smooth_nonneg (φ := φ)
    (f := (weightedMassResolvent φ ht g : Space n → ℝ)) hφ
    (Lp.memLp (weightedMassResolvent φ ht g))
  intro ψ hψ hc hψ0
  have hψ2 : MemLp ψ 2 (potentialMeasure φ) :=
    memLp_of_continuous_hasCompactSupport hφ.continuous hψ.continuous hc
  have hp := weightedMassResolvent_nonneg_smooth_forcing hφ ht hψ hψ2
    (Eventually.of_forall hψ0)
  have hs := weightedMassResolvent_symmetric (φ := φ) ht g (hψ2.toLp ψ)
  rw [MeasureTheory.L2.real_inner_eq_integral, MeasureTheory.L2.real_inner_eq_integral] at hs
  have hleft : (∫ x, weightedMassResolvent φ ht g x * hψ2.toLp ψ x ∂potentialMeasure φ) =
      ∫ x, weightedMassResolvent φ ht g x * ψ x ∂potentialMeasure φ :=
    integral_congr_ae (EventuallyEq.rfl.mul hψ2.coeFn_toLp)
  rw [hleft] at hs
  rw [hs]
  apply integral_nonneg_of_ae
  filter_upwards [hg0,hp] with x hx hy
  exact mul_nonneg hx hy

/-- Order preservation holds on the whole actual weighted-L2 space. -/
theorem weightedMassResolvent_order
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    (g h : Lp ℝ 2 (potentialMeasure φ))
    (hgh : ∀ᵐ x ∂potentialMeasure φ, g x ≤ h x) :
    ∀ᵐ x ∂potentialMeasure φ,
      weightedMassResolvent φ ht g x ≤ weightedMassResolvent φ ht h x := by
  have hdiff : ∀ᵐ x ∂potentialMeasure φ, 0 ≤ (h-g) x := by
    filter_upwards [hgh, Lp.coeFn_sub h g] with x hx hy
    simpa only [hy, Pi.sub_apply] using sub_nonneg.mpr hx
  have hp := weightedMassResolvent_nonneg hφ ht (h-g) hdiff
  rw [map_sub] at hp
  filter_upwards [hp, Lp.coeFn_sub (weightedMassResolvent φ ht h)
    (weightedMassResolvent φ ht g)] with x hx hy
  rw [hy] at hx
  exact sub_nonneg.mp hx

end KLS
end
