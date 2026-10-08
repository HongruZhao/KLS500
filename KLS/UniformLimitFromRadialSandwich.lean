import KLS.WeightedAverageSandwich
import KLS.RadialKernelUniformBounds

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Uniform convergence follows from actual weighted L1 convergence,
vanishing primal-dual gaps, and upper/lower radial averages. No modulus of
continuity or pointwise convergence of the original sequence is assumed. -/
theorem tendstoUniformlyOn_of_radial_primal_dual_sandwich
    {w v : ℕ → Space n → ℝ} {h χ : Space n → ℝ} {e : ℕ → ℝ}
    (hw : ∀ j, Continuous (w j)) (hv : ∀ j, Continuous (v j)) (hh : Continuous h)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    {r s R : ℝ} (hrs : r < s) (hR : 0 < R)
    (hχone : ∀ x ∈ closedBall (0 : Space n) s, χ x = 1)
    (hE : Tendsto (fun j => ∫ x, χ x * |w j x - h x|) atTop (𝓝 0))
    (hG : Tendsto (fun j => ∫ x, χ x * (w j x - v j x)) atTop (𝓝 0))
    (he : Tendsto e atTop (𝓝 0))
    (hgap : ∀ᶠ j in atTop, ∀ x, 0 ≤ χ x * (w j x - v j x))
    (hmeans : ∀ t : ℝ, 0 < t → t < R → ∀ᶠ j in atTop,
      ∀ c ∈ closedBall (0 : Space n) r,
        w j c ≤ (∫ x, w j x * radialAverageKernel (normalizedRadialProfile n) c t x) + e j ∧
        (∫ x, v j x * radialAverageKernel (normalizedRadialProfile n) c t x) - e j ≤ v j c ∧
        v j c ≤ w j c) :
    TendstoUniformlyOn w h atTop (closedBall (0 : Space n) r) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have hu := (isCompact_closedBall (0 : Space n) s).uniformContinuousOn_of_continuous hh.continuousOn
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff.mp hu (η / 2) (by positivity)
  let t := min (R / 2) (min ((s-r) / 2) (δ / 2))
  have ht : 0 < t := lt_min (by positivity) (lt_min (by linarith) (by positivity))
  have htR : t < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hts : r + t ≤ s := by
    have ht2 : t ≤ (s-r) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have htδ : t < δ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  let B := (radialKernelMass n)⁻¹ / t ^ n
  have hB : 0 ≤ B := div_nonneg (inv_nonneg.mpr (radialKernelMass_pos n).le) (pow_nonneg ht.le n)
  have hlim : Tendsto (fun j => B * ((∫ x, χ x * |w j x - h x|) +
      (∫ x, χ x * (w j x - v j x))) + e j) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using ((hE.add hG).const_mul B).add he
  have hsmall := hlim.eventually_lt_const (by positivity : (0 : ℝ) < η / 2)
  filter_upwards [hgap, hmeans t ht htR, hsmall] with j hjgap hjmean hjsmall
  intro c hc
  let κ := radialAverageKernel (normalizedRadialProfile n) c t
  have hκs : tsupport κ ⊆ closedBall (0 : Space n) s :=
    normalizedRadialKernel_tsupport_subset_centered_closedBall hc ht hts
  have hos : ∀ x ∈ tsupport κ, |h x - h c| ≤ η / 2 := by
    intro x hx
    have hxc : dist x c ≤ t :=
      tsupport_radialAverageKernel_subset_closedBall
        (fun _ hs => normalizedRadialProfile_eq_zero n hs) c ht hx
    have hhxc := hosc x (hκs hx) c (closedBall_subset_closedBall hrs.le hc) (hxc.trans_lt htδ)
    exact (show |h x - h c| < η / 2 by simpa only [Real.dist_eq] using hhxc).le
  have hsand := abs_primal_sub_limit_le_weighted_average_errors (hw j) (hv j) hh
    hχ hχc (continuous_normalizedRadialKernel c t) (hasCompactSupport_normalizedRadialKernel c ht)
    hχ0 (fun x => radialAverageKernel_nonneg (normalizedRadialProfile_nonneg n) c x ht)
    (integral_normalizedRadialKernel c ht) (fun x hx => hχone x (hκs hx)) hjgap hB
    (fun x => normalizedRadialKernel_le c x ht) hos (hjmean c hc).1
    (hjmean c hc).2.1 (hjmean c hc).2.2
  rw [Real.dist_eq, abs_sub_comm]
  exact hsand.trans_lt (by linarith)

end KLS
end
