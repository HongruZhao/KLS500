import KLS.WeightedResolventMaximumPrinciple

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Order preservation for classical representatives follows from the genuine
maximum principle applied to their actual resolvent difference. -/
theorem weightedMassResolvent_order_of_representatives
    (hφ : ContDiff ℝ 1 φ) {t : ℝ} (ht : 0 < t)
    (g h : Lp ℝ 2 (potentialMeasure φ)) {f u : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hu : ContDiff ℝ 1 u)
    (hfμ : f =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht g : Space n → ℝ))
    (huμ : u =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht h : Space n → ℝ))
    (hgh : ∀ᵐ x ∂potentialMeasure φ, g x ≤ h x) : ∀ x, f x ≤ u x := by
  have hdiff : (fun x => f x - u x) =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (g - h) : Space n → ℝ) := by
    rw [map_sub]
    exact (hfμ.sub huμ).trans (Lp.coeFn_sub _ _).symm
  have hbound : ∀ᵐ x ∂potentialMeasure φ, (g - h) x ≤ 0 := by
    filter_upwards [hgh, Lp.coeFn_sub g h] with x hx hy
    simpa only [hy, Pi.sub_apply] using sub_nonpos.mpr hx
  have hmax := weightedMassResolvent_upper_bound_of_representative
    hφ ht (g - h) (hf.sub hu) hdiff hbound
  intro x
  exact sub_nonpos.mp (hmax x)

/-- Smooth weighted-L2 forcing has order-preserving actual resolvent values.
All solution regularity is obtained from the earlier construction. -/
theorem weightedMassResolvent_order_smooth_forcing
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    {g h : Space n → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hg2 : MemLp g 2 (potentialMeasure φ)) (hh2 : MemLp h 2 (potentialMeasure φ))
    (hgh : ∀ᵐ x ∂potentialMeasure φ, g x ≤ h x) :
    ∀ᵐ x ∂potentialMeasure φ,
      weightedMassResolvent φ ht (hg2.toLp g) x ≤ weightedMassResolvent φ ht (hh2.toLp h) x := by
  obtain ⟨f, hf, _, _, _, hfμ, _, _⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht hg hg2
  obtain ⟨u, hu, _, _, _, huμ, _, _⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht hh hh2
  have hinput : ∀ᵐ x ∂potentialMeasure φ, hg2.toLp g x ≤ hh2.toLp h x := by
    filter_upwards [hgh, hg2.coeFn_toLp, hh2.coeFn_toLp] with x hx hy hz
    simpa only [hy, hz] using hx
  have horder := weightedMassResolvent_order_of_representatives (hφ.of_le (by simp)) ht
    (hg2.toLp g) (hh2.toLp h) (hf.of_le (by simp)) (hu.of_le (by simp)) hfμ huμ hinput
  filter_upwards [hfμ, huμ] with x hx hy
  rw [← hx, ← hy]
  exact horder x

/-- A bounded smooth forcing has a bounded globally smooth actual resolvent
representative with the same bound, its genuine gradients, and exact equation. -/
theorem weightedMassResolvent_exists_bounded_smooth_representative
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    {g : Space n → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 (potentialMeasure φ)) {M : ℝ}
    (hgM : ∀ᵐ x ∂potentialMeasure φ, |g x| ≤ M) :
    ∃ f : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ MemLp f 2 (potentialMeasure φ) ∧
      (∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ)) ∧
      f =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ) ∧
      (∀ x, |f x| ≤ M) ∧
      (∫ x, f x ∂potentialMeasure φ) = ∫ x, g x ∂potentialMeasure φ ∧
      ∀ x, f x - t * weightedDiffusion φ f x = g x := by
  obtain ⟨f, hf, hf2, hdf, _, hfμ, hfm, heq⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht hg hg2
  have hupper : ∀ᵐ x ∂potentialMeasure φ, hg2.toLp g x ≤ M := by
    filter_upwards [hgM, hg2.coeFn_toLp] with x hx hy
    rw [hy]
    exact (abs_le.mp hx).2
  have hlower : ∀ᵐ x ∂potentialMeasure φ, -M ≤ hg2.toLp g x := by
    filter_upwards [hgM, hg2.coeFn_toLp] with x hx hy
    rw [hy]
    exact (abs_le.mp hx).1
  have hu := weightedMassResolvent_upper_bound_of_representative (hφ.of_le (by simp)) ht
    (hg2.toLp g) (hf.of_le (by simp)) hfμ hupper
  have hl := weightedMassResolvent_lower_bound_of_representative (hφ.of_le (by simp)) ht
    (hg2.toLp g) (hf.of_le (by simp)) hfμ hlower
  exact ⟨f, hf, hf2, hdf, hfμ, fun x => abs_le.mpr ⟨hl x, hu x⟩, hfm, heq⟩

end KLS
end
