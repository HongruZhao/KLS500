import KLS.WeightedResolventTwoStepSmoothing
import KLS.WeightedMassResolventStrongLimit

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The actual mixed resolvent in the squared-difference identity has a smooth
representative with a bound depending only on the forcing supremum and times. -/
theorem weightedMassResolvent_exists_mixed_gradient_bound
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M) :
    ∃ h : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) h ∧ MemLp h 2 (potentialMeasure φ) ∧
      h =ᵐ[potentialMeasure φ] (weightedMassResolvent φ hs (weightedMassResolvent φ ht
        (weightedMassResolvent φ ht (hg2.toLp g)+weightedMassResolvent φ hs (hg2.toLp g))) : Space n → ℝ) ∧
      ∀ x, ‖gradient h x‖ ≤ B/Real.sqrt (2*t)+B/Real.sqrt (2*s) := by
  obtain ⟨z,hz,hz2,hzμ,_,hzG⟩ :=
    weightedMassResolvent_exists_two_step_gradient_bound hφ hconv ht hg hg2 hB hM hgB hgM
  obtain ⟨w,hw,hw2,hwμ,_,hwG⟩ :=
    weightedMassResolvent_exists_two_step_gradient_bound hφ hconv hs hg hg2 hB hM hgB hgM
  obtain ⟨u,hu,hu2,_,huμ,_,_,huG⟩ :=
    weightedMassResolvent_exists_gradient_bounded_representative hφ hconv hs hz hz2
      (div_nonneg hB (Real.sqrt_nonneg _)) hzG
  obtain ⟨v,hv,hv2,_,hvμ,_,_,hvG⟩ :=
    weightedMassResolvent_exists_gradient_bounded_representative hφ hconv ht hw hw2
      (div_nonneg hB (Real.sqrt_nonneg _)) hwG
  have hzLp : hz2.toLp z = weightedMassResolvent φ ht (weightedMassResolvent φ ht (hg2.toLp g)) := by
    apply Lp.ext
    exact hz2.coeFn_toLp.trans hzμ
  have hwLp : hw2.toLp w = weightedMassResolvent φ hs (weightedMassResolvent φ hs (hg2.toLp g)) := by
    apply Lp.ext
    exact hw2.coeFn_toLp.trans hwμ
  rw [hzLp] at huμ
  rw [hwLp] at hvμ
  have he : weightedMassResolvent φ hs (weightedMassResolvent φ ht
      (weightedMassResolvent φ ht (hg2.toLp g)+weightedMassResolvent φ hs (hg2.toLp g))) =
      weightedMassResolvent φ hs (weightedMassResolvent φ ht (weightedMassResolvent φ ht (hg2.toLp g)))+
      weightedMassResolvent φ ht (weightedMassResolvent φ hs (weightedMassResolvent φ hs (hg2.toLp g))) := by
    simp only [map_add]
    congr 1
    exact weightedMassResolvent_commute hφ.continuous ht hs _
  refine ⟨u+v,hu.add hv,hu2.add hv2,?_,?_⟩
  · rw [he]
    filter_upwards [huμ,hvμ,Lp.coeFn_add
      (weightedMassResolvent φ hs (weightedMassResolvent φ ht (weightedMassResolvent φ ht (hg2.toLp g))))
      (weightedMassResolvent φ ht (weightedMassResolvent φ hs (weightedMassResolvent φ hs (hg2.toLp g))))]
      with x hx hy hz
    change u x+v x=_
    rw [hz,hx,hy]
    rfl
  · intro x
    rw [gradient_add_real (hu.differentiable (by simp) x) (hv.differentiable (by simp) x)]
    exact (norm_add_le _ _).trans (add_le_add (huG x) (hvG x))

end KLS
end
