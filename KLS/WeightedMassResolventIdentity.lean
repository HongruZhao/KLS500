import KLS.WeightedResolventIdentity

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Restoring the mean identifies the composition of the actual mass resolvents. -/
theorem weightedMassResolvent_comp_apply (hφ : Continuous φ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ)) :
    weightedMassResolvent φ ht (weightedMassResolvent φ hs g) =
      weightedMassProjection φ g+weightedResolvent φ ht (weightedResolvent φ hs g) := by
  rw [weightedMassResolvent_apply,weightedMassProjection_apply,
    weightedMassResolvent_integral hφ hs,weightedMassResolvent_apply,map_add,
    weightedMassProjection_apply,map_smul,weightedResolvent_one_eq_zero hφ ht,
    smul_zero,zero_add]

/-- Mass-preserving resolvents at different positive times commute. -/
theorem weightedMassResolvent_commute (hφ : Continuous φ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ)) :
    weightedMassResolvent φ ht (weightedMassResolvent φ hs g) =
      weightedMassResolvent φ hs (weightedMassResolvent φ ht g) := by
  rw [weightedMassResolvent_comp_apply hφ hs ht,weightedMassResolvent_comp_apply hφ ht hs,
    weightedResolvent_commute φ hs ht]

/-- The genuine mass-preserving resolvent satisfies the parameter identity. -/
theorem weightedMassResolvent_resolvent_identity (hφ : Continuous φ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ)) :
    t • weightedMassResolvent φ ht g-s • weightedMassResolvent φ hs g =
      (t-s) • weightedMassResolvent φ ht (weightedMassResolvent φ hs g) := by
  rw [weightedMassResolvent_comp_apply hφ hs ht]
  simp only [weightedMassResolvent_apply,smul_add,sub_smul]
  have h := weightedResolvent_resolvent_identity φ hs ht g
  rw [sub_smul] at h
  linear_combination (norm := module) h

/-- A difference form suitable for applying actual diffusion equations. -/
theorem weightedMassResolvent_sub_identity (hφ : Continuous φ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ)) :
    s • (weightedMassResolvent φ ht g-weightedMassResolvent φ hs g) =
      (t-s) • (weightedMassResolvent φ ht (weightedMassResolvent φ hs g)-
        weightedMassResolvent φ ht g) := by
  have h := weightedMassResolvent_resolvent_identity hφ hs ht g
  simp only [smul_sub,sub_smul] at h ⊢
  linear_combination (norm := module) h

/-- The true two-step difference factors through both resolvents and their sum. -/
theorem weightedMassResolvent_square_sub_identity (hφ : Continuous φ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ)) :
    s • (weightedMassResolvent φ ht (weightedMassResolvent φ ht g)-
        weightedMassResolvent φ hs (weightedMassResolvent φ hs g)) =
      (t-s) • (weightedMassResolvent φ ht (weightedMassResolvent φ hs
          (weightedMassResolvent φ ht g+weightedMassResolvent φ hs g))-
        weightedMassResolvent φ ht (weightedMassResolvent φ ht g+weightedMassResolvent φ hs g)) := by
  have h := weightedMassResolvent_sub_identity hφ hs ht
    (weightedMassResolvent φ ht g+weightedMassResolvent φ hs g)
  have he : weightedMassResolvent φ ht (weightedMassResolvent φ ht g+weightedMassResolvent φ hs g)-
      weightedMassResolvent φ hs (weightedMassResolvent φ ht g+weightedMassResolvent φ hs g) =
      weightedMassResolvent φ ht (weightedMassResolvent φ ht g)-
        weightedMassResolvent φ hs (weightedMassResolvent φ hs g) := by
    simp only [map_add]
    rw [weightedMassResolvent_commute hφ hs ht]
    abel
  rwa [he] at h

end KLS
end
