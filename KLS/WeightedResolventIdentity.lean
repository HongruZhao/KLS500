import KLS.WeightedMassResolvent

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The concrete variational equations imply the resolvent identity on the
actual completed gradient graph, without a spectral theorem assumption. -/
theorem weightedResolventH1_resolvent_identity (φ : Space n → ℝ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ)) :
    t • weightedResolventH1 φ ht g-s • weightedResolventH1 φ hs g =
      (t-s) • weightedResolventH1 φ ht (weightedResolvent φ hs g) := by
  rw [← map_smul (weightedResolventH1 φ ht) (t-s) (weightedResolvent φ hs g)]
  apply weightedResolvent_unique
  intro V
  have hT := weightedResolvent_variational φ ht g V
  have hS := weightedResolvent_variational φ hs g V
  simp only [map_sub,map_smul,inner_sub_left,inner_smul_left,conj_trivial,
    sub_apply,smul_apply,smul_eq_mul]
  change t*inner ℝ (weightedResolvent φ ht g) (weightedH1Value φ V)-
      s*inner ℝ (weightedResolvent φ hs g) (weightedH1Value φ V)+
      t*(t*weightedEnergyForm φ (weightedResolventH1 φ ht g) V-
        s*weightedEnergyForm φ (weightedResolventH1 φ hs g) V) =
      (t-s)*inner ℝ (weightedResolvent φ hs g) (weightedH1Value φ V)
  nlinarith

/-- The same resolvent identity holds for its actual L2 value. -/
theorem weightedResolvent_resolvent_identity (φ : Space n → ℝ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ)) :
    t • weightedResolvent φ ht g-s • weightedResolvent φ hs g =
      (t-s) • weightedResolvent φ ht (weightedResolvent φ hs g) := by
  simpa only [map_sub,map_smul,weightedResolvent,ContinuousLinearMap.comp_apply] using
    congrArg (weightedH1Value φ) (weightedResolventH1_resolvent_identity φ hs ht g)

/-- Actual resolvents at two positive parameters commute. -/
theorem weightedResolvent_commute (φ : Space n → ℝ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ)) :
    weightedResolvent φ ht (weightedResolvent φ hs g) =
      weightedResolvent φ hs (weightedResolvent φ ht g) := by
  by_cases he : t=s
  · subst t
    rfl
  have hT := weightedResolvent_resolvent_identity φ hs ht g
  have hS := weightedResolvent_resolvent_identity φ ht hs g
  have heq : (t-s) • weightedResolvent φ ht (weightedResolvent φ hs g) =
      (t-s) • weightedResolvent φ hs (weightedResolvent φ ht g) := by
    rw [← hT,show t-s=-(s-t) by ring,neg_smul,← hS]
    abel
  exact (smul_right_injective _ (sub_ne_zero.mpr he)) heq

end KLS
end
