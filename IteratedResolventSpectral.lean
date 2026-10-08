import KLS.WeightedResolventSpectralPairing

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace NNReal
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

theorem weightedMassResolvent_iterate_integral (hφ : Continuous φ)
    {t : ℝ} (ht : 0 < t) (k : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)) :
    (∫ x, ((weightedMassResolvent φ ht)^[k] f) x ∂potentialMeasure φ) =
      ∫ x, f x ∂potentialMeasure φ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', weightedMassResolvent_integral hφ ht, ih]

theorem weightedMassResolvent_iterate_defect_pairing_ge
    (hφ : Continuous φ) {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ))
    {t : ℝ} (ht : 0 < t) (k : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)) :
    (1-((C : ℝ)/((C : ℝ)+t))^k)*‖CenteredL2.center (potentialMeasure φ) f‖^2 ≤
      inner ℝ (f-(weightedMassResolvent φ ht)^[k] f) f := by
  let c := CenteredL2.center (potentialMeasure φ) f
  let d := CenteredL2.center (potentialMeasure φ) ((weightedMassResolvent φ ht)^[k] f)
  have hsub : f-(weightedMassResolvent φ ht)^[k] f = c-d := by
    dsimp only [c,d,CenteredL2.center]
    rw [weightedMassResolvent_iterate_integral hφ ht]
    abel
  have hdecomp : c + (∫ x, f x ∂potentialMeasure φ) • CenteredL2.oneLp (potentialMeasure φ) = f := by
    dsimp only [c,CenteredL2.center]
    abel
  have horth (u : Lp ℝ 2 (potentialMeasure φ)) :
      inner ℝ (CenteredL2.center (potentialMeasure φ) u) (CenteredL2.oneLp (potentialMeasure φ)) = 0 := by
    rw [real_inner_comm, CenteredL2.inner_oneLp, CenteredL2.integral_center]
  have heq : inner ℝ (f-(weightedMassResolvent φ ht)^[k] f) f = ‖c‖^2-inner ℝ d c := by
    rw [hsub]
    calc
      _ = inner ℝ (c-d) (c+(∫ x, f x ∂potentialMeasure φ) • CenteredL2.oneLp (potentialMeasure φ)) :=
        congrArg (fun u => inner ℝ (c-d) u) hdecomp.symm
      _ = _ := by
        rw [inner_add_right, inner_sub_left, real_inner_self_eq_norm_sq,
          inner_smul_right, inner_sub_left, horth f, horth ((weightedMassResolvent φ ht)^[k] f)]
        ring
  have hn := weightedMassResolvent_iterate_center_norm_le hφ hC ht k f
  have hp := (le_abs_self (inner ℝ d c)).trans (abs_real_inner_le_norm d c)
  have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg c)
  change ‖d‖*‖c‖ ≤ ((C:ℝ)/((C:ℝ)+t))^k*‖c‖*‖c‖ at hm
  rw [heq]
  change (1-((C:ℝ)/((C:ℝ)+t))^k)*‖c‖^2 ≤ ‖c‖^2-inner ℝ d c
  nlinarith

end KLS.ConstantReduction
end
