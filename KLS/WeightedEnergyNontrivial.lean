import KLS.WeightedEnergyGraphClosability
import KLS.SmoothCutoffSequence
import Mathlib.MeasureTheory.Measure.OpenPos

/-! A genuine compact smooth bump supplies a nonzero and then unit weighted value. -/
open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff RealInnerProductSpace
noncomputable section
namespace KLS
variable {n : ℕ}

/-- In positive dimension a genuine centered compact smooth function has nonzero weighted L² value. -/
theorem exists_weightedH1_value_ne_zero {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hn : 0 < n) (hφ : Continuous φ) :
    ∃ U : WeightedCenteredH1 φ, weightedH1Value φ U ≠ 0 := by
  obtain ⟨U, hv, _⟩ := exists_weightedH1_of_smoothCompact hφ
    ((unitCutoff n).contDiff : ContDiff ℝ 3 (unitCutoff n)) (unitCutoff n).hasCompactSupport
  refine ⟨U, ?_⟩
  intro hU
  have hz : (weightedH1Value φ U : Space n → ℝ) =ᵐ[potentialMeasure φ] fun _ => 0 := by
    rw [hU]
    exact Lp.coeFn_zero ℝ 2 (potentialMeasure φ)
  have he : (fun x => unitCutoff n x - ∫ y, unitCutoff n y ∂potentialMeasure φ) =
      (fun _ : Space n => (0 : ℝ)) :=
    MeasureTheory.Measure.eq_of_ae_eq
      ((volume_absolutelyContinuous_potentialMeasure hφ).ae_eq (hv.symm.trans hz))
      ((unitCutoff n).continuous.sub continuous_const) continuous_const
  have hzero : unitCutoff n (0 : Space n) = 1 :=
    (unitCutoff n).one_of_mem_closedBall (by simp [unitCutoff])
  let x : Space n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) 3
  have hfar : unitCutoff n x = 0 := by
    apply (unitCutoff n).zero_of_le_dist
    norm_num [unitCutoff, x, dist_zero_right]
  have h₀ := congrFun he 0
  have h₁ := congrFun he x
  rw [hzero] at h₀
  rw [hfar] at h₁
  linarith

/-- The value image meets the actual unit sphere; no eigenfunction or spectral witness is assumed. -/
theorem exists_weightedH1_value_norm_eq_one {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hn : 0 < n) (hφ : Continuous φ) :
    ∃ U : WeightedCenteredH1 φ, ‖weightedH1Value φ U‖ = 1 := by
  obtain ⟨U, hU⟩ := exists_weightedH1_value_ne_zero hn hφ
  refine ⟨‖weightedH1Value φ U‖⁻¹ • U, ?_⟩
  rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hU)]

end KLS
end
#print axioms KLS.exists_weightedH1_value_ne_zero
#print axioms KLS.exists_weightedH1_value_norm_eq_one
