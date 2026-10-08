import KLS.WeightedEnergyInverse

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual shifted weighted Dirichlet form on the complete gradient graph. -/
def weightedShiftedEnergyForm (φ : Space n → ℝ) (t : ℝ) :
    WeightedCenteredH1 φ →L[ℝ] WeightedCenteredH1 φ →L[ℝ] ℝ :=
  ((innerSL ℝ).bilinearComp (weightedH1Value φ) (weightedH1Value φ) :
    WeightedCenteredH1 φ →L[ℝ] WeightedCenteredH1 φ →L[ℝ] ℝ) +
    t • weightedEnergyForm φ

@[simp] theorem weightedShiftedEnergyForm_apply (φ : Space n → ℝ) (t : ℝ)
    (U V : WeightedCenteredH1 φ) :
    weightedShiftedEnergyForm φ t U V =
      inner ℝ (weightedH1Value φ U) (weightedH1Value φ V) + t * weightedEnergyForm φ U V := by
  simp [weightedShiftedEnergyForm]

theorem weightedShiftedEnergyForm_symm (φ : Space n → ℝ) (t : ℝ)
    (U V : WeightedCenteredH1 φ) :
    weightedShiftedEnergyForm φ t U V = weightedShiftedEnergyForm φ t V U := by
  simp only [weightedShiftedEnergyForm_apply, real_inner_comm, weightedEnergyForm_symm φ U V]

/-- The shift supplies coercivity for every positive time, without a Poincare
or curvature assumption. -/
theorem weightedShiftedEnergyForm_isCoercive (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t) :
    IsCoercive (weightedShiftedEnergyForm φ t) := by
  refine ⟨min 1 t, lt_min zero_lt_one ht, fun U => ?_⟩
  have hv := sq_nonneg ‖weightedH1Value φ U‖
  have he : 0 ≤ ∑ i : Fin n, ‖weightedH1Derivative φ i U‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [weightedShiftedEnergyForm_apply, real_inner_self_eq_norm_sq, weightedEnergyForm_self]
  have hn := weightedH1_norm_sq φ U
  have hvb := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) t) hv
  have heb := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) t) he
  calc
    min 1 t * ‖U‖ * ‖U‖ = min 1 t * ‖U‖ ^ 2 := by ring
    _ = min 1 t * ‖weightedH1Value φ U‖ ^ 2 +
        min 1 t * ∑ i : Fin n, ‖weightedH1Derivative φ i U‖ ^ 2 := by rw [hn, mul_add]
    _ ≤ _ := add_le_add (by simpa using hvb) heb

end KLS
end
