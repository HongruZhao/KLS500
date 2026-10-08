import KLS.WeightedResolventSpectralPairing

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal NNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Poincare contraction and the actual dyadic displacement yield the
bounded smooth test variance bound in the literal L1 gradient. -/
theorem variance_le_gradient_L1_of_poincare_smooth_bounded
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ)) (hC0 : 0 < (C : ℝ))
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf2 : MemLp f 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfB : ∀ x, |f x| ≤ B) (hfM : ∀ x, ‖gradient f x‖ ≤ M) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      (16/3 : ℝ)*B*Real.sqrt C*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
  have hfaithful : LocallyLipschitzTests (potentialMeasure φ) f :=
    ⟨(hf.of_le (by simp) : ContDiff ℝ 1 f).locallyLipschitz,hf2⟩
  have he : energy (potentialMeasure φ) f < ⊤ := by
    apply energy_lt_top_of_memLp_coordinateDerivative
    intro i
    apply MemLp.of_bound (measurable_coordinateDerivative f i).aestronglyMeasurable M
    exact Eventually.of_forall fun x => (norm_coordinateDerivative_le f i x).trans (hfM x)
  have hu := weightedMassResolvent_square_dual_displacement_le hφ hconv hC0
    hf hf2 hB hM hfB hfM hfaithful he
  have hl := weightedMassResolvent_square_defect_pairing_ge hφ.continuous hC hC0 (hf2.toLp f)
  have hc : (C : ℝ)/((C : ℝ)+(C : ℝ))=1/2 := by field_simp;ring
  rw [hc,CenteredL2.norm_center_sq_eq_variance,ProbabilityTheory.variance_congr hf2.coeFn_toLp] at hl
  have hp := le_abs_self (inner ℝ
    (hf2.toLp f-weightedMassResolvent φ hC0 (weightedMassResolvent φ hC0 (hf2.toLp f))) (hf2.toLp f))
  nlinarith

/-- Compact support derives every bound needed for the variance-to-gradient estimate. -/
theorem variance_le_gradient_L1_of_poincare_smooth_compact
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ)) (hC0 : 0 < (C : ℝ))
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ B) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      (16/3 : ℝ)*B*Real.sqrt C*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
  have hf2 := memLp_of_continuous_hasCompactSupport hφ.continuous hf.continuous hfc
  obtain ⟨M,hM⟩ := (hasCompactSupport_gradient hfc).exists_bound_of_continuous
    (continuous_gradient_of_contDiff (hf.of_le (by simp) : ContDiff ℝ 1 f))
  exact variance_le_gradient_L1_of_poincare_smooth_bounded hφ hconv hC hC0 hf hf2 hB
    ((norm_nonneg (gradient f 0)).trans (hM 0)) hfB hM

end KLS
end
