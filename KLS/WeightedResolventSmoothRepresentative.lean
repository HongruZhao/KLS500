import KLS.WeightedResolventLocalEquation

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Regularity
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Smooth forcing and potential give an actual globally smooth representative
of the constructed resolvent. Its value, gradient, mean, and classical equation
are all concluded from the genuine graph construction. -/
theorem weightedResolvent_exists_smooth_representative
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    {g : Space n → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 (potentialMeasure φ)) :
    ∃ f : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ MemLp f 2 (potentialMeasure φ) ∧
      (∫ x, f x ∂potentialMeasure φ) = 0 ∧
      (∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ)) ∧
      f =ᵐ[volume] (weightedH1Value φ
        (weightedResolventH1 φ ht (hg2.toLp g)) : Space n → ℝ) ∧
      f =ᵐ[potentialMeasure φ] (weightedResolvent φ ht (hg2.toLp g) : Space n → ℝ) ∧
      ∀ x, f x - t * weightedDiffusion φ f x = g x - ∫ y, g y ∂potentialMeasure φ := by
  let U := weightedResolventH1 φ ht (hg2.toLp g)
  have hsol : LocalWeakSol univ (weightedEigenSmoothOp hφ (-t⁻¹)).a
      (weightedEigenSmoothOp hφ (-t⁻¹)).b (weightedEigenSmoothOp hφ (-t⁻¹)).c
      (fun x => t⁻¹ * (g x - ∫ y, g y ∂potentialMeasure φ))
      (weightedH1Value φ U) (fun i => weightedH1Derivative φ i U) := by
    simpa only [weightedEigenSmoothOp, neg_neg] using
      weightedResolvent_localWeakSol (hφ.of_le (by simp)) ht hg2
  obtain ⟨f, hs, hae⟩ := exists_contDiffOn_of_localWeakSol isOpen_univ
    (weightedEigenSmoothOp hφ (-t⁻¹)) (contDiff_const.mul (hg.sub contDiff_const)).contDiffOn
    (fun K hK _ => weightedH1Value_memLp_restrict hφ.continuous U hK)
    (fun i K hK _ => weightedH1Derivative_memLp_restrict hφ.continuous U i hK)
    (weightedH1_hasWeakGradOn_univ (hφ.of_le (by simp)) U) hsol
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiffOn_univ.mp hs
  have hv : f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ) := by
    simpa only [Measure.restrict_univ] using hae
  have hvμ : f =ᵐ[potentialMeasure φ] (weightedH1Value φ U : Space n → ℝ) :=
    (withDensity_absolutelyContinuous _ _).ae_eq hv
  have hf2 : MemLp f 2 (potentialMeasure φ) := (memLp_congr_ae hvμ).mpr (Lp.memLp _)
  have hm : (∫ x, f x ∂potentialMeasure φ) = 0 := by
    rw [integral_congr_ae hvμ, weightedH1_integral_eq_zero hφ.continuous U]
  have hd (i : Fin n) : coordinateDerivative f i =ᵐ[potentialMeasure φ]
      (weightedH1Derivative φ i U : Space n → ℝ) :=
    (withDensity_absolutelyContinuous _ _).ae_eq
      (weightedH1_coordinateDerivative_of_representative (hφ.of_le (by simp)) U
        (hf.of_le (by simp)) hv i)
  have hw (ψ : Space n → ℝ) (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
      (∑ i : Fin n, ∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x
        ∂potentialMeasure φ) =
      ∫ x, (t⁻¹ * (g x - (∫ y, g y ∂potentialMeasure φ) - f x)) * ψ x
        ∂potentialMeasure φ := by
    rw [weightedResolvent_poisson_test_toLp hφ.continuous ht hg2 hψ hc]
    apply integral_congr_ae
    filter_upwards [hvμ] with x hx
    rw [hx]
  have heq := weighted_poisson_pointwise_of_representative (hφ.of_le (by simp))
    (continuous_const.mul ((hg.continuous.sub continuous_const).sub hf.continuous)) hw
    (hf.of_le (by simp)) hv
  refine ⟨f, hf, hf2, hm, fun i => (memLp_congr_ae (hd i)).mpr (Lp.memLp _), hv, hvμ, ?_⟩
  intro x
  rw [heq x]
  simp only [Pi.mul_apply, Pi.sub_apply]
  field_simp [ht.ne']
  ring

end KLS
end
