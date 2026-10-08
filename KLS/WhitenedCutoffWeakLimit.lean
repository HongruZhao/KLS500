import KLS.DampedWhiteningWeakLimit

/-! Actual compact isotropic cutoff laws converge on compact continuous tests. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix Metric
open scoped Topology ENNReal NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

theorem admissibleMeasure.tendsto_integral_whitenedBallCutoffMeasure_compact
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0)
    {f : Space n → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun k => ∫ x, f x ∂whitenedBallCutoffMeasure μ R k)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let ν := fun k => ballCutoffMeasure μ R k
  let A := fun k => inverseSqrtMatrix (covarianceMatrix (ν k))
  let b := fun k => -matrixAction (A k) (∫ x, x ∂ν k)
  have hmap (x : Space n) : Tendsto (fun k => affineMatrixMap (A k) (b k) x) atTop (𝓝 x) :=
    tendsto_affineMatrixMap_of_coefficients (hμ.tendsto_whitening_coefficient hR) x
  obtain ⟨B, hB⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  have hb (x : Space n) : ‖f x‖ ≤ B := hB (f x) (mem_range_self x)
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hb 0)
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Space n => B)
    (F := fun k => (closedBall (0 : Space n) (R + k)).indicator
      (fun x => f (affineMatrixMap (A k) (b k) x))) (f := f) (μ := μ)
    (fun _ => (by fun_prop : AEStronglyMeasurable
      (fun x => f (affineMatrixMap (A _) (b _) x)) μ).indicator measurableSet_closedBall)
    (integrable_const _)
    (fun k => Eventually.of_forall fun x => by
      by_cases hx : x ∈ closedBall (0 : Space n) (R + k)
      · rw [indicator_of_mem hx]
        exact hb _
      · rw [indicator_of_notMem hx, norm_zero]
        exact hB0)
    (Eventually.of_forall fun x => by
      obtain ⟨N, hN⟩ := mem_iUnion.mp (show x ∈ ⋃ k : ℕ, closedBall (0 : Space n) (R + k) by
        rw [iUnion_cutoffBalls]; exact mem_univ x)
      apply (hf.continuousAt.tendsto.comp (hmap x)).congr'
      filter_upwards [eventually_ge_atTop N] with k hk
      simp only [indicator_of_mem ((monotone_cutoffBalls R hk) hN), Function.comp_apply])
  have he (k : ℕ) : (∫ x, f x ∂whitenedBallCutoffMeasure μ R k) =
      (μ.real (closedBall (0 : Space n) (R + k)))⁻¹ *
        ∫ x, (closedBall (0 : Space n) (R + k)).indicator
          (fun x => f (affineMatrixMap (A k) (b k) x)) x ∂μ := by
    rw [whitenedBallCutoffMeasure, whitenedMeasure, affineMatrixMeasure,
      integral_map (by fun_prop) hf.aestronglyMeasurable,
      ballCutoffMeasure, ProbabilityTheory.cond, integral_smul_measure,
      ENNReal.toReal_inv, smul_eq_mul, ← integral_indicator measurableSet_closedBall]
    rfl
  simp_rw [he]
  simpa only [inv_one, one_mul, Pi.mul_apply] using
    ((tendsto_cutoffMass μ R).inv₀ one_ne_zero).mul ht

theorem admissibleMeasure.mem_poincareConstants_of_compact_laws
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {C : ℝ≥0} (hC : 0 < C)
    (hcompact : ∀ ν : Measure (Space n), admissibleMeasure ν → IsCompact ν.support →
      C ∈ poincareConstants ν) : C ∈ poincareConstants μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨R, _, hR, hevent⟩ := hμ.exists_whitened_compact_cutoffs
  let : ∀ k, IsProbabilityMeasure (ballCutoffMeasure μ R k) := fun k =>
    isProbabilityMeasure_ballCutoffMeasure hR k
  let : ∀ k, IsProbabilityMeasure (whitenedBallCutoffMeasure μ R k) := fun k =>
    inferInstanceAs (IsProbabilityMeasure (whitenedMeasure (ballCutoffMeasure μ R k)))
  apply mem_poincareConstants_of_weak_measure_limit hμ.absolutelyContinuousLebesgue hC
    (ν := fun k => whitenedBallCutoffMeasure μ R k)
  · filter_upwards [hevent] with k hk
    exact hcompact _ hk.1 hk.2
  · exact fun _ hf hc => hμ.tendsto_integral_whitenedBallCutoffMeasure_compact hR hf hc

end KLS
end
