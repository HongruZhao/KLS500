import KLS.WeightedResolventGradientSubcommutation

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The genuine two-step resolvent has gradient bounded by B/sqrt(2t).
The bound depends only on the forcing supremum B and t. Smoothness and a
finite forcing-gradient bound remain explicit hypotheses of this construction. -/
theorem weightedMassResolvent_exists_two_step_gradient_bound
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M) :
    ∃ z : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) z ∧ MemLp z 2 (potentialMeasure φ) ∧
      z =ᵐ[potentialMeasure φ]
        (weightedMassResolvent φ ht (weightedMassResolvent φ ht (hg2.toLp g)) : Space n → ℝ) ∧
      (∀ x, 2*t*‖gradient z x‖ ^ 2 ≤ B ^ 2) ∧
      ∀ x, ‖gradient z x‖ ≤ B/Real.sqrt (2*t) := by
  obtain ⟨f,hF2,v,hf,hv,hf2,hv2,hfμ,hvμ,_,hev,hvar⟩ :=
    weightedMassResolvent_exists_bounded_variance_pair hφ hconv ht hg hg2 hB hM hgB hgM
  obtain ⟨z,hz,hz2,hdz,_,hzμ,_,hez⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht hf hf2
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hdv (i : Fin n) : MemLp (coordinateDerivative v i) 2 (potentialMeasure φ) :=
    (memLp_congr_ae (weightedMassResolvent_coordinateDerivative_of_representative hφ1 ht
      (hF2.toLp (fun x => ‖gradient f x‖ ^ 2)) (hv.of_le (by simp)) hvμ i)).mpr (Lp.memLp _)
  have hgv := (memLp_gradient_of_coordinateDerivative (hv.of_le (by simp)) hdv).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hLval (x : Space n) : weightedDiffusion φ z x=t⁻¹*(z x-f x) := by
    rw [inv_mul_eq_div]
    apply (eq_div_iff ht.ne').2
    linarith [hez x]
  have hL : MemLp (weightedDiffusion φ z) 2 (potentialMeasure φ) := by
    rw [show weightedDiffusion φ z = fun x => t⁻¹*(z x-f x) from funext hLval]
    exact (hz2.sub hf2).const_mul _
  have hcmp := gradient_norm_sq_le_of_resolvent_equations hφ2 hz (hf.of_le (by simp))
    (hv.of_le (by simp)) ht hez hev (hessianGradientForm_nonneg_of_convex hφ2 hconv z)
    hL hdz (hv2.integrable (by norm_num)) hgv
  have hsq (x : Space n) : 2*t*‖gradient z x‖ ^ 2 ≤ B ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left (hcmp x) (by positivity : 0 ≤ 2*t)
    nlinarith [hvar x,sq_nonneg (f x)]
  have hfLp : hf2.toLp f=weightedMassResolvent φ ht (hg2.toLp g) := by
    apply Lp.ext
    exact hf2.coeFn_toLp.trans hfμ
  rw [hfLp] at hzμ
  refine ⟨z,hz,hz2,hzμ,hsq,?_⟩
  intro x
  have htp : 0 < 2*t := by positivity
  have hsp : 0 < Real.sqrt (2*t) := Real.sqrt_pos.2 htp
  apply (le_div_iff₀ hsp).2
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hB).1
  rw [mul_pow,Real.sq_sqrt htp.le]
  nlinarith [hsq x]

end KLS
end
