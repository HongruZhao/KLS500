import KLS.ResolventDyadicNumerics

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The genuine two-step resolvent has the dimension-free dual displacement
bound. Its dyadic differences and zero-time strong limit are derived for the
actual operator; the test is any faithful finite-energy function. -/
theorem weightedMassResolvent_square_dual_displacement_le
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) :
    |inner ℝ (hg2.toLp g-weightedMassResolvent φ ht (weightedMassResolvent φ ht (hg2.toLp g)))
      (hψ.2.toLp ψ)| ≤ 4*B*Real.sqrt t*(∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ) := by
  let d : ℕ → ℝ := fun k => t/2^k
  have hd (k : ℕ) : 0 < d k := div_pos ht (by positivity)
  have hds (k : ℕ) : d (k+1)=d k/2 := by
    dsimp only [d]
    rw [pow_succ,div_mul_eq_div_div]
  have hd0 : Tendsto d atTop (𝓝 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)).const_mul t
    simpa only [d,div_eq_mul_inv,one_mul,inv_pow,mul_zero] using hp
  let F : ℕ → ℝ := fun k => inner ℝ
    (weightedMassResolvent φ (hd k) (weightedMassResolvent φ (hd k) (hg2.toLp g))) (hψ.2.toLp ψ)
  have hlim : Tendsto F atTop (𝓝 (inner ℝ (hg2.toLp g) (hψ.2.toLp ψ))) :=
    (weightedMassResolvent_square_tendsto_zero hφ.continuous hd hd0 (hg2.toLp g)).inner tendsto_const_nhds
  let I : ℝ := ∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ
  have hI : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  let C : ℝ := B*Real.sqrt t*I
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hB (Real.sqrt_nonneg _)) hI
  have hstep (k : ℕ) : |F (k+1)-F k| ≤ C*(3/4 : ℝ)^k := by
    have hst : d (k+1) ≤ d k := by rw [hds];linarith [hd k]
    have hp := weightedMassResolvent_square_sub_inner_abs_le hφ hconv (hd (k+1)) (hd k) hst
      hg hg2 hB hM hgB hgM hψ heψ
    have hc : (d k-d (k+1))*(B/Real.sqrt (2*d k)+B/Real.sqrt (2*d (k+1))) ≤
        B*Real.sqrt (d k) := by
      rw [hds]
      exact resolvent_half_step_coefficient_le (hd k) hB
    have hgrowth := sqrt_dyadic_time_le ht.le k
    calc
      _ = |inner ℝ (weightedMassResolvent φ (hd k) (weightedMassResolvent φ (hd k) (hg2.toLp g))-
          weightedMassResolvent φ (hd (k+1)) (weightedMassResolvent φ (hd (k+1)) (hg2.toLp g)))
          (hψ.2.toLp ψ)| := by rw [inner_sub_left];exact abs_sub_comm _ _
      _ ≤ _ := hp
      _ ≤ (B*Real.sqrt (d k))*I := mul_le_mul_of_nonneg_right hc hI
      _ ≤ (B*(Real.sqrt t*(3/4 : ℝ)^k))*I :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrowth hB) hI
      _ = C*(3/4 : ℝ)^k := by dsimp only [C];ring
  have hb := abs_limit_sub_zero_le_of_three_quarters_steps hC hlim hstep
  simpa only [F,d,pow_zero,div_one,← inner_sub_left,C,mul_assoc] using hb

end KLS
end
