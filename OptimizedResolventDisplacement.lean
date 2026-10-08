import ResolventPartitionNumerics
import KLS.WeightedResolventSpectralPairing

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Every geometric time partition gives its exact dual displacement bound. -/
theorem weightedMassResolvent_square_dual_displacement_le_geometric
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t q : ℝ} (ht : 0 < t) (hq : 0 < q) (hq1 : q < 1) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) :
    |inner ℝ (hg2.toLp g-weightedMassResolvent φ ht (weightedMassResolvent φ ht (hg2.toLp g)))
      (hψ.2.toLp ψ)| ≤ ((q+2+q⁻¹)/Real.sqrt 2)*B*Real.sqrt t*
        (∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ) := by
  let d : ℕ → ℝ := fun k => t*(q^2)^k
  have hd (k : ℕ) : 0 < d k := mul_pos ht (pow_pos (sq_pos_of_pos hq) k)
  have hds (k : ℕ) : d (k+1)=q^2*d k := by dsimp only [d]; rw [pow_succ]; ring
  have hd0 : Tendsto d atTop (𝓝 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg q)
      (by nlinarith : q^2 < 1)).const_mul t
    simpa only [d,mul_zero] using hp
  let F : ℕ → ℝ := fun k => inner ℝ
    (weightedMassResolvent φ (hd k) (weightedMassResolvent φ (hd k) (hg2.toLp g))) (hψ.2.toLp ψ)
  have hlim : Tendsto F atTop (𝓝 (inner ℝ (hg2.toLp g) (hψ.2.toLp ψ))) :=
    (weightedMassResolvent_square_tendsto_zero hφ.continuous hd hd0 (hg2.toLp g)).inner tendsto_const_nhds
  let I : ℝ := ∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ
  have hI : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  let C : ℝ := ((q+2+q⁻¹)/Real.sqrt 2)*B*Real.sqrt t*I
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hstep (k : ℕ) : |F (k+1)-F k| ≤ C*(1-q)*q^k := by
    have hst : d (k+1) ≤ d k := by
      rw [hds]
      calc
        q^2*d k ≤ 1*d k := mul_le_mul_of_nonneg_right (by nlinarith : q^2 ≤ 1) (hd k).le
        _ = d k := one_mul _
    have hp := weightedMassResolvent_square_sub_inner_abs_le hφ hconv (hd (k+1)) (hd k) hst
      hg hg2 hB hM hgB hgM hψ heψ
    have hc : (d k-d (k+1))*(B/Real.sqrt (2*d k)+B/Real.sqrt (2*d (k+1))) =
        (1-q)*((q+2+q⁻¹)/Real.sqrt 2)*B*Real.sqrt (d k) := by
      rw [hds]
      exact resolvent_ratio_step_coefficient (hd k) hq
    calc
      _ = |inner ℝ (weightedMassResolvent φ (hd k) (weightedMassResolvent φ (hd k) (hg2.toLp g))-
          weightedMassResolvent φ (hd (k+1)) (weightedMassResolvent φ (hd (k+1)) (hg2.toLp g)))
          (hψ.2.toLp ψ)| := by rw [inner_sub_left]; exact abs_sub_comm _ _
      _ ≤ _ := hp
      _ = ((1-q)*((q+2+q⁻¹)/Real.sqrt 2)*B*Real.sqrt (d k))*I := by rw [hc]
      _ = C*(1-q)*q^k := by dsimp only [C,d]; rw [sqrt_geometric_time ht.le hq.le]; ring
  have hb := abs_limit_sub_zero_le_of_geometric_steps hC hq.le hlim hstep
  simpa only [F,d,pow_zero,mul_one,← inner_sub_left,C,mul_assoc] using hb

/-- Letting the partition ratio tend to one gives the sharper coefficient
2 sqrt(2), for the same actual resolvent and full finite-energy test class. -/
theorem weightedMassResolvent_square_dual_displacement_le_optimized
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) :
    |inner ℝ (hg2.toLp g-weightedMassResolvent φ ht (weightedMassResolvent φ ht (hg2.toLp g)))
      (hψ.2.toLp ψ)| ≤ 2*Real.sqrt 2*B*Real.sqrt t*
        (∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ) := by
  have hid : Tendsto (fun q : ℝ => q) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnum : Tendsto (fun q : ℝ => q+2+q⁻¹) (𝓝[<] (1 : ℝ)) (𝓝 (4 : ℝ)) := by
    convert (hid.add_const 2).add (hid.inv₀ (by norm_num : (1 : ℝ) ≠ 0)) using 1
    norm_num
  have heq : (4 : ℝ)/Real.sqrt 2 = 2*Real.sqrt 2 := by
    apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))).2
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hlim := (((hnum.div_const (Real.sqrt 2)).mul_const B).mul_const (Real.sqrt t)).mul_const
    (∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ)
  rw [heq] at hlim
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  have hpos : ∀ᶠ q : ℝ in 𝓝[<] (1 : ℝ), 0 < q :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hpos,self_mem_nhdsWithin] with q hq hq1
  exact weightedMassResolvent_square_dual_displacement_le_geometric
    hφ hconv ht hq hq1 hg hg2 hB hM hgB hgM hψ heψ

end KLS
end
