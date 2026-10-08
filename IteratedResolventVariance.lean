import KLS.WeightedResolventTwoStepSmoothing
import KLS.WeightedResolventGradientContraction

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- A mixed value/gradient bound propagates through two consecutive actual
resolvents, adding exactly twice the time to its gradient coefficient. -/
theorem weightedMassResolvent_mixed_variance_step
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {f g : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hf2 : MemLp f 2 (potentialMeasure φ))
    {A B M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hfM : ∀ x, ‖gradient f x‖ ≤ M)
    (heq : ∀ x, f x - t * weightedDiffusion φ f x = g x)
    (hbound : ∀ x, g x ^ 2 + A * ‖gradient f x‖ ^ 2 ≤ B ^ 2) :
    ∃ z : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) z ∧ MemLp z 2 (potentialMeasure φ) ∧
      (∀ i : Fin n, MemLp (coordinateDerivative z i) 2 (potentialMeasure φ)) ∧
      z =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht (hf2.toLp f) : Space n → ℝ) ∧
      (∀ x, z x - t * weightedDiffusion φ z x = f x) ∧
      (∀ x, ‖gradient z x‖ ≤ M) ∧
      ∀ x, f x ^ 2 + (A+2*t) * ‖gradient z x‖ ^ 2 ≤ B ^ 2 := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x => ‖gradient f x‖ ^ 2) :=
    contDiff_gradient_norm_sq hf (by simp)
  have hF2 : MemLp (fun x => ‖gradient f x‖ ^ 2) 2 (potentialMeasure φ) := by
    apply MemLp.of_bound hF.continuous.aestronglyMeasurable (M^2)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) hM).2 (hfM x)
  have hgSq (x : Space n) : g x ^ 2 ≤ B ^ 2 := by
    have hp := mul_nonneg hA (sq_nonneg ‖gradient f x‖)
    linarith [hbound x]
  have hG2 : MemLp (fun x => g x ^ 2) 2 (potentialMeasure φ) := by
    apply MemLp.of_bound (hg.pow 2).continuous.aestronglyMeasurable (B^2)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hgSq x
  obtain ⟨v,w,hv,hw,hv2,hw2,hvμ,hwμ,hev,_hew,hvar⟩ :=
    weightedMassResolvent_exists_variance_pair hφ ht hf hg hf2 hF2 hG2 heq
  let H : Space n → ℝ := fun x => g x ^ 2 + A * ‖gradient f x‖ ^ 2
  have hH2 : MemLp H 2 (potentialMeasure φ) := hG2.add (hF2.const_mul A)
  have hHlp : hH2.toLp H = hG2.toLp (fun x => g x ^ 2) +
      A • hF2.toLp (fun x => ‖gradient f x‖ ^ 2) := by
    apply Lp.ext
    filter_upwards [hH2.coeFn_toLp, hG2.coeFn_toLp, hF2.coeFn_toLp,
      Lp.coeFn_add (hG2.toLp (fun x => g x ^ 2))
        (A • hF2.toLp (fun x => ‖gradient f x‖ ^ 2)),
      Lp.coeFn_smul A (hF2.toLp (fun x => ‖gradient f x‖ ^ 2))] with x hh hgx hfx hadd hsmul
    simp only [hh, hadd, Pi.add_apply, hsmul, hgx, hfx, H, Pi.smul_apply, smul_eq_mul]
  have hcombo : (fun x => w x + A*v x) =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (hH2.toLp H) : Space n → ℝ) := by
    rw [hHlp, map_add, map_smul]
    filter_upwards [hwμ, hvμ,
      Lp.coeFn_add (weightedMassResolvent φ ht (hG2.toLp (fun x => g x ^ 2)))
        (A • weightedMassResolvent φ ht (hF2.toLp (fun x => ‖gradient f x‖ ^ 2))),
      Lp.coeFn_smul A (weightedMassResolvent φ ht (hF2.toLp (fun x => ‖gradient f x‖ ^ 2)))]
      with x hwx hvx hadd hsmul
    simp only [hadd, Pi.add_apply, hsmul, hwx, hvx, Pi.smul_apply, smul_eq_mul]
  have hupper : ∀ x, w x + A*v x ≤ B^2 := by
    apply weightedMassResolvent_upper_bound_of_representative hφ1 ht (hH2.toLp H)
      ((hw.add ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Space n => A)).mul hv)).of_le (by simp)) hcombo
    filter_upwards [hH2.coeFn_toLp] with x hx
    rw [hx]
    exact hbound x
  obtain ⟨z,hz,hz2,hdz,hzμ,_hm,hez,hzM⟩ :=
    weightedMassResolvent_exists_gradient_bounded_representative hφ hconv ht hf hf2 hM hfM
  have hdv (i : Fin n) : MemLp (coordinateDerivative v i) 2 (potentialMeasure φ) :=
    (memLp_congr_ae (weightedMassResolvent_coordinateDerivative_of_representative hφ1 ht
      (hF2.toLp (fun x => ‖gradient f x‖ ^ 2)) (hv.of_le (by simp)) hvμ i)).mpr (Lp.memLp _)
  have hgv := (memLp_gradient_of_coordinateDerivative (hv.of_le (by simp)) hdv).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hLval (x : Space n) : weightedDiffusion φ z x = t⁻¹*(z x-f x) := by
    rw [inv_mul_eq_div]
    apply (eq_div_iff ht.ne').2
    linarith [hez x]
  have hL : MemLp (weightedDiffusion φ z) 2 (potentialMeasure φ) := by
    rw [show weightedDiffusion φ z = fun x => t⁻¹*(z x-f x) from funext hLval]
    exact (hz2.sub hf2).const_mul _
  have hcmp := gradient_norm_sq_le_of_resolvent_equations hφ2 hz (hf.of_le (by simp))
    (hv.of_le (by simp)) ht hez hev (hessianGradientForm_nonneg_of_convex hφ2 hconv z)
    hL hdz (hv2.integrable (by norm_num)) hgv
  refine ⟨z,hz,hz2,hdz,hzμ,hez,hzM,?_⟩
  intro x
  have hp := mul_le_mul_of_nonneg_left (hcmp x) (by positivity : 0 ≤ A+2*t)
  nlinarith [hvar x,hupper x]

end KLS.ConstantReduction
end
