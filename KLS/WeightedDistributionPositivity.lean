import KLS.ScalarMollification

open MeasureTheory InnerProductSpace Set Filter ContinuousLinearMap
open scoped Topology ContDiff ENNReal Convolution

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual positive mollifiers detect distributional nonnegativity. -/
theorem ae_nonneg_of_integral_smooth_nonneg {f : Space n → ℝ}
    (hf : LocallyIntegrable f volume)
    (h : ∀ ψ : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ x, f x * ψ x) :
    ∀ᵐ x ∂volume, 0 ≤ f x := by
  have hm (k : ℕ) (x : Space n) : 0 ≤ mollify k f x := by
    have hp := h (fun y => mollifierKernel n k (x-y))
      ((mollifierKernel_contDiff k).comp (contDiff_const.sub contDiff_id))
      ((mollifierKernel_hasCompactSupport k).comp_homeomorph (Homeomorph.subLeft x))
      (fun y => (mollifierBump n k).nonneg_normed (x-y))
    simpa only [mollify, scalarConvolution, convolution_def, lsmul_apply, smul_eq_mul] using hp
  filter_upwards [mollify_tendsto_ae hf] with x hx
  exact ge_of_tendsto hx (Eventually.of_forall fun k => hm k x)

/-- Weighted smooth nonnegative tests detect the sign of every weighted-L2
function, using the actual positive density and actual Lebesgue mollifiers. -/
theorem ae_nonneg_of_weighted_integral_smooth_nonneg {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hf : MemLp f 2 (potentialMeasure φ))
    (h : ∀ ψ : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ x, f x * ψ x ∂potentialMeasure φ) :
    ∀ᵐ x ∂potentialMeasure φ, 0 ≤ f x := by
  have hv : ∀ᵐ x ∂volume, 0 ≤ f x := by
    apply ae_nonneg_of_integral_smooth_nonneg
      (KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure hf hφ.continuous)
    intro ψ hψ hc hψ0
    have ht := h (fun x => ψ x * Real.exp (φ x)) (hψ.mul hφ.exp) hc.mul_right
      (fun x => mul_nonneg (hψ0 x) (Real.exp_pos _).le)
    have heq : (∫ x, f x * (ψ x * Real.exp (φ x)) ∂potentialMeasure φ) =
        ∫ x, f x * ψ x := by
      rw [integral_potentialMeasure hφ.continuous.measurable]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        have hcancel : Real.exp (φ x) * Real.exp (-φ x) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        calc
          _ = (f x * ψ x) * (Real.exp (φ x) * Real.exp (-φ x)) := by ring
          _ = _ := by rw [hcancel, mul_one]
    rwa [heq] at ht
  exact (withDensity_absolutelyContinuous _ _).ae_le hv

end KLS
end
