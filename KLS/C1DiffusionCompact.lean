import KLS.WeightedWeakEquation
import KLS.WeightedDiffusionLiouville

/-!
# C¹ potential: C1DiffusionCompact

This extension uses the actual diffusion and weighted L² representatives.
Only first derivatives of the source potential are required.
-/

open MeasureTheory InnerProductSpace Set Filter ContinuousLinearMap
open scoped ContDiff ENNReal Convolution Topology

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual compact C³ diffusion is in L² for a finite C¹ source potential. -/
theorem memLp_weightedDiffusion_of_C1_hasCompactSupport {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    MemLp (weightedDiffusion φ g) 2 (potentialMeasure φ) := by
  apply memLp_of_continuous_hasCompactSupport hφ.continuous
  · have hcont : Continuous (fun x => ∑ i,
        (coordinateHessian g x i i - coordinateDerivative g i x * coordinateDerivative φ i x)) :=
      continuous_finsetSum _ (fun i _ =>
        (contDiff_coordinateHessian hg (m := 0) (by norm_num) i i).continuous.sub
          ((contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous.mul
            (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous))
    convert hcont using 1
    funext x
    exact weightedDiffusion_eq_sum φ g x
  · apply hc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_ (isClosed_tsupport g))
    intro x hx
    by_contra h
    exact hx (weightedDiffusion_eq_zero_of_notMem_tsupport h)

theorem mem_orthogonal_compactDiffusionRange_iff_C1 {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (u : Lp ℝ 2 (potentialMeasure φ)) :
    u ∈ (compactDiffusionRange φ)ᗮ ↔
      ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
        (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0 := by
  rw [(compactDiffusionRange φ).mem_orthogonal']
  constructor
  · intro hu g hg hc
    let hv2 := (memLp_weightedDiffusion_of_C1_hasCompactSupport hφ hg hc).neg
    let v : Lp ℝ 2 (potentialMeasure φ) := hv2.toLp (fun x => -weightedDiffusion φ g x)
    have hvae : (v : Space n → ℝ) =ᵐ[potentialMeasure φ] fun x => -weightedDiffusion φ g x :=
      hv2.coeFn_toLp
    have hv : v ∈ compactDiffusionRange φ := ⟨g, hg, hc, hvae⟩
    have he := hu v hv
    rw [inner_eq_neg_integral_diffusion_of_ae u v hvae] at he
    exact neg_eq_zero.mp he
  · intro hu v hv
    rcases hv with ⟨g, hg, hc, hv⟩
    rw [inner_eq_neg_integral_diffusion_of_ae u v hv, hu g hg hc, neg_zero]

theorem diffusionRangeDense_of_weakDiffusionLiouville_C1 {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hweak : WeakDiffusionLiouville φ) :
    DiffusionRangeDense φ := by
  intro u hu
  rw [← (compactDiffusionRange φ).orthogonal_orthogonal_eq_closure]
  rw [((compactDiffusionRange φ)ᗮ).mem_orthogonal]
  intro v hv
  obtain ⟨c, hc⟩ := hweak v ((mem_orthogonal_compactDiffusionRange_iff_C1 hφ v).mp hv)
  rw [L2.inner_def]
  calc
    (∫ x, inner ℝ (v x) (u x) ∂potentialMeasure φ) =
        ∫ x, c * u x ∂potentialMeasure φ := by
      apply integral_congr_ae
      filter_upwards [hc] with x hx
      simp [hx, RCLike.inner_apply, mul_comm]
    _ = 0 := by rw [integral_const_mul, hu, mul_zero]

end KLS
end
