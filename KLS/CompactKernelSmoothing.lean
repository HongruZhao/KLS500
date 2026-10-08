import KLS.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Smooth integration against a compactly supported finite measure

A smooth kernel need not itself have compact support. Around each evaluation
point, a concrete smooth bump leaves the kernel unchanged on every translate
of the source support. Mathlib's compact-kernel convolution theorem then
supplies the actual smoothness of the integral.
-/

open MeasureTheory Set Filter Metric ContinuousLinearMap
open scoped ContDiff Convolution Topology

noncomputable section
namespace KLS

theorem integrable_of_continuous_compact_support_measure {n : ℕ}
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    {g : Space n → ℝ} (hg : Continuous g) : Integrable g μ := by
  have hh : IntegrableOn g μ.support μ :=
    ContinuousOn.integrableOn_compact hμ hg.continuousOn
  unfold IntegrableOn at hh
  have hs : μ.restrict μ.support = μ :=
    Measure.restrict_eq_self_of_ae_mem (s := μ.support) μ.support_mem_ae
  rwa [hs] at hh

theorem contDiff_integral_translate_of_compact_support {n : ℕ}
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    {g : Space n → ℝ} {m : ℕ∞} (hg : ContDiff ℝ m g) :
    ContDiff ℝ m (fun x => ∫ y, g (x - y) ∂μ) := by
  obtain ⟨R, hR, hsub⟩ := hμ.isBounded.subset_closedBall_lt 0 (0 : Space n)
  rw [contDiff_iff_contDiffAt]
  intro x
  let b : ContDiffBump (0 : Space n) :=
    ⟨‖x‖ + R + 1, ‖x‖ + R + 2, by positivity, by linarith⟩
  let k : Space n → ℝ := fun z => b z * g z
  have hk : ContDiff ℝ m k := b.contDiff.mul hg
  have hkc : HasCompactSupport k := b.hasCompactSupport.mul_right
  have hs : ContDiff ℝ m ((fun _ : Space n => (1 : ℝ)) ⋆[lsmul ℝ ℝ, μ] k) :=
    hkc.contDiff_convolution_right (lsmul ℝ ℝ) (integrable_const 1).locallyIntegrable hk
  apply hs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds x zero_lt_one] with z hz
  change (∫ y, g (z - y) ∂μ) = ∫ y, (lsmul ℝ ℝ) 1 (k (z - y)) ∂μ
  apply integral_congr_ae
  filter_upwards [μ.support_mem_ae] with y hy
  have hyR : ‖y‖ ≤ R := by simpa using hsub hy
  have hzR : ‖z‖ < ‖x‖ + 1 := by
    have hh := norm_le_norm_add_norm_sub' z x
    have hd : ‖z - x‖ < 1 := by simpa [dist_eq_norm] using hz
    linarith
  have hb : b (z - y) = 1 := b.one_of_mem_closedBall (by
    change dist (z - y) 0 ≤ ‖x‖ + R + 1
    rw [dist_zero_right]
    exact (norm_sub_le z y).trans (by linarith))
  simp [k, hb]

end KLS
end

#print axioms KLS.contDiff_integral_translate_of_compact_support
