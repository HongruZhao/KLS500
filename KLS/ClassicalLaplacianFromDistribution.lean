import KLS.MomentL2HarmonicLimit
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma integral_mul_laplacian_comm {f ψ : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, ψ x * coordinateLaplacian f x) = ∫ x, f x * coordinateLaplacian ψ x := by
  have hl (i : Fin n) : Integrable (fun x => ψ x * coordinateHessian f x i i) :=
    (hψ.continuous.mul (contDiff_coordinateHessian hf (m := 0) (by norm_num) i i).continuous).integrable_of_hasCompactSupport
      hc.mul_right
  have hr (i : Fin n) : Integrable (fun x => coordinateDerivative ψ i x * coordinateDerivative f i x) :=
    ((contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.mul
      (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative hc i).mul_right
  have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => integral_mul_coordinateDerivative_of_hasCompactSupport_left
      (hψ.of_le (by norm_num)) (contDiff_coordinateDerivative hf (m := 1) (by norm_num) i) hc i)
  change (∑ i, ∫ x, ψ x * coordinateHessian f x i i) =
    ∑ i, -(∫ x, coordinateDerivative ψ i x * coordinateDerivative f i x) at he
  rw [← integral_finsetSum _ (fun i _ => hl i), Finset.sum_neg_distrib,
    ← integral_finsetSum _ (fun i _ => hr i)] at he
  have he1 : (fun x => ∑ i, ψ x * coordinateHessian f x i i) =
      (fun x => ψ x * coordinateLaplacian f x) := by
    funext x
    simp only [coordinateLaplacian, Finset.mul_sum]
  have he2 : (fun x => ∑ i, coordinateDerivative ψ i x * coordinateDerivative f i x) =
      (fun x => inner ℝ (gradient ψ x) (gradient f x)) := by
    funext x
    simp only [coordinateDerivative_eq_gradient, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, mul_comm]
  rw [he1, he2, integral_inner_gradient_eq_neg_laplacian_pairing
    (hf.of_le (by norm_num)) hψ hc, neg_neg] at he
  exact he

lemma coordinateLaplacian_eq_zero_on_of_distribution
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) {U : Set (Space n)} (hU : IsOpen U)
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ x, f x * coordinateLaplacian ψ x) = 0) :
    ∀ x ∈ U, coordinateLaplacian f x = 0 := by
  have hL := continuous_coordinateLaplacian hf
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hL.continuousOn.locallyIntegrableOn hU.measurableSet)
    (fun ψ hψ hc hs => by
      simpa only [smul_eq_mul, integral_mul_laplacian_comm hf (hψ.of_le (by simp)) hc] using
        hdist ψ (hψ.of_le (by simp)) hc hs)
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).mpr hae) hU
    hL.continuousOn continuousOn_const

lemma integral_mul_compact_test_congr_ae_on {f g b : Space n → ℝ}
    {U : Set (Space n)} (hU : MeasurableSet U) (he : f =ᵐ[volume.restrict U] g)
    (hs : tsupport b ⊆ U) : (∫ x, f x * b x) = ∫ x, g x * b x := by
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU).mp he] with x hx
  by_cases hxu : x ∈ U
  · rw [hx hxu]
  · have hb : b x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hxu (hs ht))
    rw [hb, mul_zero, mul_zero]

/-- A function smooth only on its open domain and distribution harmonic
there satisfies the actual classical Laplace equation at every point. -/
theorem coordinateLaplacian_eq_zero_on_of_contDiffOn_distribution
    {f : Space n → ℝ} {U : Set (Space n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ x, f x * coordinateLaplacian ψ x) = 0) :
    ∀ x ∈ U, coordinateLaplacian f x = 0 := by
  intro x hx
  obtain ⟨g, hg, he⟩ := exists_global_smooth_eq_near_compact hU hf isCompact_singleton
    (singleton_subset_iff.mpr hx)
  have hex : g =ᶠ[𝓝 x] f := he.filter_mono (nhds_le_nhdsSet (mem_singleton x))
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff.mp (hex.and (hU.mem_nhds hx))
  have hgdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball x r → (∫ y, g y * coordinateLaplacian ψ y) = 0 := by
    intro ψ hψ hc hs
    have hsub : ball x r ⊆ U := fun y hy => (hnear hy).2
    rw [← hdist ψ hψ hc (hs.trans hsub)]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      by_cases hy : y ∈ tsupport (coordinateLaplacian ψ)
      · rw [(hnear (hs (tsupport_coordinateLaplacian_subset ψ hy))).1]
      · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero]
  have hz := coordinateLaplacian_eq_zero_on_of_distribution (hg.of_le (by simp)) isOpen_ball
    hgdist x (mem_ball_self hr)
  rwa [coordinateLaplacian_eq_of_eventuallyEq hex] at hz

end KLS
end
