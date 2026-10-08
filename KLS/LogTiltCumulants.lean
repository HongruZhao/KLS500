import KLS.TiltCumulants
import KLS.TiltMoments
import KLS.ThirdCumulant

/-!
# Log-partition derivatives and the BKL third-moment matrix

The first four directional log-partition derivatives are identified with
actual tilted means, covariances and centered cumulants. The derivative of the
coordinate covariance at an isotropic law is the existing BKL third-cumulant
matrix, with all compact-support moment hypotheses discharged.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

noncomputable section
namespace KLS

theorem iteratedDeriv_one_log_tiltPartition {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q s : Space n → ℝ} (hq : Continuous q) (hs : Continuous s) (t : ℝ) :
    iteratedDeriv 1 (fun u : ℝ => Real.log (tiltPartition μ (fun x => q x + u * s x))) t =
      tiltAverage μ (fun x => q x + t * s x) s := by
  simpa only [iteratedDeriv_one] using (hasDerivAt_log_tiltPartition hμ hq hs t).deriv

theorem iteratedDeriv_two_log_tiltPartition {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q s : Space n → ℝ} (hq : Continuous q) (hs : Continuous s) (t : ℝ) :
    iteratedDeriv 2 (fun u : ℝ => Real.log (tiltPartition μ (fun x => q x + u * s x))) t =
      covariance s s (μ.tilted (fun x => q x + t * s x)) := by
  rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ,
    funext (iteratedDeriv_one_log_tiltPartition hμ hq hs)]
  have := tilted_isProbability_of_compact_support hμ (q := fun x => q x + t * s x)
    (by fun_prop)
  rw [(hasDerivAt_tiltAverage hμ hq hs
    (integrable_of_continuous_compact_support_measure hμ hs) t).deriv,
    covariance_eq_sub (memLp_two_continuous_tilted hμ (by fun_prop) hs)
      (memLp_two_continuous_tilted hμ (by fun_prop) hs)]
  rfl

theorem iteratedDeriv_three_log_tiltPartition {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q s : Space n → ℝ} (hq : Continuous q) (hs : Continuous s) (t : ℝ) :
    iteratedDeriv 3 (fun u : ℝ => Real.log (tiltPartition μ (fun x => q x + u * s x))) t =
      tiltThirdCumulant μ (fun x => q x + t * s x) s s s := by
  rw [show 3 = 2 + 1 from rfl, iteratedDeriv_succ,
    funext (iteratedDeriv_two_log_tiltPartition hμ hq hs)]
  exact (hasDerivAt_tilted_covariance hμ hq hs hs hs t).deriv

theorem iteratedDeriv_four_log_tiltPartition {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q s : Space n → ℝ} (hq : Continuous q) (hs : Continuous s) (t : ℝ) :
    iteratedDeriv 4 (fun u : ℝ => Real.log (tiltPartition μ (fun x => q x + u * s x))) t =
      tiltFourthCumulant μ (fun x => q x + t * s x) s s s s := by
  rw [show 4 = 3 + 1 from rfl, iteratedDeriv_succ,
    funext (iteratedDeriv_three_log_tiltPartition hμ hq hs)]
  exact (hasDerivAt_tiltThirdCumulant hμ hq hs hs hs hs t).deriv

theorem hasDerivAt_exponentialTilt_covariance {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {f g : Space n → ℝ} (hf : Continuous f) (hg : Continuous g)
    (z v : Space n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => covariance f g (exponentialTilt μ (z + u • v)))
      (tiltThirdCumulant μ (fun x => inner ℝ (z + t • v) x) f g
        (fun x => inner ℝ v x)) t := by
  simpa only [exponentialTilt, inner_add_left, inner_smul_left, RCLike.conj_to_real] using
    hasDerivAt_tilted_covariance hμ (q := fun x => inner ℝ z x)
      (s := fun x => inner ℝ v x) (by fun_prop) hf hg (by fun_prop) t

theorem IsIsotropic.tiltThirdCumulant_zero {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hiso : IsIsotropic μ) (u : Space n) (i j : Fin n) :
    tiltThirdCumulant μ (fun _ => 0) (fun x => x i) (fun x => x j)
      (fun x => inner ℝ u x) = thirdCumulantMatrix μ u i j := by
  have hinner : (∫ x, inner ℝ u x ∂μ) = 0 := by
    simpa only [real_inner_comm u] using hiso.integral_inner u
  simp only [tiltThirdCumulant, tiltAverage, tilted_const, hiso.integral_coordinate,
    hinner, sub_zero, thirdCumulantMatrix]
  congr 1
  funext x
  rw [real_inner_comm u x]
  ring

theorem IsIsotropic.hasDerivAt_covariance_eq_thirdCumulant {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (hiso : IsIsotropic μ) (u : Space n) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => covariance (fun x : Space n => x i) (fun x => x j)
      (exponentialTilt μ (t • u))) (thirdCumulantMatrix μ u i j) 0 := by
  have hd := hasDerivAt_exponentialTilt_covariance hμ
    (f := fun x => x i) (g := fun x => x j) (by fun_prop) (by fun_prop) 0 u 0
  simpa only [zero_add, zero_smul, inner_zero_left, hiso.tiltThirdCumulant_zero] using hd

end KLS
end

#print axioms KLS.iteratedDeriv_four_log_tiltPartition
#print axioms KLS.hasDerivAt_exponentialTilt_covariance
#print axioms KLS.IsIsotropic.hasDerivAt_covariance_eq_thirdCumulant
