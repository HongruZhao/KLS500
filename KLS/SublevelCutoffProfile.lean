import KLS.HessianMetricComposition

/-!
# A concrete sublevel cutoff and its controlling primitive

The cutoff is mathlib's smooth transition applied to `2-t`. The auxiliary
primitive has derivative exactly minus the absolute second derivative.
It is C¹, which is sufficient for the proved compact-first-factor identity.
-/

open MeasureTheory Set Filter Function
open scoped Topology ContDiff

noncomputable section
namespace KLS

def sublevelCutoffProfile (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

lemma sublevelCutoffProfile_contDiff : ContDiff ℝ ∞ sublevelCutoffProfile :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

lemma sublevelCutoffProfile_nonneg (t : ℝ) : 0 ≤ sublevelCutoffProfile t :=
  Real.smoothTransition.nonneg _

lemma sublevelCutoffProfile_le_one (t : ℝ) : sublevelCutoffProfile t ≤ 1 :=
  Real.smoothTransition.le_one _

lemma sublevelCutoffProfile_one {t : ℝ} (ht : t ≤ 1) : sublevelCutoffProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma sublevelCutoffProfile_zero {t : ℝ} (ht : 2 ≤ t) : sublevelCutoffProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma sublevelCutoffProfile_antitone : Antitone sublevelCutoffProfile := by
  intro s t hst
  exact Real.smoothTransition.monotone (by linarith)

lemma tsupport_deriv_sublevelCutoffProfile : tsupport (deriv sublevelCutoffProfile) ⊆ Icc (1 : ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_cases hlt : t < 1
  · have hzero : deriv sublevelCutoffProfile t = 0 := by
      apply HasDerivAt.deriv
      apply (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hlt] with s hs
      exact sublevelCutoffProfile_one (show s ≤ 1 from le_of_lt hs)
    exact False.elim (ht hzero)
  · by_cases hgt : 2 < t
    · have hzero : deriv sublevelCutoffProfile t = 0 := by
        apply HasDerivAt.deriv
        apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds hgt] with s hs
        exact sublevelCutoffProfile_zero (show 2 ≤ s from le_of_lt hs)
      exact False.elim (ht hzero)
    · exact ⟨le_of_not_gt hlt, le_of_not_gt hgt⟩

lemma hasCompactSupport_deriv_sublevelCutoffProfile : HasCompactSupport (deriv sublevelCutoffProfile) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) tsupport_deriv_sublevelCutoffProfile

lemma sublevelCutoffProfile_second_zero {t : ℝ} (ht : 2 < t) :
    deriv (deriv sublevelCutoffProfile) t = 0 := by
  apply deriv_of_notMem_tsupport
  intro hmem
  exact (not_le_of_gt ht) (tsupport_deriv_sublevelCutoffProfile hmem).2

lemma continuous_sublevelCutoffProfile_second : Continuous (deriv (deriv sublevelCutoffProfile)) :=
  (sublevelCutoffProfile_contDiff.iterate_deriv 2).continuous

lemma integrable_sublevelCutoffProfile_second_norm :
    Integrable (fun t => ‖deriv (deriv sublevelCutoffProfile) t‖) :=
  continuous_sublevelCutoffProfile_second.norm.integrable_of_hasCompactSupport
    hasCompactSupport_deriv_sublevelCutoffProfile.deriv.norm

def sublevelCutoffTail (t : ℝ) : ℝ :=
  ∫ s in t..2, ‖deriv (deriv sublevelCutoffProfile) s‖

lemma sublevelCutoffTail_hasDerivAt (t : ℝ) :
    HasDerivAt sublevelCutoffTail (-‖deriv (deriv sublevelCutoffProfile) t‖) t := by
  have hc := continuous_sublevelCutoffProfile_second.norm
  exact intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable t 2)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma sublevelCutoffTail_deriv (t : ℝ) :
    deriv sublevelCutoffTail t = -‖deriv (deriv sublevelCutoffProfile) t‖ :=
  (sublevelCutoffTail_hasDerivAt t).deriv

lemma sublevelCutoffTail_contDiff : ContDiff ℝ 1 sublevelCutoffTail := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (sublevelCutoffTail_hasDerivAt t).differentiableAt, ?_⟩
  have heq : deriv sublevelCutoffTail = fun t => -‖deriv (deriv sublevelCutoffProfile) t‖ :=
    funext sublevelCutoffTail_deriv
  rw [heq]
  exact continuous_sublevelCutoffProfile_second.norm.neg

lemma sublevelCutoffTail_zero {t : ℝ} (ht : 2 ≤ t) : sublevelCutoffTail t = 0 := by
  unfold sublevelCutoffTail
  rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le ht]
  apply neg_eq_zero.mpr
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [sublevelCutoffProfile_second_zero hs.1, norm_zero]
  rfl

lemma sublevelCutoffTail_norm_le (t : ℝ) : ‖sublevelCutoffTail t‖ ≤
    ∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖ := by
  unfold sublevelCutoffTail
  calc
    _ ≤ ∫ s in Set.uIoc t (2 : ℝ), ‖‖deriv (deriv sublevelCutoffProfile) s‖‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖ := by
      simpa only [norm_norm] using setIntegral_le_integral integrable_sublevelCutoffProfile_second_norm
        (Eventually.of_forall (fun s => norm_nonneg (deriv (deriv sublevelCutoffProfile) s)))

lemma sublevelCutoffProfile_deriv_bounded : ∃ C : ℝ, 0 ≤ C ∧
    ∀ t, ‖deriv sublevelCutoffProfile t‖ ≤ C := by
  obtain ⟨C, hC⟩ := hasCompactSupport_deriv_sublevelCutoffProfile.exists_bound_of_continuous
    (sublevelCutoffProfile_contDiff.continuous_deriv (by simp))
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

def scaledSublevelProfile (c t : ℝ) : ℝ := sublevelCutoffProfile (c * t)

def scaledSublevelTail (c t : ℝ) : ℝ := c * sublevelCutoffTail (c * t)

lemma scaledSublevelProfile_contDiff (c : ℝ) : ContDiff ℝ ∞ (scaledSublevelProfile c) :=
  sublevelCutoffProfile_contDiff.comp (contDiff_const.mul contDiff_id)

lemma scaledSublevelTail_contDiff (c : ℝ) : ContDiff ℝ 1 (scaledSublevelTail c) :=
  contDiff_const.mul (sublevelCutoffTail_contDiff.comp (contDiff_const.mul contDiff_id))

lemma scaledSublevelProfile_deriv (c t : ℝ) :
    deriv (scaledSublevelProfile c) t = c * deriv sublevelCutoffProfile (c * t) := by
  exact deriv_comp_mul_left c sublevelCutoffProfile t

lemma scaledSublevelProfile_second (c t : ℝ) :
    deriv (deriv (scaledSublevelProfile c)) t = c ^ 2 * deriv (deriv sublevelCutoffProfile) (c * t) := by
  have heq : deriv (scaledSublevelProfile c) = fun s => c * deriv sublevelCutoffProfile (c * s) :=
    funext (scaledSublevelProfile_deriv c)
  rw [heq, deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul]
  ring

lemma scaledSublevelTail_deriv (c t : ℝ) :
    deriv (scaledSublevelTail c) t = -(c ^ 2 * ‖deriv (deriv sublevelCutoffProfile) (c * t)‖) := by
  change deriv (fun s => c * sublevelCutoffTail (c * s)) t = _
  rw [deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul, sublevelCutoffTail_deriv]
  ring

lemma scaledSublevelTail_norm_le {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    ‖scaledSublevelTail c t‖ ≤ c * (∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖) := by
  change ‖c * sublevelCutoffTail (c * t)‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (sublevelCutoffTail_norm_le _) hc

end KLS
end

#print axioms KLS.hasCompactSupport_deriv_sublevelCutoffProfile
#print axioms KLS.sublevelCutoffTail_hasDerivAt
#print axioms KLS.sublevelCutoffTail_norm_le
