import KLS.ExponentialMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# A scalar weighted inequality for the rate-one exponential law

The finite-interval argument applies to every locally Lipschitz function.
Absolute continuity supplies integration by parts, and the boundary term at
the right endpoint is nonnegative. No decay hypothesis at infinity is used.
-/

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Set Filter

noncomputable section
namespace KLS.ExponentialPoincare

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

/-- A locally Lipschitz real function is absolutely continuous on every compact interval. -/
theorem locallyLipschitz_absolutelyContinuous {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    (a b : ℝ) : AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    isCompact_uIcc hf.locallyLipschitzOn
  exact hK.absolutelyContinuousOnInterval

/-- The total derivative is square-integrable on every nonnegative finite interval. -/
theorem intervalIntegrable_deriv_sq {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun x => (deriv f x) ^ 2) volume 0 R := by
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) (R + 1)))
    hf.locallyLipschitzOn
  apply (intervalIntegrable_const (c := (K : ℝ) ^ 2)).mono_fun'
    ((measurable_deriv f).pow_const 2).aestronglyMeasurable
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  filter_upwards with x hx
  have hx' : x ∈ Ioc (0 : ℝ) R := by simpa [uIoc_of_le hR] using hx
  have hk : ‖deriv f x‖ ≤ K := norm_deriv_le_of_lipschitzOn
    (Icc_mem_nhds (by linarith [hx'.1] : (-1 : ℝ) < x)
      (by linarith [hx'.2] : x < R + 1)) hK
  simpa [norm_pow, Real.norm_eq_abs, sq_abs] using
    pow_le_pow_left₀ (norm_nonneg (deriv f x)) hk 2

/-- Finite-interval weighted Hardy inequality anchored at zero. -/
theorem weighted_anchor_interval_le {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in 0..R, (f x - f 0) ^ 2 * Real.exp (-x)) ≤
      4 * ∫ x in 0..R, (deriv f x) ^ 2 * Real.exp (-x) := by
  let h : ℝ → ℝ := fun x => f x - f 0
  have hh : LocallyLipschitz h := hf.sub (LocallyLipschitz.const (f 0))
  have hhac := locallyLipschitz_absolutelyContinuous hh 0 R
  have hwac : AbsolutelyContinuousOnInterval (fun x : ℝ => Real.exp (-x)) 0 R :=
    locallyLipschitz_absolutelyContinuous (ContDiff.locallyLipschitz (𝕂 := ℝ) (by fun_prop)) 0 R
  have hFac : AbsolutelyContinuousOnInterval (fun x => h x ^ 2 * Real.exp (-x)) 0 R := by
    simpa only [pow_two] using (hhac.fun_mul hhac).fun_mul hwac
  have hI : IntervalIntegrable (fun x => h x ^ 2 * Real.exp (-x)) volume 0 R :=
    ((hh.continuous.pow 2).mul (by fun_prop)).intervalIntegrable 0 R
  have hJ : IntervalIntegrable (fun x => (deriv f x) ^ 2 * Real.exp (-x)) volume 0 R :=
    (intervalIntegrable_deriv_sq hf hR).mul_continuousOn (by fun_prop)
  have hrhs : IntervalIntegrable
      (fun x => -(1 / 2 : ℝ) * (h x ^ 2 * Real.exp (-x)) +
        2 * ((deriv f x) ^ 2 * Real.exp (-x))) volume 0 R :=
    (hI.const_mul _).add (hJ.const_mul _)
  have hmono :
      (∫ x in 0..R, deriv (fun y => h y ^ 2 * Real.exp (-y)) x) ≤
      ∫ x in 0..R, -(1 / 2 : ℝ) * (h x ^ 2 * Real.exp (-x)) +
        2 * ((deriv f x) ^ 2 * Real.exp (-x)) := by
    apply intervalIntegral.integral_mono_ae_restrict hR hFac.intervalIntegrable_deriv hrhs
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hhac.ae_differentiableAt] with x hx hxin
    have hx' := hx (by simpa [uIcc_of_le hR] using hxin)
    have hw : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
      simpa using (hasDerivAt_id x).neg.exp
    have hd := (hx'.hasDerivAt.fun_pow 2).fun_mul hw
    have hder : deriv (fun y => h y ^ 2 * Real.exp (-y)) x =
        (2 * h x * deriv f x - h x ^ 2) * Real.exp (-x) := by
      rw [hd.deriv]
      simp only [h, deriv_sub_const, Nat.cast_ofNat]
      ring
    rw [hder]
    have hsq := mul_nonneg (sq_nonneg (h x - 2 * deriv f x)) (Real.exp_pos (-x)).le
    nlinarith
  rw [hFac.integral_deriv_eq_sub] at hmono
  rw [intervalIntegral.integral_add (hI.const_mul _) (hJ.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  have hzero : h 0 = 0 := by simp [h]
  rw [hzero] at hmono
  have hb : 0 ≤ h R ^ 2 * Real.exp (-R) := by positivity
  change (∫ x in 0..R, h x ^ 2 * Real.exp (-x)) ≤ _
  nlinarith

private theorem ofReal_weighted_interval {g : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hg : IntervalIntegrable (fun x => g x ^ 2 * Real.exp (-x)) volume 0 R) :
    ENNReal.ofReal (∫ x in 0..R, g x ^ 2 * Real.exp (-x)) =
      ∫⁻ x in Icc 0 R, ENNReal.ofReal (g x ^ 2 * Real.exp (-x)) := by
  rw [intervalIntegral.integral_of_le hR, ← integral_Icc_eq_integral_Ioc]
  exact ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hR).mp hg)
    (Filter.Eventually.of_forall fun x => by positivity)

/-- Monotone passage to the half-line keeps infinite derivative energy as infinity. -/
theorem weighted_anchor_halfLine_le {f : ℝ → ℝ} (hf : LocallyLipschitz f) :
    (∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal ((f x - f 0) ^ 2 * Real.exp (-x))) ≤
      4 * ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal ((deriv f x) ^ 2 * Real.exp (-x)) := by
  have hinterval (R : ℝ) (hR : 0 ≤ R) :
      (∫⁻ x in Icc 0 R, ENNReal.ofReal ((f x - f 0) ^ 2 * Real.exp (-x))) ≤
        4 * ∫⁻ x in Icc 0 R, ENNReal.ofReal ((deriv f x) ^ 2 * Real.exp (-x)) := by
    have h := ENNReal.ofReal_le_ofReal (weighted_anchor_interval_le hf hR)
    have hI : IntervalIntegrable (fun x => (f x - f 0) ^ 2 * Real.exp (-x)) volume 0 R :=
      (((hf.continuous.sub continuous_const).pow 2).mul (by fun_prop)).intervalIntegrable 0 R
    have hJ : IntervalIntegrable (fun x => (deriv f x) ^ 2 * Real.exp (-x)) volume 0 R :=
      (intervalIntegrable_deriv_sq hf hR).mul_continuousOn (by fun_prop)
    rwa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat,
      ofReal_weighted_interval hR hI, ofReal_weighted_interval hR hJ] at h
  have hcover : (⋃ n : ℕ, Icc (0 : ℝ) n) = Ici (0 : ℝ) := by
    ext x
    simp only [mem_iUnion, mem_Icc, mem_Ici]
    constructor
    · rintro ⟨n, hx, _⟩
      exact hx
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, hx, hn⟩
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Icc (0 : ℝ) n) := by
    intro i j
    refine ⟨max i j, Icc_subset_Icc_right ?_, Icc_subset_Icc_right ?_⟩
    · exact_mod_cast le_max_left i j
    · exact_mod_cast le_max_right i j
  calc
    _ = ⨆ n : ℕ, ∫⁻ x in Icc (0 : ℝ) n,
        ENNReal.ofReal ((f x - f 0) ^ 2 * Real.exp (-x)) := by
      rw [← hcover]
      exact setLIntegral_iUnion_of_directed _ hdir
    _ ≤ _ := by
      apply iSup_le
      intro n
      apply (hinterval n (by positivity)).trans
      gcongr
      exact Icc_subset_Ici_self

/-- The weighted half-line integral is the integral for the actual exponential law. -/
theorem lintegral_expMeasure_one_sq (g : ℝ → ℝ) (hg : Measurable g) :
    (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂expMeasure 1) =
      ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (g x ^ 2 * Real.exp (-x)) := by
  change (∫⁻ x, ENNReal.ofReal (g x ^ 2)
    ∂(volume : Measure ℝ).withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (by unfold exponentialPDF; fun_prop)
    (by fun_prop)]
  have heq : (fun x => (exponentialPDF 1 * fun x => ENNReal.ofReal (g x ^ 2)) x) =
      (Ici (0 : ℝ)).indicator (fun x => ENNReal.ofReal (g x ^ 2 * Real.exp (-x))) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp [exponentialPDF_eq, hx, ENNReal.ofReal_mul (sq_nonneg (g x)), mul_comm]
    · simp [exponentialPDF_eq, hx]
  rw [heq, lintegral_indicator measurableSet_Ici]

/-- A weighted Hardy bound for the standard exponential probability law, valid in extended reals. -/
theorem expMeasure_anchor_le {f : ℝ → ℝ} (hf : LocallyLipschitz f) :
    (∫⁻ x, ENNReal.ofReal ((f x - f 0) ^ 2) ∂expMeasure 1) ≤
      4 * ∫⁻ x, ENNReal.ofReal ((deriv f x) ^ 2) ∂expMeasure 1 := by
  rw [lintegral_expMeasure_one_sq (fun x => f x - f 0)
    (hf.continuous.measurable.sub measurable_const),
    lintegral_expMeasure_one_sq _ (measurable_deriv f)]
  exact weighted_anchor_halfLine_le hf

/-- The scalar Poincaré inequality for all locally Lipschitz L² tests of the actual exponential law. -/
theorem evariance_expMeasure_le {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    (hf2 : MemLp f 2 (expMeasure 1)) :
    ProbabilityTheory.evariance f (expMeasure 1) ≤
      4 * ∫⁻ x, ENNReal.ofReal ((deriv f x) ^ 2) ∂expMeasure 1 := by
  have hcenter : MemLp (fun x => f x - f 0) 2 (expMeasure 1) := hf2.sub (memLp_const _)
  have hint : Integrable (fun x => (f x - f 0) ^ 2) (expMeasure 1) :=
    (memLp_two_iff_integrable_sq hcenter.aestronglyMeasurable).mp hcenter
  have hv := variance_le_expectation_sq hcenter.aestronglyMeasurable
  rw [ProbabilityTheory.variance_sub_const hf2.aestronglyMeasurable] at hv
  have hext := ENNReal.ofReal_le_ofReal hv
  rw [ProbabilityTheory.ofReal_variance hf2] at hext
  have hi : ENNReal.ofReal (∫ x, (f x - f 0) ^ 2 ∂expMeasure 1) =
      ∫⁻ x, ENNReal.ofReal ((f x - f 0) ^ 2) ∂expMeasure 1 :=
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)
  change ProbabilityTheory.evariance f (expMeasure 1) ≤
    ENNReal.ofReal (∫ x, (f x - f 0) ^ 2 ∂expMeasure 1) at hext
  exact (hext.trans_eq hi).trans (expMeasure_anchor_le hf)

end KLS.ExponentialPoincare
end

#print axioms KLS.ExponentialPoincare.locallyLipschitz_absolutelyContinuous
#print axioms KLS.ExponentialPoincare.intervalIntegrable_deriv_sq
#print axioms KLS.ExponentialPoincare.weighted_anchor_interval_le

#print axioms KLS.ExponentialPoincare.weighted_anchor_halfLine_le
#print axioms KLS.ExponentialPoincare.evariance_expMeasure_le
