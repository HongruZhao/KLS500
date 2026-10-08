import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Pairwise squared differences and L² membership

A finite nonnegative integral of pairwise squared differences forces L²
membership for real-valued functions on a probability space. The proof first
selects one integrable fiber by Fubini, then adds back its finite constant.
No Poincaré inequality or finite-energy-to-L² implication is assumed.

The second part records the pairwise variance identity in extended nonnegative
reals. Its infinite case is proved separately, so divergent real integrals are
never interpreted as finite variances.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped ENNReal Topology

namespace KLS

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {f : Ω → ℝ}

/-- An integrable pairwise square has an integrable fiber; shifting the function
by that fiber's value gives L² membership of the original function. -/
theorem memLp_two_of_integrable_pairwise_sq
    (hf : AEStronglyMeasurable f μ)
    (hpair : Integrable (fun z : Ω × Ω => (f z.1 - f z.2) ^ 2) (μ.prod μ)) :
    MemLp f 2 μ := by
  obtain ⟨y, hy⟩ := hpair.prod_left_ae.exists
  have hshift : MemLp (fun x => f x - f y) 2 μ :=
    (memLp_two_iff_integrable_sq (hf.sub aestronglyMeasurable_const)).mpr hy
  convert hshift.add (memLp_const (f y)) using 1
  ext x
  simp

/-- Finiteness is stated using a nonnegative extended integral. It is sufficient
for L² membership without first assuming integrability of `f`. -/
theorem memLp_two_of_lintegral_pairwise_sq_lt_top
    (hf : AEStronglyMeasurable f μ)
    (hpair : (∫⁻ z : Ω × Ω, ENNReal.ofReal ((f z.1 - f z.2) ^ 2)
      ∂(μ.prod μ)) < ∞) :
    MemLp f 2 μ := by
  apply memLp_two_of_integrable_pairwise_sq hf
  refine ⟨(hf.comp_fst.sub hf.comp_snd).pow 2, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun z : Ω × Ω => sq_nonneg (f z.1 - f z.2))).mpr hpair

/-- The ordinary variance of the difference of two independent copies is twice
the variance. All real variance expressions here have L² witnesses. -/
theorem variance_pairwise_sub (hf : MemLp f 2 μ) :
    variance (fun z : Ω × Ω => f z.1 - f z.2) (μ.prod μ) =
      2 * variance f μ := by
  have h := variance_add_prod hf hf.neg
  simp only [Pi.neg_apply, sub_eq_add_neg] at h ⊢
  rw [h, variance_neg]
  ring

/-- The extended pairwise square integral is twice extended variance for L²
functions on a probability space. -/
theorem lintegral_pairwise_sq_eq_two_evariance_of_memLp (hf : MemLp f 2 μ) :
    (∫⁻ z : Ω × Ω, ENNReal.ofReal ((f z.1 - f z.2) ^ 2) ∂(μ.prod μ)) =
      2 * evariance f μ := by
  have hdiff : MemLp (fun z : Ω × Ω => f z.1 - f z.2) 2 (μ.prod μ) :=
    (hf.comp_fst μ).sub (hf.comp_snd μ)
  have hint : Integrable f μ := hf.integrable (by norm_num)
  have hmean : (∫ z : Ω × Ω, f z.1 - f z.2 ∂(μ.prod μ)) = 0 := by
    rw [integral_sub (hint.comp_fst μ) (hint.comp_snd μ),
      integral_fun_fst, integral_fun_snd]
    simp
  calc
    (∫⁻ z : Ω × Ω, ENNReal.ofReal ((f z.1 - f z.2) ^ 2) ∂(μ.prod μ)) =
        evariance (fun z : Ω × Ω => f z.1 - f z.2) (μ.prod μ) := by
          rw [evariance_eq_lintegral_ofReal, hmean]
          simp
    _ = ENNReal.ofReal
        (variance (fun z : Ω × Ω => f z.1 - f z.2) (μ.prod μ)) :=
      (ofReal_variance hdiff).symm
    _ = 2 * evariance f μ := by
      rw [variance_pairwise_sub hf, ENNReal.ofReal_mul (by norm_num),
        ofReal_variance hf]
      norm_num

/-- The pairwise variance identity includes non-L² functions: in that case both
sides are infinite, as proved using the finite-fiber implication above. -/
theorem lintegral_pairwise_sq_eq_two_evariance
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ z : Ω × Ω, ENNReal.ofReal ((f z.1 - f z.2) ^ 2) ∂(μ.prod μ)) =
      2 * evariance f μ := by
  by_cases hL2 : MemLp f 2 μ
  · exact lintegral_pairwise_sq_eq_two_evariance_of_memLp hL2
  · have hpair : (∫⁻ z : Ω × Ω, ENNReal.ofReal ((f z.1 - f z.2) ^ 2)
        ∂(μ.prod μ)) = ∞ := by
      apply eq_top_iff.mpr
      apply le_of_not_gt
      intro hfinite
      exact hL2 (memLp_two_of_lintegral_pairwise_sq_lt_top hf hfinite)
    rw [hpair, evariance_eq_top hf hL2]
    simp

/-- A uniform bound on extended variances survives almost-everywhere convergence.
The proof uses Fatou on pairwise differences, so convergence of the means is not
required and is not assumed. -/
theorem evariance_le_of_ae_tendsto {F : ℕ → Ω → ℝ} {B : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, evariance (F n) μ ≤ B) :
    evariance f μ ≤ B := by
  let G : ℕ → Ω × Ω → ℝ≥0∞ :=
    fun n z => ENNReal.ofReal ((F n z.1 - F n z.2) ^ 2)
  have hG : ∀ n, AEMeasurable (G n) (μ.prod μ) := by
    intro n
    exact (((hF n).comp_fst.sub (hF n).comp_snd).pow 2).aemeasurable.ennreal_ofReal
  have hlim : ∀ᵐ z : Ω × Ω ∂(μ.prod μ),
      Tendsto (fun n => G n z) atTop
        (𝓝 (ENNReal.ofReal ((f z.1 - f z.2) ^ 2))) := by
    filter_upwards [quasiMeasurePreserving_fst.ae hconv,
      quasiMeasurePreserving_snd.ae hconv] with z hx hy
    exact ENNReal.tendsto_ofReal ((hx.sub hy).pow 2)
  have hpair : (∫⁻ z : Ω × Ω, ENNReal.ofReal ((f z.1 - f z.2) ^ 2)
      ∂(μ.prod μ)) ≤ 2 * B := by
    calc
      _ = ∫⁻ z, liminf (fun n => G n z) atTop ∂(μ.prod μ) := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with z hz
        exact hz.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ z, G n z ∂(μ.prod μ)) atTop :=
        lintegral_liminf_le' hG
      _ ≤ 2 * B := by
        apply liminf_le_of_frequently_le'
        apply Filter.Frequently.of_forall
        intro n
        change (∫⁻ z : Ω × Ω, ENNReal.ofReal ((F n z.1 - F n z.2) ^ 2)
          ∂(μ.prod μ)) ≤ 2 * B
        rw [lintegral_pairwise_sq_eq_two_evariance (hF n)]
        gcongr
        exact hbound n
  rw [lintegral_pairwise_sq_eq_two_evariance hf] at hpair
  exact (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp hpair

/-- Finite uniform variance bounds along an a.e.-convergent sequence establish
L² membership of the limit as well as its variance bound. -/
theorem memLp_two_and_evariance_le_of_ae_tendsto {F : ℕ → Ω → ℝ} {B : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, evariance (F n) μ ≤ B) (hB : B < ∞) :
    MemLp f 2 μ ∧ evariance f μ ≤ B := by
  have h := evariance_le_of_ae_tendsto hf hF hconv hbound
  exact ⟨(evariance_lt_top_iff_memLp hf).mp (h.trans_lt hB), h⟩

/-- Symmetric value truncation at the nonnegative integer radius `n`. -/
def symmetricTruncation (n : ℕ) (f : Ω → ℝ) (x : Ω) : ℝ :=
  max (-(n : ℝ)) (min (f x) (n : ℝ))

omit [IsProbabilityMeasure μ] in
/-- Value truncation preserves almost-everywhere strong measurability. -/
theorem aestronglyMeasurable_symmetricTruncation
    (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    AEStronglyMeasurable (symmetricTruncation n f) μ := by
  have h : AEMeasurable (symmetricTruncation n f) μ :=
    aemeasurable_const.max (hf.aemeasurable.min aemeasurable_const)
  exact h.aestronglyMeasurable

/-- Each truncation is L² on a probability space; no integrability of the
original function is required. -/
theorem memLp_two_symmetricTruncation
    (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    MemLp (symmetricTruncation n f) 2 μ := by
  apply memLp_of_bounded (a := -(n : ℝ)) (b := (n : ℝ))
    (hX := aestronglyMeasurable_symmetricTruncation hf n)
  apply Filter.Eventually.of_forall
  intro x
  refine ⟨le_max_left _ _, max_le ?_ (min_le_right _ _)⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

omit [MeasurableSpace Ω] in
/-- At each point, the truncations eventually equal the finite real value of the
original function, hence converge to it. -/
theorem tendsto_symmetricTruncation (f : Ω → ℝ) (x : Ω) :
    Tendsto (fun n => symmetricTruncation n f x) atTop (𝓝 (f x)) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_ge |f x|
  apply Filter.eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  have habs : |f x| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
  have hupper : f x ≤ (n : ℝ) := (le_abs_self _).trans habs
  have hlower : -(n : ℝ) ≤ f x := (neg_le_neg habs).trans (neg_abs_le _)
  simp only [symmetricTruncation, min_eq_left hupper, max_eq_right hlower]

omit [MeasurableSpace Ω] in
/-- Symmetric value truncation preserves local Lipschitz regularity. -/
theorem locallyLipschitz_symmetricTruncation [PseudoMetricSpace Ω]
    (hf : LocallyLipschitz f) (n : ℕ) :
    LocallyLipschitz (symmetricTruncation n f) :=
  (hf.min_const (n : ℝ)).const_max (-(n : ℝ))

/-- Uniformly bounded variances of value truncations prove L² membership and the
same variance bound for the untruncated function. This theorem assumes no L²
membership of the original function. -/
theorem memLp_two_and_evariance_le_of_truncation_bound {B : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ)
    (hbound : ∀ n, evariance (symmetricTruncation n f) μ ≤ B) (hB : B < ∞) :
    MemLp f 2 μ ∧ evariance f μ ≤ B := by
  exact memLp_two_and_evariance_le_of_ae_tendsto hf
    (aestronglyMeasurable_symmetricTruncation hf)
    (Filter.Eventually.of_forall (tendsto_symmetricTruncation f)) hbound hB

end KLS

#print axioms KLS.memLp_two_of_integrable_pairwise_sq
#print axioms KLS.memLp_two_of_lintegral_pairwise_sq_lt_top
#print axioms KLS.variance_pairwise_sub
#print axioms KLS.lintegral_pairwise_sq_eq_two_evariance_of_memLp
#print axioms KLS.lintegral_pairwise_sq_eq_two_evariance

#print axioms KLS.evariance_le_of_ae_tendsto
#print axioms KLS.memLp_two_and_evariance_le_of_ae_tendsto

#print axioms KLS.aestronglyMeasurable_symmetricTruncation
#print axioms KLS.memLp_two_symmetricTruncation
#print axioms KLS.tendsto_symmetricTruncation
#print axioms KLS.locallyLipschitz_symmetricTruncation
#print axioms KLS.memLp_two_and_evariance_le_of_truncation_bound
