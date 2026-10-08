import KLS.CenteredL2Variational
import KLS.WeightedDiffusionLinear

/-!
# The concrete diffusion range and its explicit density obligation

The range consists of actual negative weighted diffusions of C³ compactly
supported functions, represented in the genuine weighted L² space. Its
linearity and zero mean are proved. The density assertion is separately
named and remains a hypothesis in the Brascamp--Lieb variance theorem.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter
open scoped Topology ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

/-- Actual compact smooth diffusion images, with equality in genuine weighted L². -/
def compactDiffusionRange (φ : Space n → ℝ) :
    Submodule ℝ (Lp ℝ 2 (potentialMeasure φ)) where
  carrier := {u | ∃ g : Space n → ℝ, ContDiff ℝ 3 g ∧ HasCompactSupport g ∧
    (u : Space n → ℝ) =ᵐ[potentialMeasure φ] fun x => -weightedDiffusion φ g x}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx
    simpa only [weightedDiffusion_zero, neg_zero, Pi.zero_apply] using hx
  add_mem' := by
    rintro u v ⟨g, hg, hgc, hu⟩ ⟨h, hh, hhc, hv⟩
    refine ⟨g + h, hg.add hh, hgc.add hhc, ?_⟩
    filter_upwards [Lp.coeFn_add u v, hu, hv] with x hx hy hz
    rw [hx, Pi.add_apply, hy, hz,
      weightedDiffusion_add (hg.of_le (by norm_num)) (hh.of_le (by norm_num))]
    ring
  smul_mem' := by
    rintro c u ⟨g, hg, hgc, hu⟩
    refine ⟨c • g, hg.const_smul c, hgc.smul_left, ?_⟩
    filter_upwards [Lp.coeFn_smul c u, hu] with x hx hy
    rw [hx, Pi.smul_apply, smul_eq_mul, hy,
      weightedDiffusion_smul (hg.of_le (by norm_num))]
    ring

lemma mem_compactDiffusionRange_iff {φ : Space n → ℝ}
    {u : Lp ℝ 2 (potentialMeasure φ)} :
    u ∈ compactDiffusionRange φ ↔
      ∃ g : Space n → ℝ, ContDiff ℝ 3 g ∧ HasCompactSupport g ∧
        (u : Space n → ℝ) =ᵐ[potentialMeasure φ] fun x => -weightedDiffusion φ g x := Iff.rfl

lemma integral_eq_zero_of_mem_compactDiffusionRange {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) {u : Lp ℝ 2 (potentialMeasure φ)}
    (hu : u ∈ compactDiffusionRange φ) :
    (∫ x, u x ∂potentialMeasure φ) = 0 := by
  rcases hu with ⟨g, hg, hc, hu⟩
  rw [integral_congr_ae hu, integral_neg,
    integral_weightedDiffusion_eq_zero_of_hasCompactSupport
      (hφ.of_le (by norm_num)) (hg.of_le (by norm_num)) hc, neg_zero]

/-- The unresolved analytic density statement, stated in the L² norm topology. -/
def DiffusionRangeDense (φ : Space n → ℝ) : Prop :=
  ∀ u : Lp ℝ 2 (potentialMeasure φ), (∫ x, u x ∂potentialMeasure φ) = 0 →
    u ∈ (compactDiffusionRange φ).topologicalClosure

lemma memLp_of_continuous_hasCompactSupport {φ f : Space n → ℝ}
    (hφ : Continuous φ) (hf : Continuous f) (hc : HasCompactSupport f) :
    MemLp f 2 (potentialMeasure φ) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  apply integrable_potentialMeasure_of_continuous_hasCompactSupport hφ (hf.pow 2)
  simpa only [pow_two] using hc.mul_right (f' := f)

/-- Every actual smooth compact diffusion has its canonical L² representative in the range. -/
lemma toLp_neg_weightedDiffusion_mem {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    ((memLp_weightedDiffusion_of_hasCompactSupport hφ hg hc).neg.toLp
      (fun x => -weightedDiffusion φ g x)) ∈ compactDiffusionRange φ :=
  ⟨g, hg, hc, (memLp_weightedDiffusion_of_hasCompactSupport hφ hg hc).neg.coeFn_toLp⟩

/-- Full compact-test variance bound, conditional only on the explicitly named range density
in addition to the actual potential regularity, normalization and Hessian hypotheses. -/
theorem brascampLieb_variance_of_diffusionRangeDense {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (hc : HasCompactSupport f)
    (hdense : DiffusionRangeDense φ) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      ∫ x, inverseHessianGradientForm φ f x ∂potentialMeasure φ := by
  let hf2 := memLp_of_continuous_hasCompactSupport hφ.continuous hf.continuous hc
  let F : Lp ℝ 2 (potentialMeasure φ) := hf2.toLp f
  have hF : (F : Space n → ℝ) =ᵐ[potentialMeasure φ] f := hf2.coeFn_toLp
  have hclosure : CenteredL2.center (potentialMeasure φ) F ∈
      closure (compactDiffusionRange φ : Set (Lp ℝ 2 (potentialMeasure φ))) :=
    hdense _ (CenteredL2.integral_center _ F)
  have hbound : ∀ v ∈ compactDiffusionRange φ,
      2 * inner ℝ F v - ‖v‖ ^ 2 ≤
        ∫ x, inverseHessianGradientForm φ f x ∂potentialMeasure φ := by
    rintro v ⟨g, hg, hgc, hv⟩
    have hi : inner ℝ F v =
        ∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hF, hv] with x hx hy
      simp [hx, hy, RCLike.inner_apply, mul_comm]
    have hn : ‖v‖ ^ 2 =
        ∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      simp [hx, RCLike.inner_apply, pow_two]
    rw [hi, hn]
    exact brascampLieb_dual_diffusion hφ hf hg hpos hc hgc
  have he := CenteredL2.variance_le_of_center_mem_closure (potentialMeasure φ) hclosure hbound
  rwa [ProbabilityTheory.variance_congr hF] at he

end KLS
end

#print axioms KLS.compactDiffusionRange
#print axioms KLS.integral_eq_zero_of_mem_compactDiffusionRange
#print axioms KLS.toLp_neg_weightedDiffusion_mem
#print axioms KLS.brascampLieb_variance_of_diffusionRangeDense
