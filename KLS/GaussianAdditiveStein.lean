import KLS.GaussianIntegrationByParts
import KLS.GaussianSmoothingMoments

/-!
# Gaussian addition to an actual Stein coupling

The old coupling is retained. Independent Gaussian addition changes its
Stein action from T to T+r²w. No conditional expectation or choice of a
pointwise kernel on the target is used.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff Topology RealInnerProductSpace

noncomputable section
namespace KLS

theorem gaussianSmoothing_map_eq_map_prod {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → Space n} (hX : Measurable X) (r : ℝ) :
    gaussianSmoothing (μ.map X) r =
      (μ.prod (gaussianExample n)).map (fun p => X p.1 + r • p.2) := by
  have he : (μ.map X).prod (gaussianExample n) =
      (μ.prod (gaussianExample n)).map (fun p => (X p.1, p.2)) := by
    simpa only [Measure.map_id, Prod.map_def, id_eq] using
      Measure.map_prod_map μ (gaussianExample n) hX measurable_id
  rw [gaussianSmoothing_eq_map_prod, he, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma gradient_translate {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (a x : Space n) : gradient (fun y => f (y + a)) x = gradient f (x + a) := by
  have hd := (hf (x + a)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const a)
  simp only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] at hd
  simp only [gradient, hd.fderiv]

lemma hasCompactSupport_translate {n : ℕ} {f : Space n → ℝ}
    (hf : HasCompactSupport f) (a : Space n) : HasCompactSupport (fun y => f (y + a)) :=
  hf.comp_homeomorph (Homeomorph.addRight a)

lemma memLp_inner_const {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → Space n} (hX : MemLp X 2 μ) (w : Space n) :
    MemLp (fun x => inner ℝ (X x) w) 2 μ := by
  simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm] using
    (innerSL ℝ w).comp_memLp' hX

theorem integral_gaussian_additive_stein {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X T : Ω → Space n}
    (hXm : Measurable X) (hX : MemLp X 2 μ) (hT : MemLp T 2 μ)
    (w : Space n)
    (hstein : ∀ h : Space n → ℝ, ContDiff ℝ 1 h → HasCompactSupport h →
      (∫ x, h (X x) * inner ℝ (X x) w ∂μ) =
        ∫ x, inner ℝ (gradient h (X x)) (T x) ∂μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (r : ℝ) :
    (∫ p : Ω × Space n, f (X p.1 + r • p.2) * inner ℝ (X p.1 + r • p.2) w
      ∂μ.prod (gaussianExample n)) =
      ∫ p : Ω × Space n, inner ℝ (gradient f (X p.1 + r • p.2)) (T p.1 + r ^ 2 • w)
        ∂μ.prod (gaussianExample n) := by
  let Z : Ω × Space n → Space n := fun p => X p.1 + r • p.2
  have hZm : Measurable Z := (hXm.comp measurable_fst).add (measurable_snd.const_smul r)
  have hf2 := memLp_compact_test_comp (μ := μ.prod (gaussianExample n)) hf.continuous hc hZm
  have hg2 := memLp_compact_test_gradient_comp (μ := μ.prod (gaussianExample n)) hf hc hZm
  have hX2 := (memLp_inner_const hX w).comp_fst (gaussianExample n)
  have hY2 := (memLp_inner_const
    ((ProbabilityTheory.IsGaussian.memLp_two_fun_id (μ := gaussianExample n)).const_smul r) w).comp_snd μ
  have hiX : Integrable (fun p : Ω × Space n => f (Z p) * inner ℝ (X p.1) w)
      (μ.prod (gaussianExample n)) := hf2.integrable_mul hX2
  have hiY : Integrable (fun p : Ω × Space n => f (Z p) * inner ℝ (r • p.2) w)
      (μ.prod (gaussianExample n)) := hf2.integrable_mul hY2
  have hdX : Integrable (fun p : Ω × Space n => inner ℝ (gradient f (Z p)) (T p.1))
      (μ.prod (gaussianExample n)) := integrable_inner_of_memLp_two hg2 (hT.comp_fst _)
  have hdY : Integrable (fun p : Ω × Space n => inner ℝ (gradient f (Z p)) (r ^ 2 • w))
      (μ.prod (gaussianExample n)) := integrable_inner_of_memLp_two hg2 (memLp_const _)
  have hsX : (∫ p : Ω × Space n, f (Z p) * inner ℝ (X p.1) w
      ∂μ.prod (gaussianExample n)) =
      ∫ p : Ω × Space n, inner ℝ (gradient f (Z p)) (T p.1)
        ∂μ.prod (gaussianExample n) := by
    rw [integral_prod_symm _ hiX, integral_prod_symm _ hdX]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      have ht := hstein (fun z => f (z + r • y)) (hf.comp (by fun_prop))
        (hasCompactSupport_translate hc (r • y))
      simpa only [gradient_translate (hf.differentiable (by norm_num)), Z] using ht
  have hsY : (∫ p : Ω × Space n, f (Z p) * inner ℝ (r • p.2) w
      ∂μ.prod (gaussianExample n)) =
      ∫ p : Ω × Space n, inner ℝ (gradient f (Z p)) (r ^ 2 • w)
        ∂μ.prod (gaussianExample n) := by
    rw [integral_prod _ hiY, integral_prod _ hdY]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => integral_gaussian_shift_mul_inner hf hc (X x) w r
  change (∫ p, f (Z p) * inner ℝ (X p.1 + r • p.2) w ∂μ.prod (gaussianExample n)) = _
  simp_rw [inner_add_left, mul_add, inner_add_right]
  rw [integral_add hiX hiY, integral_add hdX hdY, hsX, hsY]

/-- Exact Cauchy--Schwarz bound using the unchanged source coupling. -/
theorem integral_gaussian_additive_stein_sq_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X T : Ω → Space n}
    (hXm : Measurable X) (hX : MemLp X 2 μ) (hT : MemLp T 2 μ)
    (w : Space n)
    (hstein : ∀ h : Space n → ℝ, ContDiff ℝ 1 h → HasCompactSupport h →
      (∫ x, h (X x) * inner ℝ (X x) w ∂μ) =
        ∫ x, inner ℝ (gradient h (X x)) (T x) ∂μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (r : ℝ) :
    (∫ p : Ω × Space n, f (X p.1 + r • p.2) * inner ℝ (X p.1 + r • p.2) w
      ∂μ.prod (gaussianExample n)) ^ 2 ≤
      (∫ x, ‖T x + r ^ 2 • w‖ ^ 2 ∂μ) *
        ∫ p : Ω × Space n, ‖gradient f (X p.1 + r • p.2)‖ ^ 2
          ∂μ.prod (gaussianExample n) := by
  rw [integral_gaussian_additive_stein hXm hX hT w hstein hf hc r]
  have hg2 := memLp_compact_test_gradient_comp (μ := μ.prod (gaussianExample n)) hf hc
    (X := fun p => X p.1 + r • p.2)
    ((hXm.comp measurable_fst).add (measurable_snd.const_smul r))
  have he := integral_inner_sq_le hg2 ((hT.add (memLp_const (r ^ 2 • w))).comp_fst (gaussianExample n))
  simp only [Pi.add_apply] at he
  rw [integral_fun_fst (fun x => ‖T x + r ^ 2 • w‖ ^ 2), probReal_univ, one_smul] at he
  exact he.trans_eq (mul_comm _ _)

end KLS
end

#print axioms KLS.integral_gaussian_additive_stein
#print axioms KLS.integral_gaussian_additive_stein_sq_le
