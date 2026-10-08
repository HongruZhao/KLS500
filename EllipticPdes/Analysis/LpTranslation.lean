/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import EllipticPdes.Analysis.PoincareInequality

/-!
# `L²` translation estimate

For a continuously differentiable, compactly supported `f` on a finite-dimensional real normed
space with an additive Haar measure, the `L²`
norm of the difference between `f` and its translate `f(· + h)` is controlled by
the displacement `‖h‖` and the `L²` norm of the gradient:
`∫ x, (f (x + h) - f x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2`.

This is the gradient-to-`L²` translation estimate, the equicontinuity input to the
Fréchet-Kolmogorov precompactness criterion and hence to the Rellich-Kondrachov
compact embedding.

The argument writes `f (x + h) - f x = ∫ t in 0..1, (fderiv ℝ f (x + t • h)) h`
by the fundamental theorem of calculus along the segment `t ↦ x + t • h`, squares
through the one-variable Cauchy-Schwarz bound on `[0, 1]`
(`EllipticPdes.Analysis.sq_intervalIntegral_le`), integrates over `x`, swaps the order of
integration (Tonelli, the integrand being a continuous function supported in a
bounded slab), and uses translation invariance of the Haar integral to collapse
the inner translate back to the gradient integral.

## Main results

* `EllipticPdes.Analysis.integral_sq_sub_translation_le_fderiv_apply`: the estimate along a
  direction, `∫ (f (x + h) - f x) ^ 2 ≤ ∫ (Df x h) ^ 2`.
* `EllipticPdes.Analysis.integral_sq_sub_translation_le_norm_fderiv`: the `L²` translation
  estimate.
* `EllipticPdes.Analysis.integral_sq_sub_translation_le`: its instance on `ℝⁿ`.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral Metric
open scoped ENNReal

noncomputable section

namespace EllipticPdes.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

/-- The segment path `t ↦ f (x + t • h)` has derivative `(fderiv ℝ f (x + t • h)) h`
at every `t`, for a differentiable `f`. -/
private theorem hasDerivAt_comp_segment (hf : ContDiff ℝ 1 f)
    (x h : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • h)) ((fderiv ℝ f (x + t • h)) h) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f (x + t • h)) (x + t • h) :=
    hf.differentiable_one.differentiableAt.hasFDerivAt
  exact hf'.comp_hasDerivAt t hline

/-- Continuity of the segment derivative `t ↦ (fderiv ℝ f (x + t • h)) h`. -/
private theorem continuous_segment_deriv (hf : ContDiff ℝ 1 f)
    (x h : E) :
    Continuous (fun t : ℝ => (fderiv ℝ f (x + t • h)) h) :=
  ((hf.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply continuous_const

/-- Joint continuity of `(x, t) ↦ ((fderiv ℝ f (x + t • h)) h) ^ 2`. -/
private theorem continuous_uncurry_segment (hf : ContDiff ℝ 1 f)
    (h : E) :
    Continuous (Function.uncurry fun (x : E) (t : ℝ) =>
        ((fderiv ℝ f (x + t • h)) h) ^ 2) :=
  (((hf.continuous_fderiv (by norm_num)).comp (by fun_prop : Continuous
    fun p : E × ℝ => p.1 + p.2 • h)).clm_apply continuous_const).pow 2

/-- Fundamental theorem of calculus along the segment from `x` to `x + h`. -/
private theorem sub_translation_eq_integral (hf : ContDiff ℝ 1 f)
    (x h : E) :
    f (x + h) - f x = ∫ t in (0 : ℝ)..1, (fderiv ℝ f (x + t • h)) h := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_comp_segment hf x h t)
        (continuous_segment_deriv hf x h).continuousOn.intervalIntegrable]
  simp

/-- Pointwise square estimate: `(f (x + h) - f x) ^ 2` is at most the `[0, 1]`
integral of the squared segment derivative. -/
private theorem sq_sub_translation_le (hf : ContDiff ℝ 1 f)
    (x h : E) :
    (f (x + h) - f x) ^ 2 ≤ ∫ t in (0 : ℝ)..1, ((fderiv ℝ f (x + t • h)) h) ^ 2 := by
  rw [sub_translation_eq_integral hf x h]
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have := sq_intervalIntegral_le h01
    (continuous_segment_deriv hf x h).continuousOn
  simpa using this

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] in
/-- The squared-gradient integrand `x ↦ (fderiv ℝ f x v) ^ 2` is integrable for a
`C¹` compactly supported `f`. -/
private theorem integrable_grad_apply_sq (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (v : E) :
    Integrable (fun x => ((fderiv ℝ f x) v) ^ 2) μ := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
  · exact (((hfc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L v)
      (by simp)).comp_left (g := fun r : ℝ => r ^ 2) (by simp))

omit [FiniteDimensional ℝ E] in
/-- The squared gradient norm `x ↦ ‖fderiv ℝ f x‖ ^ 2` is integrable for a `C¹`
compactly supported `f`. -/
private theorem integrable_grad_norm_sq (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hf.continuous_fderiv (by norm_num)).norm.pow 2
  · exact ((hfc.fderiv ℝ).norm.comp_left (g := fun r : ℝ => r ^ 2) (by simp))

/-- The integrand `(x, t) ↦ ((fderiv ℝ f (x + t • h)) h) ^ 2` is integrable for the
product of `μ` with the unit-interval slice: it is continuous, and for `t ∈ (0, 1]` it vanishes
off a compact slab. -/
private theorem integrable_uncurry_segment (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (h : E) :
    Integrable (Function.uncurry fun (x : E) (t : ℝ) => ((fderiv ℝ f (x + t • h)) h) ^ 2)
      (μ.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  obtain ⟨R, hR⟩ := (hfc.fderiv ℝ).isCompact.isBounded.subset_closedBall 0
  have hC : IsCompact (closedBall (0 : E) (R + ‖h‖) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  rw [← Measure.restrict_univ (μ := μ), Measure.prod_restrict, ← IntegrableOn]
  refine ((continuous_uncurry_segment hf h).locallyIntegrable.integrableOn_isCompact
    hC).of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Ioc) ?_
  rintro ⟨x, t⟩ ⟨⟨-, ht⟩, hxC⟩
  have hx : x + t • h ∉ tsupport (fderiv ℝ f) := fun hmem => hxC ⟨by
    have h1 : ‖x + t • h‖ ≤ R := by simpa using hR hmem
    have h2 : ‖t • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      exact mul_le_of_le_one_left (norm_nonneg h) ht.2
    rw [mem_closedBall_zero_iff, ← add_sub_cancel_right x (t • h)]
    exact (norm_sub_le _ _).trans (add_le_add h1 h2), Ioc_subset_Icc_self ht⟩
  simp [image_eq_zero_of_notMem_tsupport hx]

/-- **`L²` translation estimate along a direction.** For a continuously differentiable,
compactly supported `f` on a finite-dimensional space with an additive Haar measure,
`∫ (f (x + h) - f x) ^ 2 ≤ ∫ (Df x h) ^ 2`. -/
theorem integral_sq_sub_translation_le_fderiv_apply (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (h : E) :
    ∫ x, (f (x + h) - f x) ^ 2 ∂μ ≤ ∫ x, ((fderiv ℝ f x) h) ^ 2 ∂μ := by
  set F : E → ℝ → ℝ := fun x t => ((fderiv ℝ f (x + t • h)) h) ^ 2 with hF
  have hInt := integrable_uncurry_segment (μ := μ) hf hfc h
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hLHS_int : Integrable (fun x => (f (x + h) - f x) ^ 2) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hf.continuous.comp (by fun_prop)).sub hf.continuous).pow 2
    · exact (((hfc.comp_homeomorph (Homeomorph.addRight h)).sub hfc).comp_left
        (g := fun r : ℝ => r ^ 2) (by simp))
  have hRHS_int : Integrable (fun x => ∫ t in (0 : ℝ)..1, F x t) μ := by
    simp_rw [intervalIntegral.integral_of_le h01]
    exact hInt.integral_prod_left
  -- Integrate the pointwise bound, swap the integrals, and collapse each translate.
  calc ∫ x, (f (x + h) - f x) ^ 2 ∂μ
      ≤ ∫ x, (∫ t in (0 : ℝ)..1, F x t) ∂μ :=
        integral_mono hLHS_int hRHS_int fun x => sq_sub_translation_le hf x h
    _ = ∫ t in (0 : ℝ)..1, (∫ x, F x t ∂μ) := by
        simp_rw [intervalIntegral.integral_of_le h01]
        exact integral_integral_swap hInt
    _ = ∫ x, ((fderiv ℝ f x) h) ^ 2 ∂μ := by
        simp [hF, integral_add_right_eq_self (μ := μ) (fun x => ((fderiv ℝ f x) h) ^ 2)]

/-- **`L²` translation estimate.** For a continuously differentiable, compactly supported `f`
on a finite-dimensional space with an additive Haar measure,
`∫ (f (x + h) - f x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ ‖Df x‖ ^ 2`. -/
theorem integral_sq_sub_translation_le_norm_fderiv (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (h : E) :
    ∫ x, (f (x + h) - f x) ^ 2 ∂μ ≤ ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  refine (integral_sq_sub_translation_le_fderiv_apply hf hfc h).trans ?_
  rw [← MeasureTheory.integral_const_mul]
  refine integral_mono (integrable_grad_apply_sq hf hfc h)
    ((integrable_grad_norm_sq hf hfc).const_mul _) fun x => ?_
  calc ((fderiv ℝ f x) h) ^ 2 = ‖(fderiv ℝ f x) h‖ ^ 2 := (sq_abs _).symm
    _ ≤ (‖fderiv ℝ f x‖ * ‖h‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ((fderiv ℝ f x).le_opNorm h) 2
    _ = ‖h‖ ^ 2 * ‖fderiv ℝ f x‖ ^ 2 := by ring

/-- **`L²` translation estimate on `ℝⁿ`.** For a continuously differentiable, compactly
supported `f : ℝⁿ → ℝ`, `∫ x, (f (x + h) - f x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2`. -/
theorem integral_sq_sub_translation_le {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (h : EuclideanSpace ℝ (Fin n)) :
    ∫ x, (f (x + h) - f x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 :=
  integral_sq_sub_translation_le_norm_fderiv hf hfc h

end EllipticPdes.Analysis

/-- Alias for backward compatibility. -/
alias MeasureTheory.integral_sq_sub_translation_le :=
  EllipticPdes.Analysis.integral_sq_sub_translation_le
