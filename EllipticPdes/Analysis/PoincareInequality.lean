/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import EllipticPdes.Sobolev.Basic

/-!
# One-dimensional Poincaré inequality

For a continuously differentiable `u` on a compact interval `[a, b]` that
vanishes at the left endpoint, the `L²` norm of `u` is controlled by the `L²`
norm of its derivative:
`∫ x in a..b, (u x) ^ 2 ≤ (b - a) ^ 2 / 2 * ∫ x in a..b, (u' x) ^ 2`.

The argument has three steps. First, `intervalIntegral_mul_sq_le` is the
Cauchy-Schwarz inequality for the interval integral, obtained from the
inner product of `L²`. Second, the fundamental theorem of
calculus writes `u x` as `∫ t in a..x, u' t`, which the Cauchy-Schwarz bound
(with `g = 1`, `sq_intervalIntegral_le`) turns into the pointwise estimate
`(u x) ^ 2 ≤ M * (x - a)` with `M = ∫ t in a..b, (u' t) ^ 2`. Third,
integrating that estimate over `[a, b]` and evaluating
`∫ x in a..b, (x - a) = (b - a) ^ 2 / 2` gives the constant.

## Main results

* `EllipticPdes.Analysis.sq_integral_mul_le`: Cauchy-Schwarz for `∫ f g` in `L²`.
* `EllipticPdes.Analysis.sq_setIntegral_le_measureReal_mul`: the case `g = 1` on a set.
* `EllipticPdes.Analysis.intervalIntegral_mul_sq_le` and `sq_intervalIntegral_le`: the interval
  forms.
* `EllipticPdes.Analysis.poincare_1d`: the one-dimensional Poincaré inequality.
-/

@[expose] public section

open MeasureTheory intervalIntegral Set
open scoped RealInnerProductSpace

namespace EllipticPdes.Analysis

section CauchySchwarz

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}

/-- Cauchy-Schwarz for the integral of a product of two square-integrable functions. -/
theorem sq_integral_mul_le (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [L2.real_inner_eq_integral, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    L2.norm_sq_eq_integral_sq, L2.norm_sq_eq_integral_sq] at h
  have hfg : ∫ x, hf.toLp f x * hg.toLp g x ∂μ = ∫ x, f x * g x ∂μ :=
    integral_congr_ae (by filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy; rw [hx, hy])
  have hff : ∫ x, hf.toLp f x ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ :=
    integral_congr_ae (by filter_upwards [hf.coeFn_toLp] with x hx; rw [hx])
  have hgg : ∫ x, hg.toLp g x ^ 2 ∂μ = ∫ x, g x ^ 2 ∂μ :=
    integral_congr_ae (by filter_upwards [hg.coeFn_toLp] with x hx; rw [hx])
  rw [hfg, hff, hgg] at h
  nlinarith [h]

/-- **Finite-measure Cauchy-Schwarz with one constant factor.** The square of the integral of a
square-integrable `f` over a set of finite measure is at most the measure of the set times the
integral of `f ^ 2`. -/
theorem sq_setIntegral_le_measureReal_mul {s : Set α} (hμs : μ s ≠ ⊤)
    (hf : MemLp f 2 (μ.restrict s)) :
    (∫ x in s, f x ∂μ) ^ 2 ≤ μ.real s * ∫ x in s, f x ^ 2 ∂μ := by
  have : IsFiniteMeasure (μ.restrict s) := ⟨by simpa [lt_top_iff_ne_top] using hμs⟩
  have h := sq_integral_mul_le hf (memLp_const (1 : ℝ) : MemLp (fun _ => (1 : ℝ)) 2 (μ.restrict s))
  simpa [mul_comm, Measure.real, mul_one, one_pow] using h

end CauchySchwarz

/-- Cauchy-Schwarz for the interval integral: the square of `∫ f g` is at most
the product of `∫ f ^ 2` and `∫ g ^ 2`. -/
theorem intervalIntegral_mul_sq_le {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (uIcc a b)) (hg : ContinuousOn g (uIcc a b)) :
    (∫ t in a..b, f t * g t) ^ 2 ≤ (∫ t in a..b, (f t) ^ 2) * ∫ t in a..b, (g t) ^ 2 := by
  have hmem : ∀ {u : ℝ → ℝ}, ContinuousOn u (uIcc a b) → MemLp u 2 (volume.restrict (Ioc a b)) :=
    fun hu => (memLp_two_iff_integrable_sq
      (hu.mono (by rw [uIcc_of_le hab]; exact Ioc_subset_Icc_self) |>.aestronglyMeasurable
        measurableSet_Ioc)).2
      (((hu.pow 2).intervalIntegrable (a := a) (b := b)).1)
  simp only [intervalIntegral.integral_of_le hab]
  exact sq_integral_mul_le (hmem hf) (hmem hg)

/-- Cauchy-Schwarz with one factor constant: on `[a, x]` the square of the
integral of `f` is at most `(x - a)` times the integral of `f ^ 2`. The `g = 1`
case of `intervalIntegral_mul_sq_le`. -/
theorem sq_intervalIntegral_le {a x : ℝ} (hax : a ≤ x) {f : ℝ → ℝ}
    (hf : ContinuousOn f (uIcc a x)) :
    (∫ t in a..x, f t) ^ 2 ≤ (x - a) * ∫ t in a..x, (f t) ^ 2 := by
  have h := intervalIntegral_mul_sq_le hax hf (continuousOn_const (c := (1 : ℝ)))
  simp only [mul_one, one_pow] at h
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, mul_comm] at h
  exact h

/-- **One-dimensional Poincaré inequality.** If `u` has derivative `u'` at
every point of `[a, b]` with `u'` continuous there, and `u a = 0`, then
`∫ x in a..b, (u x) ^ 2 ≤ (b - a) ^ 2 / 2 * ∫ x in a..b, (u' x) ^ 2`.

A function compactly supported in `(a, b)` satisfies `u a = 0`, so this applies
to each one-dimensional slice in the Fubini proof of the Poincaré inequality on
a box, with constant `(b - a) ^ 2 / 2`. -/
theorem poincare_1d {a b : ℝ} (hab : a ≤ b) {u u' : ℝ → ℝ}
    (hderiv : ∀ y ∈ uIcc a b, HasDerivAt u (u' y) y)
    (hu' : ContinuousOn u' (uIcc a b)) (ha : u a = 0) :
    ∫ x in a..b, (u x) ^ 2 ≤ (b - a) ^ 2 / 2 * ∫ x in a..b, (u' x) ^ 2 := by
  set M : ℝ := ∫ x in a..b, (u' x) ^ 2 with hM
  have hu'2 : ContinuousOn (fun t => (u' t) ^ 2) (uIcc a b) := hu'.pow 2
  have hu_cont : ContinuousOn u (uIcc a b) :=
    fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
  -- Pointwise estimate from FTC and the Cauchy-Schwarz bound.
  have pointwise : ∀ x ∈ Icc a b, (u x) ^ 2 ≤ M * (x - a) := by
    intro x hx
    obtain ⟨hax, hxb⟩ := hx
    have hsub : uIcc a x ⊆ uIcc a b := by
      rw [uIcc_of_le hax, uIcc_of_le hab]; exact Icc_subset_Icc_right hxb
    have hsubxb : uIcc x b ⊆ uIcc a b := by
      rw [uIcc_of_le hxb, uIcc_of_le hab]; exact Icc_subset_Icc_left hax
    -- `u x = ∫ t in a..x, u' t` by the fundamental theorem of calculus.
    have hux : u x = ∫ t in a..x, u' t := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hderiv t (hsub ht))
        ((hu'.mono hsub).intervalIntegrable), ha, sub_zero]
    have hcs : (∫ t in a..x, u' t) ^ 2 ≤ (x - a) * ∫ t in a..x, (u' t) ^ 2 :=
      sq_intervalIntegral_le hax (hu'.mono hsub)
    -- `∫ t in a..x, (u')² ≤ M` since the integrand is nonnegative.
    have hmono : ∫ t in a..x, (u' t) ^ 2 ≤ M := by
      have hI1 : IntervalIntegrable (fun t => (u' t) ^ 2) volume a x :=
        (hu'2.mono hsub).intervalIntegrable
      have hI2 : IntervalIntegrable (fun t => (u' t) ^ 2) volume x b :=
        (hu'2.mono hsubxb).intervalIntegrable
      have hadj := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
      have hxbnn : 0 ≤ ∫ t in x..b, (u' t) ^ 2 :=
        intervalIntegral.integral_nonneg hxb (fun t _ => by positivity)
      rw [hM]; linarith [hadj, hxbnn]
    calc (u x) ^ 2 = (∫ t in a..x, u' t) ^ 2 := by rw [hux]
      _ ≤ (x - a) * ∫ t in a..x, (u' t) ^ 2 := hcs
      _ ≤ (x - a) * M := mul_le_mul_of_nonneg_left hmono (by linarith)
      _ = M * (x - a) := by ring
  -- Integrate the pointwise estimate over `[a, b]`.
  have hfint : IntervalIntegrable (fun x => (u x) ^ 2) volume a b :=
    (hu_cont.pow 2).intervalIntegrable
  have hgint : IntervalIntegrable (fun x => M * (x - a)) volume a b :=
    (by fun_prop : Continuous fun x : ℝ => M * (x - a)).intervalIntegrable a b
  have hmain : ∫ x in a..b, (u x) ^ 2 ≤ ∫ x in a..b, M * (x - a) :=
    intervalIntegral.integral_mono_on hab hfint hgint pointwise
  -- `∫ x in a..b, (x - a) = (b - a) ^ 2 / 2`.
  have hxa : ∫ x in a..b, (x - a) = (b - a) ^ 2 / 2 := by
    have hd : ∀ y ∈ uIcc a b, HasDerivAt (fun z => (z - a) ^ 2 / 2) (y - a) y := by
      intro y _
      have hg : HasDerivAt (fun z : ℝ => z - a) 1 y := (hasDerivAt_id y).sub_const a
      have h2 := (hg.pow 2).div_const 2
      convert h2 using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun x : ℝ => x - a).intervalIntegrable a b)]
    simp
  calc ∫ x in a..b, (u x) ^ 2 ≤ ∫ x in a..b, M * (x - a) := hmain
    _ = M * ∫ x in a..b, (x - a) := by rw [intervalIntegral.integral_const_mul]
    _ = M * ((b - a) ^ 2 / 2) := by rw [hxa]
    _ = (b - a) ^ 2 / 2 * M := by ring

end EllipticPdes.Analysis

/-- Alias for backward compatibility. -/
alias MeasureTheory.sq_intervalIntegral_le := EllipticPdes.Analysis.sq_intervalIntegral_le
