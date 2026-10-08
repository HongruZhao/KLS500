/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.LpTranslation

/-!
# Poincaré inequality on a slab

Let `ℓ` be a continuous linear functional on a finite-dimensional real normed space and `v` a
vector with `ℓ v = 1`. A `C¹` function `f` with compact support in the slab `a < ℓ x < b`
satisfies

  `∫ f² ≤ (b - a)² / 2 · ∫ (Df · v)²`

for any additive Haar measure. The translate of `f` by `(b - a) • v` has support disjoint from
that of `f`, so `∫ (f (· + h) - f)² = 2 ∫ f²`, and the directional `L²` translation estimate
`EllipticPdes.Analysis.integral_sq_sub_translation_le_fderiv_apply` bounds the left side by
`(b - a)² ∫ (Df · v)²`. No coordinates and no Fubini decomposition are used.

## Main declarations

* `EllipticPdes.Poincare.integral_sq_le_of_tsupport_subset_slab`: the slab inequality.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace EllipticPdes.Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → ℝ}

/-- **Poincaré inequality on a slab.** If `ℓ v = 1` and the `C¹` function `f` has compact
support in the slab `a < ℓ x < b`, then `∫ f² ≤ (b - a)² / 2 · ∫ (Df · v)²`. -/
theorem integral_sq_le_of_tsupport_subset_slab (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (ℓ : E →L[ℝ] ℝ) {v : E} (hv : ℓ v = 1) {a b : ℝ}
    (hs : tsupport f ⊆ ℓ ⁻¹' Ioo a b) :
    ∫ x, f x ^ 2 ∂μ ≤ (b - a) ^ 2 / 2 * ∫ x, (fderiv ℝ f x v) ^ 2 ∂μ := by
  set h : E := (b - a) • v
  -- The translate by `h` and `f` itself have disjoint supports.
  have hdisj : ∀ x, f (x + h) * f x = 0 := fun x => by
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
    have hx : ℓ x ∈ Ioo a b := hs (subset_tsupport f h2)
    have hxh : ℓ (x + h) ∈ Ioo a b := hs (subset_tsupport f h1)
    simp only [h, map_add, map_smul, hv, smul_eq_mul, mul_one, mem_Ioo] at hx hxh
    linarith [hx.1, hxh.2]
  have hsq : Integrable (fun x => f x ^ 2) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hf.continuous.pow 2
    · exact hfc.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have htr := Analysis.integral_sq_sub_translation_le_fderiv_apply (μ := μ) hf hfc h
  have hpt : ∀ x, (f (x + h) - f x) ^ 2 = f (x + h) ^ 2 + f x ^ 2 := fun x => by
    linear_combination (-2 : ℝ) * hdisj x
  simp_rw [hpt, h, map_smul, smul_eq_mul, mul_pow] at htr
  rw [integral_add (hsq.comp_add_right _) hsq, integral_add_right_eq_self (fun x => f x ^ 2),
    integral_const_mul] at htr
  linarith

end EllipticPdes.Poincare
