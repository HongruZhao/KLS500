/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.LowerOrderWkInfty
public import EllipticPdes.Regularity.CutoffTower
public import EllipticPdes.Regularity.Caccioppoli

/-!
# Cutting a locally smooth function off to a globally smooth one

The interior-regularity chain runs on a `FullEllipticOp`, whose coefficients are global on
`EuclideanSpace ℝ (Fin d)`, essentially bounded, and asked for no more. A datum smooth on an
open set `U` alone, or coefficients smooth on `U` alone with no bound off it, do not meet that
shape directly. Multiplying by a smooth cutoff supported in `U` and equal to `1` near the region
of interest repairs this: the product is globally smooth, compactly supported, and so lies in
`W^{k,∞}` at every order, with no bound needed on the factor itself.

This file supplies that cutting-off step in general, for a single scalar function; `LocalOp`
applies it entrywise to build a global operator out of one with coefficients smooth on `U` alone.

## Main declarations

* `contDiff_mul_of_contDiffOn`: a function of class `C^n` on `U`, cut off by a test function of
  `U`, is globally of class `C^n`.
* `hasCompactSupport_mul`: the product has compact support.
* `exists_iteratedFDeriv_bound`: a compactly supported function of class `C^m` has every iterated
  derivative of order at most `m` uniformly bounded.
* `exists_iteratedFDeriv_bound_const_add`: the same for a constant shift of one, at every
  positive order.
* `nonempty_isWkInfty`: a compactly supported function of class `C^m` lies in `W^{k,∞}` for
  `k ≤ m`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A function of class `C^n` on an open `U`, multiplied by a test function supported in `U`, is
of class `C^n` on the whole space: away from the topological support of the cutoff the product is
eventually zero, and on that support the cutoff is smooth and `g` is of class `C^n` near the
point, since the support sits inside `U`. -/
theorem contDiff_mul_of_contDiffOn {U : Set E} (hU : IsOpen U) {χ g : E → ℝ}
    (hχ : IsTestFn U χ) {n : ℕ∞} (hg : ContDiffOn ℝ n g U) :
    ContDiff ℝ n (fun x => χ x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact ((hχ.1.of_le (by exact_mod_cast le_top)).contDiffAt).mul
      (hg.contDiffAt (hU.mem_nhds (hχ.2.2 hx)))
  · have h0 : χ =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).1 hx
    have h1 : (fun y => χ y * g y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [h0] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h1

/-- The product of a test function with any function has compact support: the topological
support of the product sits inside that of the cutoff. -/
theorem hasCompactSupport_mul {U : Set E} {χ g : E → ℝ} (hχ : IsTestFn U χ) :
    HasCompactSupport (fun x => χ x * g x) :=
  hχ.2.1.mul_right (f' := g)

/-- A compactly supported function of class `C^m` has every iterated derivative of order at
most `m` bounded, with a nonnegative bound at each order. -/
theorem exists_iteratedFDeriv_bound {g : E → ℝ} {m : ℕ∞} (hg : ContDiff ℝ m g)
    (hc : HasCompactSupport g) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧ ∀ j : ℕ, (j : ℕ∞) ≤ m → ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B j := by
  have h : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ((j : ℕ∞) ≤ m → ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C) := by
    intro j
    by_cases hj : (j : ℕ∞) ≤ m
    · obtain ⟨C, hC⟩ := (hc.iteratedFDeriv j).exists_bound_of_continuous
        (hg.continuous_iteratedFDeriv (by exact_mod_cast hj))
      exact ⟨C, (norm_nonneg _).trans (hC 0), fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose B hB0 hB using h
  exact ⟨B, hB0, fun j hj => hB j hj⟩

/-- A constant plus a compactly supported function of class `C^m` has every iterated derivative
of order between `1` and `m` bounded: the constant contributes nothing past order zero. -/
theorem exists_iteratedFDeriv_bound_const_add {g : E → ℝ} {m : ℕ∞} (hg : ContDiff ℝ m g)
    (hc : HasCompactSupport g) (c : ℝ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧ ∀ j : ℕ, 1 ≤ j → (j : ℕ∞) ≤ m → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => c + g y) x‖ ≤ B j := by
  obtain ⟨B, hB0, hB⟩ := exists_iteratedFDeriv_bound hg hc
  refine ⟨B, hB0, fun j hj hjm x => ?_⟩
  have hadd : iteratedFDeriv ℝ j (fun y => c + g y) x
      = iteratedFDeriv ℝ j (fun _ : E => c) x + iteratedFDeriv ℝ j g x :=
    iteratedFDeriv_add_apply contDiffAt_const ((hg.of_le (by exact_mod_cast hjm)).contDiffAt)
  rw [hadd, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add]
  exact hB j hjm x

/-- A compactly supported function of class `C^m` lies in `W^{k,∞}` for every `k ≤ m`: its
classical iterated partials serve as the weak-derivative family, and
`exists_iteratedFDeriv_bound` supplies the uniform bound each order needs. -/
theorem nonempty_isWkInfty {g : E → ℝ} {m : ℕ∞} {k : ℕ} (hk : (k : ℕ∞) ≤ m)
    (hg : ContDiff ℝ m g) (hc : HasCompactSupport g) : Nonempty (IsWkInfty g k) := by
  obtain ⟨B, hB0, hB⟩ := exists_iteratedFDeriv_bound hg hc
  exact ⟨IsWkInfty.ofContDiff (hg.of_le (by exact_mod_cast hk)) hB0
    (fun j hj x => hB j ((by exact_mod_cast hj : (j : ℕ∞) ≤ k).trans hk) x)⟩

/-- A family of continuous compactly supported functions is bounded in absolute value by the sum
of the suprema of the absolute values. -/
theorem abs_le_sum_iSup_abs {ι : Type*} [Fintype ι] {f : ι → E → ℝ}
    (hc : ∀ i, Continuous (f i)) (hs : ∀ i, HasCompactSupport (f i)) (i : ι) (x : E) :
    |f i x| ≤ ∑ j, ⨆ y, |f j y| :=
  ((hs i).abs_le_iSup_abs (hc i) x).trans
    (Finset.single_le_sum (f := fun j => ⨆ y, |f j y|)
      (fun j _ => (hs j).iSup_abs_nonneg (hc j)) (Finset.mem_univ i))

end EllipticPdes.Regularity
