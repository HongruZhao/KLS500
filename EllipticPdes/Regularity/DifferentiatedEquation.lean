/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.Interior
public import EllipticPdes.Regularity.CoeffBridge
public import EllipticPdes.Regularity.LeibnizWkInfty
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Calculus of test functions and the weak Leibniz rule for a `C¹` weight

The partial derivative of a smooth compactly supported function is again smooth and compactly
supported, so `∂ⱼφ` is an admissible test function wherever `φ` is. The mixed partials of a
smooth function agree, and a class in `L²(V)` is integrable against a test function.

## Main declarations

* `contDiff_partialD`, `hasCompactSupport_partialD`, `isTest_partialD`: `∂ⱼφ` is a test
  function.
* `partialD_partialD_swap`: the mixed partials of a smooth function agree.
* `integrable_mul_testFn`: an `L²(V)` class is integrable against a test function.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Test-function calculus -/

/-- **Integrability of an `L²` class against a test function.** Hölder with the two exponents `2`
and the continuous compactly supported factor in `L²`. -/
theorem integrable_mul_testFn {V : Set (EuclideanSpace ℝ (Fin d))} (F : L2D V)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ) :
    Integrable (fun x => (F x : ℝ) * φ x) (volume.restrict V) := by
  exact (Lp.memLp F).integrable_mul
    ((hφc.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hφcs).restrict V)

/-- **Mixed-partial symmetry for smooth functions.** `∂_ℓ ∂ⱼφ = ∂ⱼ ∂_ℓφ`.

`partialD ℓ φ` is `fun y => fderiv ℝ φ y (eℓ)`, so `fderiv_clm_apply` reads its derivative off
the second Fréchet derivative, and `ContDiffAt.isSymmSndFDerivAt` swaps the two arguments. -/
lemma partialD_partialD_swap {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j ℓ : Fin d) :
    partialD ℓ (partialD j φ) = partialD j (partialD ℓ φ) := by
  have hFd : Differentiable ℝ (fderiv ℝ φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ).2).differentiable (by simp)
  have hentry : ∀ (a b : Fin d) (x : EuclideanSpace ℝ (Fin d)),
      partialD a (partialD b φ) x
        = fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    intro a b x
    have hrw : partialD b φ = fun y => (fderiv ℝ φ y) (EuclideanSpace.single b 1) := rfl
    simp only [partialD, hrw]
    rw [fderiv_clm_apply (hFd x) (differentiableAt_const _)]
    simp [ContinuousLinearMap.flip_apply]
  funext x
  rw [hentry ℓ j x, hentry j ℓ x]
  refine (hφ.contDiffAt.isSymmSndFDerivAt ?_) _ _
  simp only [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr le_top

end EllipticPdes.Regularity
