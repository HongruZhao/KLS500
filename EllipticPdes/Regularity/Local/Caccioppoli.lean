/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.Local.WeakSolution

/-!
# Caccioppoli estimate for a weak solution in `H¹`

`caccioppoli_W12` bounds the cutoff-weighted energy of a weak solution in `H¹` by
`‖f‖² + ‖u‖²`. Its proof tests the equation with `ζ² u`, and that test function is admissible
for a local weak solution `U ∈ W12 Ω` as well (`cutoffMul_mem_H01_of_mem_W12`), with the
identity against it supplied by `IsLocalWeakSolution.weakForm`. The proof uses no boundary
condition, so the statement holds for `W12` solutions with the same constant
(`caccioppoli_core`).

This is the step Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 1 takes in
the proof before (8) to replace `‖u‖_{H¹(U)}` by `‖u‖_{L²(U)}` on the right of the estimate.

## Main declarations

* `caccioppoli_W12`: the energy estimate.
* `exists_norm_mulTest_grad_le`: its consequence for each gradient coordinate, with the norms
  unsquared.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- **Caccioppoli estimate for a weak solution in `H¹`.** For a local weak solution
`U ∈ W12 Ω` of `L U = f` on an open `Ω`, with no boundary condition, and a test function `ζ` of
`Ω`, the cutoff-weighted gradient energy `(λ/2) Σ ‖ζ ∂_i U‖²` is bounded by
`C (‖f‖² + ‖U₀‖²)`, with `C` quantified before the solution and the datum. It is
`caccioppoli_core` with the identity of `IsLocalWeakSolution.weakForm` against `ζ² U`. -/
theorem caccioppoli_W12 (Op : FullEllipticOp d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩo : IsOpen Ω) {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω) (f : L2D Ω), IsLocalWeakSolution Op Ω U f →
      Op.lam / 2 * ∑ i : Fin d, ‖mulTest hζ (U i.succ)‖ ^ 2
        ≤ C * (‖f‖ ^ 2 + ‖U 0‖ ^ 2) := by
  obtain ⟨C, hC, h⟩ := caccioppoli_core Op hζ
  refine ⟨C, hC, fun U f hsol => h U f ?_⟩
  have hmem := cutoffMul_mem_H01_of_mem_W12 hΩo (isTestFn_mul hζ hζ) hsol.1
  have := hsol.weakForm hmem
  rwa [pairL_apply] at this

/-- A term of a sum of squares, from a bound on the weighted sum, with the square root
taken. -/
theorem le_sqrt_mul_of_sum_sq_le {ι : Type*} [Fintype ι] (g : ι → ℝ) (hg : ∀ j, 0 ≤ g j)
    {lam C0 a b : ℝ} (hlam : 0 < lam) (hC0 : 0 ≤ C0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : lam / 2 * ∑ j, g j ^ 2 ≤ C0 * (a ^ 2 + b ^ 2)) (i : ι) :
    g i ≤ Real.sqrt (2 * C0 / lam) * (a + b) := by
  have hC'0 : 0 ≤ 2 * C0 / lam := div_nonneg (by linarith) hlam.le
  have hsum : ∑ j, g j ^ 2 ≤ 2 * C0 / lam * (a ^ 2 + b ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    linarith [h]
  have hi : g i ^ 2 ≤ ∑ j, g j ^ 2 :=
    Finset.single_le_sum (f := fun j => g j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by nlinarith
  have hkey : g i ^ 2 ≤ (Real.sqrt (2 * C0 / lam) * (a + b)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC'0]
    exact hi.trans (hsum.trans (mul_le_mul_of_nonneg_left hsq hC'0))
  have h1 := Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_sq (hg i),
    Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg ha hb))] at h1

/-- **Cutoff gradient bounded by the function and the datum.** Each gradient coordinate of a
local weak solution, cut off by a test function `ζ`, is bounded in `L²(Ω)` by
`C (‖f‖ + ‖U₀‖)`: the square root of `caccioppoli_W12`. -/
theorem exists_norm_mulTest_grad_le (Op : FullEllipticOp d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩo : IsOpen Ω) {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω) (f : L2D Ω), IsLocalWeakSolution Op Ω U f →
      ∀ i : Fin d, ‖mulTest hζ (U i.succ)‖ ≤ C * (‖f‖ + ‖U 0‖) := by
  obtain ⟨C0, hC0, h⟩ := caccioppoli_W12 Op hΩo hζ
  exact ⟨_, Real.sqrt_nonneg _, fun U f hsol i =>
    le_sqrt_mul_of_sum_sq_le (fun j : Fin d => ‖mulTest hζ (U j.succ)‖) (fun _ => norm_nonneg _)
      Op.lam_pos hC0 (norm_nonneg f) (norm_nonneg (U 0)) (h U f hsol) i⟩

end EllipticPdes.Regularity
