/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Poincare.BoxSlice

/-!
# Poincaré inequality on arbitrary bounded domains (chain step 5)

`BoxSlice.lean` discharges the per-direction slice bound when the domain IS the open
coordinate box. This file removes that restriction: any `Ω` contained in a box inherits
the slice bound, because a test function of `Ω` is a test function of the box
(`IsTestFn.mono`) and the box integrals restrict to `Ω` (the integrands vanish off
`tsupport φ ⊆ Ω`). Averaging (`poincare_testfn`) and density (`poincare_H01`) are already
domain-general, so the Poincaré inequality follows on every bounded domain
(`poincare_H01_of_bounded`), with the closed-form constant `L²/(2(n+1))` from any
bounding box of side `L`. This is the `p = q = 2` Friedrichs (Poincaré) inequality
for `H₀¹`; the limit passage from test functions to `H₀¹(Ω)` by density is the
density step `poincare_H01`, which is architectural here because `H₀¹` is defined
as the closure of the test-function graphs.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace EllipticPdes.Poincare

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- Every bounded set sits inside an open coordinate box with sides bounded by a
single `L` (derived from a bounding radius about the origin). -/
theorem exists_euclBox_superset {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩb : Bornology.IsBounded Ω) :
    ∃ (a b : Fin (n + 1) → ℝ) (L : ℝ), (∀ k, a k ≤ b k) ∧ Ω ⊆ euclBox a b
      ∧ ∀ i, b i - a i ≤ L := by
  obtain ⟨R, hR⟩ := hΩb.subset_closedBall 0
  set M : ℝ := max R 0 + 1
  have hM0 : 0 < M := by
    have : (0 : ℝ) ≤ max R 0 := le_max_right R 0
    linarith
  refine ⟨fun _ => -M, fun _ => M, 2 * M, fun k => by linarith, ?_, fun i => by linarith⟩
  intro x hx
  have hxR : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hx
  intro k
  have habs : |x k| ≤ ‖x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x k
  have hlt : |x k| < M := by
    have : R ≤ max R 0 := le_max_left R 0
    linarith [le_trans habs hxR]
  exact ⟨by simpa using (abs_lt.mp hlt).1, (abs_lt.mp hlt).2⟩

/-- **Poincaré inequality on `H₀¹` of an arbitrary bounded domain** (the
Friedrichs inequality, `p = q = 2`): some constant `C ≥ 0` controls the function part
by the gradient part, uniformly over `H₀¹(Ω)`.

Guo, *Partial Differential Equations* (JHU AS.110.631-632), Theorem III.4.6 states the
`W_0^{1,p}` form, `‖u‖_{L^q} ≤ C ‖Du‖_{L^p}` for `q ∈ [1, p*]`, and derives it from the
Gagliardo-Nirenberg-Sobolev inequality. This declaration is its `p = q = 2` case, proved
on a different route and consequently in every dimension: Guo's hypothesis `p ∈ [1, n)`
reads `n > 2` at `p = 2`, excluding `n = 1` and `n = 2`, because the GNS route needs a
finite Sobolev conjugate. The route here goes through the slab Poincaré inequality
`integral_sq_le_of_tsupport_subset_slab`, which asks nothing of the dimension, with the constant
`L²/(2(n+1))` in place of the sharp one. -/
theorem poincare_H01_of_bounded {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩb : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω), U ∈ H01 Ω →
      ‖U 0‖ ^ 2 ≤ C * ∑ i : Fin (n + 1), ‖U i.succ‖ ^ 2 := by
  obtain ⟨a, b, L, hab, hsub, hL⟩ := exists_euclBox_superset hΩb
  have hL0 : 0 ≤ L := le_trans (sub_nonneg.mpr (hab 0)) (hL 0)
  exact ⟨L ^ 2 / (2 * (n + 1)), by positivity, fun U hU =>
    poincare_H01_of_subset_euclBox hab hsub hL hU⟩

/-- **Coercivity of the bilinear form of the Laplacian on a bounded domain**, with no abstract
Poincaré
hypothesis. `poincare_H01_of_bounded` names the constant, so the only input is boundedness of
`Ω`. This is the form of coercivity the direct method uses, where the domain is a ball and no
box structure is at hand. -/
theorem laplaceBilin_coercive_of_bounded {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩb : Bornology.IsBounded Ω) : IsCoercive (EllipticPdes.laplaceBilin Ω) := by
  obtain ⟨C, hC, hpoin⟩ := poincare_H01_of_bounded hΩb
  refine ⟨1 / (C + 1), by positivity, fun U => ?_⟩
  exact isCoercive_of_energy_le (H01 Ω) one_pos hC
    (fun V => by rw [EllipticPdes.laplaceBilin_self, one_mul]; rfl)
    (fun V => hpoin (V : H1amb Ω) V.2) U

end EllipticPdes.Poincare
