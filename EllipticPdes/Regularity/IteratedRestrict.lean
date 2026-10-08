/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.HigherWeakDeriv

/-!
# Iterated weak derivatives pass to a smaller region

The induction of Guo, *Partial Differential Equations I and II* (Course Lecture Notes),
Theorem VIII.3.2 (p. 65) runs on a pair `V ⋐ W ⋐ Ω`: the cutoff lives on `W`, the conclusion
is asked on `V`, and the datum's regularity is established on whichever of the two is
convenient. Moving a family between them is the bookkeeping this file removes.

A weak derivative on `W` is tested against every test function supported in `W`, and a test
function supported in `V ⊆ W` is one of them. Both integrals then localise to `V`, since the
integrands vanish off the support. The bound comes along because extension by zero preserves
the norm and restriction does not increase it.

## Main declarations

* `HasWeakDerivOn.restrict`: a weak derivative on `W` restricts to one on `V ⊆ W`.
* `HasIteratedWeakDerivOn.restrict`: the family.
* `IteratedL2Bound.restrict`: the bound, with the same constant.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {W V : Set (EuclideanSpace ℝ (Fin d))} {k : ℕ} {ℓ : Fin d}

/-- **Restriction of a weak derivative to a smaller region.** Test functions supported in `V` are
test functions supported in `W`, and each integral over `W` collapses to one over `V` because
its integrand vanishes off the support. -/
theorem HasWeakDerivOn.restrict (hWm : MeasurableSet W) (hVm : MeasurableSet V) (hVW : V ⊆ W)
    {g g' : L2D W} (h : HasWeakDerivOn W ℓ g g') :
    HasWeakDerivOn V ℓ (restrictL2 (Ω := V) (extendL2 hWm g))
      (restrictL2 (Ω := V) (extendL2 hWm g')) := by
  intro φ hφc hφcs hφV
  have e1 := setIntegral_mul_restrictL2_extendL2 hWm hVm hVW g (fun _ => 1) (partialD ℓ φ)
    fun x hx => image_eq_zero_of_notMem_tsupport
      fun hc => hx (hφV (tsupport_partialD_subset ℓ φ hc))
  have e2 := setIntegral_mul_restrictL2_extendL2 hWm hVm hVW g' (fun _ => 1) φ
    fun x hx => image_eq_zero_of_notMem_tsupport fun hc => hx (hφV hc)
  simp only [one_mul] at e1 e2
  rw [← e1, ← e2]
  exact h φ hφc hφcs (hφV.trans hVW)

/-- The order-`k` family on a smaller region, entry by entry. -/
def HasIteratedWeakDerivOn.restrict (hWm : MeasurableSet W) (hVm : MeasurableSet V)
    (hVW : V ⊆ W) {g : L2D W} (hg : HasIteratedWeakDerivOn W k g) :
    HasIteratedWeakDerivOn V k (restrictL2 (Ω := V) (extendL2 hWm g)) where
  D α := restrictL2 (Ω := V) (extendL2 hWm (hg.D α))
  D_nil := by rw [hg.D_nil]
  D_step m α hα := (hg.D_step m α hα).restrict hWm hVm hVW

/-- The restricted family has the same bound: extension by zero preserves the norm and
restriction does not increase it. -/
theorem IteratedL2Bound.restrict {hWm : MeasurableSet W} {hVm : MeasurableSet V} {hVW : V ⊆ W}
    {g : L2D W} {hg : HasIteratedWeakDerivOn W k g} {C : ℝ} (hC : IteratedL2Bound hg C) :
    IteratedL2Bound (hg.restrict hWm hVm hVW) C := by
  intro α hα
  refine le_trans (norm_restrictL2_le _) ?_
  rw [norm_extendL2]
  exact hC α hα

end EllipticPdes.Regularity
