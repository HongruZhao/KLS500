/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Poincare.Domain
public import EllipticPdes.Sobolev.Basic

/-!
# Density extension to H₀¹ (dependency-chain step 4)

The Poincaré inequality, once established for every smooth compactly supported test
function, extends to all of `H₀¹(Ω)` by density. The key structural facts (proved in
`Sobolev/Basic.lean`) are that the test-function graphs already form a submodule
(`span_testGraphSet`) and that `H₀¹(Ω)` is their topological closure. The Poincaré
estimate is the condition `0 ≤ Φ` for a continuous function `Φ`, hence a closed
condition; holding on the dense test functions, it passes to the closure.

The base estimate on test functions is taken as a hypothesis here (it is supplied by the
domain Poincaré inequality `poincare_domain` rewritten through the `L²` norms). This keeps
the density mechanism independent of the geometry of `Ω`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace EllipticPdes.Poincare

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- **Density Poincaré inequality on `H₀¹`.** If the Poincaré bound
`‖φ‖²_{L²} ≤ C · ∑ᵢ ‖∂ᵢφ‖²_{L²}` holds for every test function `φ` (phrased through the
graph coordinates `testGraph 0` and `testGraph i.succ`), then it holds for every element
of `H₀¹(Ω)`: the function part `U 0` is controlled by the gradient part `U ∘ Fin.succ`. -/
theorem poincare_H01 {Ω : Set (EuclideanSpace ℝ (Fin d))} (C : ℝ)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ C * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    ‖U 0‖ ^ 2 ≤ C * ∑ i : Fin d, ‖U i.succ‖ ^ 2 := by
  have hclosed : IsClosed {V : H1amb Ω | ‖V 0‖ ^ 2 ≤ C * ∑ i : Fin d, ‖V i.succ‖ ^ 2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact H01_subset_of_isClosed hclosed (fun φ h => by simpa using hbase h) hU

/-- **Coercivity from an energy bound and a Poincaré bound.** If a bilinear form on a closed
subspace `S` of `H¹` dominates `lam` times the Dirichlet energy and the function part is bounded
by `CP` times the energy, then the form dominates the full `H¹` norm with constant
`lam / (CP + 1)`. -/
theorem isCoercive_of_energy_le {Ω : Set (EuclideanSpace ℝ (Fin d))} (S : Submodule ℝ (H1amb Ω))
    {B : S →L[ℝ] S →L[ℝ] ℝ} {lam CP : ℝ} (hlam : 0 < lam) (hCP : 0 ≤ CP)
    (hE : ∀ U : S, lam * ∑ i, ‖(U : H1amb Ω).grad i‖ ^ 2 ≤ B U U)
    (hP : ∀ U : S, ‖(U : H1amb Ω).fn‖ ^ 2 ≤ CP * ∑ i, ‖(U : H1amb Ω).grad i‖ ^ 2)
    (U : S) : lam / (CP + 1) * ‖U‖ * ‖U‖ ≤ B U U := by
  have hpos : 0 < CP + 1 := by linarith
  have hkey : ‖U‖ * ‖U‖ ≤ (CP + 1) * ∑ i, ‖(U : H1amb Ω).grad i‖ ^ 2 := by
    have hn : ‖U‖ ^ 2 = ‖(U : H1amb Ω).fn‖ ^ 2 + ∑ i, ‖(U : H1amb Ω).grad i‖ ^ 2 :=
      H1amb.norm_sq_eq (U : H1amb Ω)
    linarith [hP U, sq ‖U‖]
  calc lam / (CP + 1) * ‖U‖ * ‖U‖
      = lam / (CP + 1) * (‖U‖ * ‖U‖) := by ring
    _ ≤ lam / (CP + 1) * ((CP + 1) * ∑ i, ‖(U : H1amb Ω).grad i‖ ^ 2) := by gcongr
    _ = lam * ∑ i, ‖(U : H1amb Ω).grad i‖ ^ 2 := by field_simp
    _ ≤ B U U := hE U

end EllipticPdes.Poincare
