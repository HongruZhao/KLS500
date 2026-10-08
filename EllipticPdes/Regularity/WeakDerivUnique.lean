/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.DiffQuotientBound
public import EllipticPdes.Sobolev.WeakDeriv

/-!
# Uniqueness of the whole-space weak derivative

`HasWeakDeriv k g g'` (`EllipticPdes.Regularity.DiffQuotientBound`) pins `g'` only through
its integrals against smooth compactly supported test functions. Those integrals determine
`g'` as an `L²` class, because the test classes are dense in `L²(ℝᵈ)`
(`MeasureTheory.Lp.dense_hasCompactSupport_contDiff`), so two weak `k`-derivatives of the same
class agree.

The identification steps of higher interior regularity (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1, Theorem 2) produce a second derivative twice, once as a limit
of difference quotients and once through the Leibniz rule, and need them to be the same
class. This file supplies that step.

## Main declarations

* `annihilates_of_forall_testCls`: an `L²` class orthogonal to every smooth compactly
  supported class is zero.
* `HasWeakDeriv.unique`: the weak `k`-derivative is unique as an `L²` class, an instance of
  `EllipticPdes.ae_eq_of_forall_integral_smul_eq`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Vanishing of an `L²` class orthogonal to every test class.** The classes of smooth compactly
supported functions are dense in `L²(ℝᵈ)`, and `y ↦ ⟪w, y⟫` is continuous, so a pairing that
vanishes on that family vanishes everywhere, in particular against `w` itself. -/
theorem annihilates_of_forall_testCls {w : EucL2 d}
    (hw : ∀ ρ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ →
      ∫ x, (w x : ℝ) * ρ x = 0) : w = 0 := by
  classical
  set S : Set (EucL2 d) := {y : EucL2 d | ∃ ρ : EuclideanSpace ℝ (Fin d) → ℝ,
    y =ᵐ[volume] ρ ∧ HasCompactSupport ρ ∧ ContDiff ℝ (⊤ : ℕ∞) ρ} with hS
  have hdense : Dense S :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (F := ℝ) (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (by norm_num)
  have hbase : ∀ y ∈ S, ⟪w, y⟫ = 0 := by
    rintro y ⟨ρ, hyρ, hρcs, hρcd⟩
    have hrepr : ⟪w, y⟫ = ∫ x, (w x : ℝ) * ρ x := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hyρ] with x hx
      rw [Real.inner_apply, hx]
    rw [hrepr, hw ρ hρcd hρcs]
  have hclosed : IsClosed {y : EucL2 d | ⟪w, y⟫ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hall : ∀ y : EucL2 d, ⟪w, y⟫ = 0 := by
    have hsub : closure S ⊆ {y : EucL2 d | ⟪w, y⟫ = 0} :=
      hclosed.closure_subset_iff.mpr hbase
    rw [hdense.closure_eq] at hsub
    exact fun y => hsub (Set.mem_univ y)
  exact inner_self_eq_zero.mp (hall w)

/-- **Uniqueness of the whole-space weak derivative.** Two `L²` weak `k`-derivatives of the
same class coincide, by `EllipticPdes.ae_eq_of_forall_integral_smul_eq` on the whole space. -/
theorem HasWeakDeriv.unique {k : Fin d} {g w₁ w₂ : EucL2 d}
    (h₁ : HasWeakDeriv k g w₁) (h₂ : HasWeakDeriv k g w₂) : w₁ = w₂ := by
  have hli : ∀ w : EucL2 d, LocallyIntegrableOn w Set.univ volume := fun w =>
    ((Lp.memLp w).locallyIntegrable one_le_two).locallyIntegrableOn _
  have h := ae_eq_of_forall_integral_smul_eq (Ω := ⟨Set.univ, isOpen_univ⟩) (hli w₁) (hli w₂)
    fun φ hφ hc _ => by simpa [mul_comm] using (h₁ φ hφ hc).symm.trans (h₂ φ hφ hc)
  exact Lp.ext (by simpa using h)

end EllipticPdes.Regularity
