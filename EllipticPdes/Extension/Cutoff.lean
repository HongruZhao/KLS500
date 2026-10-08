/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A one-sided cutoff along a linear functional

The extension by reflection is proved by testing strictly inside the half space and letting the
excluded slab shrink. The cutoff that excludes it is a function of one linear functional `ℓ`:
`slabCut ℓ ε` vanishes where `ℓ x ≤ ε` and is `1` where `ℓ x ≥ 2ε`, so a test function
multiplied by it is supported in the open half space `{0 < ℓ}`.

Its derivative along `w` is `ℓ w / ε` times a bounded profile supported where `ε < ℓ x ≤ 2ε`.
A direction that `ℓ` annihilates therefore leaves no boundary term, and the remaining one is
bounded by `C/ε` on a slab that shrinks to nothing.

## Main declarations

* `EllipticPdes.Extension.slabCut`: the cutoff.
* `EllipticPdes.Extension.slabCut_eq_zero`, `EllipticPdes.Extension.slabCut_eq_one`: its values
  on the slab and beyond it.
* `EllipticPdes.Extension.fderiv_slabCut`: its derivative.
* `EllipticPdes.Extension.abs_fderiv_slabCut_le`: the `C/ε` bound.
-/

@[expose] public section

open Filter Topology Set

noncomputable section

namespace EllipticPdes.Extension

/-- The derivative of the smooth transition profile vanishes off `[0, 1]`. -/
theorem deriv_smoothTransition_eq_zero {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition t = 0 := by
  rcases not_and_or.1 ht with h | h
  · have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [gt_mem_nhds (not_le.1 h)] with s hs using
        Real.smoothTransition.zero_of_nonpos hs.le
    rw [hev.deriv_eq, deriv_const]
  · have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [lt_mem_nhds (not_le.1 h)] with s hs using
        Real.smoothTransition.one_of_one_le hs.le
    rw [hev.deriv_eq, deriv_const]

/-- The smooth transition profile is smooth. -/
theorem contDiff_smoothTransition : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
  Real.smoothTransition.contDiff

/-- The derivative of the smooth transition profile is bounded. -/
theorem exists_bound_deriv_smoothTransition :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv Real.smoothTransition t| ≤ C := by
  have hcs : HasCompactSupport (deriv Real.smoothTransition) :=
    HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun t ht =>
      deriv_smoothTransition_eq_zero ht
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous
    (contDiff_smoothTransition.continuous_deriv (by exact_mod_cast le_top))
  exact ⟨C, (abs_nonneg _).trans (by simpa using hC 0), fun t => by simpa using hC t⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Cutoff excluding the slab `ℓ x ≤ ε`.** It depends on `x` through `ℓ x` alone. -/
def slabCut (ℓ : E →L[ℝ] ℝ) (ε : ℝ) (x : E) : ℝ := Real.smoothTransition (ℓ x / ε - 1)

/-- `slabCut ℓ ε` is smooth. -/
theorem contDiff_slabCut (ℓ : E →L[ℝ] ℝ) (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (slabCut ℓ ε) :=
  Real.smoothTransition.contDiff.comp ((ℓ.contDiff.div_const ε).sub contDiff_const)

/-- `slabCut ℓ ε` is nonnegative. -/
theorem slabCut_nonneg (ℓ : E →L[ℝ] ℝ) (ε : ℝ) (x : E) : 0 ≤ slabCut ℓ ε x :=
  Real.smoothTransition.nonneg _

/-- `slabCut ℓ ε` is at most `1`. -/
theorem slabCut_le_one (ℓ : E →L[ℝ] ℝ) (ε : ℝ) (x : E) : slabCut ℓ ε x ≤ 1 :=
  Real.smoothTransition.le_one _

/-- `slabCut ℓ ε` has norm at most `1`. -/
theorem norm_slabCut_le_one (ℓ : E →L[ℝ] ℝ) (ε : ℝ) (x : E) : ‖slabCut ℓ ε x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (slabCut_nonneg ℓ ε x)]
  exact slabCut_le_one ℓ ε x

/-- On the excluded slab the cutoff vanishes. -/
theorem slabCut_eq_zero {ℓ : E →L[ℝ] ℝ} {ε : ℝ} (hε : 0 < ε) {x : E} (hx : ℓ x ≤ ε) :
    slabCut ℓ ε x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by rw [sub_nonpos, div_le_one hε]; exact hx)

/-- Beyond the slab the cutoff is `1`. -/
theorem slabCut_eq_one {ℓ : E →L[ℝ] ℝ} {ε : ℝ} (hε : 0 < ε) {x : E} (hx : 2 * ε ≤ ℓ x) :
    slabCut ℓ ε x = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_sub_iff_add_le, le_div_iff₀ hε]; linarith)

/-- **Derivative of the cutoff**, along every direction. -/
theorem fderiv_slabCut (ℓ : E →L[ℝ] ℝ) (ε : ℝ) (x w : E) :
    fderiv ℝ (slabCut ℓ ε) x w
      = deriv Real.smoothTransition (ℓ x / ε - 1) * (ℓ w / ε) := by
  have hin : HasFDerivAt (fun y => ℓ y / ε - 1) (ε⁻¹ • ℓ) x := by
    simpa [div_eq_inv_mul] using (ℓ.hasFDerivAt.const_smul ε⁻¹).sub_const 1
  have hc : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (ℓ x / ε - 1))
      (ℓ x / ε - 1) :=
    (contDiff_smoothTransition.differentiable (by simp) _).hasDerivAt
  have h := (hc.comp_hasFDerivAt x hin).fderiv
  rw [show slabCut ℓ ε = Real.smoothTransition ∘ fun y => ℓ y / ε - 1 from rfl, h]
  simp [div_eq_inv_mul]

/-- **Bound `C/ε` on the derivative of the cutoff.** -/
theorem abs_fderiv_slabCut_le {ℓ : E →L[ℝ] ℝ} {ε : ℝ} (hε : 0 < ε) {C : ℝ}
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) (x w : E) :
    |fderiv ℝ (slabCut ℓ ε) x w| ≤ C / ε * |ℓ w| := by
  rw [fderiv_slabCut, abs_mul, abs_div, abs_of_pos hε]
  calc |deriv Real.smoothTransition (ℓ x / ε - 1)| * (|ℓ w| / ε) ≤ C * (|ℓ w| / ε) := by
        gcongr; exact hC _
    _ = C / ε * |ℓ w| := by ring

/-- **Support of the cutoff's derivative in the slab.** -/
theorem fderiv_slabCut_eq_zero_of_notMem {ℓ : E →L[ℝ] ℝ} {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : ℓ x ∉ Icc ε (2 * ε)) (w : E) : fderiv ℝ (slabCut ℓ ε) x w = 0 := by
  rw [fderiv_slabCut, deriv_smoothTransition_eq_zero, zero_mul]
  contrapose! hx
  rw [mem_Icc, sub_nonneg, sub_le_iff_le_add, le_div_iff₀ hε, div_le_iff₀ hε] at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **Vanishing of the cutoff off the open half space**, so a test function multiplied by it is
supported where the hypothesis of a weak gradient applies. -/
theorem tsupport_mul_slabCut_subset {ℓ : E →L[ℝ] ℝ} {ε : ℝ} (hε : 0 < ε) (ψ : E → ℝ) :
    tsupport (fun x => slabCut ℓ ε x * ψ x) ⊆ {x | 0 < ℓ x} := by
  refine fun x hx => lt_of_lt_of_le hε
    (closure_minimal (s := Function.support fun x => slabCut ℓ ε x * ψ x)
      (t := {x | ε ≤ ℓ x}) (fun y hy => ?_) (isClosed_le continuous_const ℓ.continuous) hx)
  by_contra hcon
  exact hy (by
    change slabCut ℓ ε y * ψ y = 0
    rw [slabCut_eq_zero hε (not_le.1 hcon).le, zero_mul])

end EllipticPdes.Extension
