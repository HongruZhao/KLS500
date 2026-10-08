/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Poincare.Geometry
public import EllipticPdes.Poincare.Slab
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Poincaré inequality on a coordinate box

`Poincare/Geometry.lean` reduces coercivity of the bilinear form of the Laplacian on a domain `Ω`
to the **slice bound**

  `∫_Ω φ² ≤ C · ∫_Ω (∂ᵢφ)²`   (`hslice`, every test function, every direction `i`),

phrased on `EuclideanSpace ℝ (Fin (n+1))`. On an open coordinate box `∏ₖ (aₖ, bₖ)` the slice
bound with `C = (bᵢ - aᵢ)² / 2` is the slab Poincaré inequality
`EllipticPdes.Poincare.integral_sq_le_of_tsupport_subset_slab` for the coordinate functional
`xᵢ`, since the box lies in the slab `aᵢ < xᵢ < bᵢ`.

The headline results are `slice_bound_euclBox` (the per-direction Poincaré bound on the box) and
`poincare_H01_of_subset_euclBox` (the Poincaré inequality on `H₀¹` of any subset of a box).
-/

@[expose] public section

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Poincare

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- The open coordinate box `∏ₖ (aₖ, bₖ)` inside `EuclideanSpace ℝ (Fin (n+1))`. -/
def euclBox (a b : Fin (n + 1) → ℝ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {x | ∀ k, x k ∈ Set.Ioo (a k) (b k)}

/-- The open coordinate box is open: it is a finite intersection of coordinate
preimages of open intervals. -/
lemma isOpen_euclBox (a b : Fin (n + 1) → ℝ) : IsOpen (euclBox a b) := by
  have h : euclBox a b
      = ⋂ k, (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x k) ⁻¹' Set.Ioo (a k) (b k) := by
    ext x
    simp [euclBox, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_Ioo.preimage ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous)

/-- **Per-direction Poincaré bound on an open box** (the slice bound `hslice`). For a test
function `φ` supported in the open box `∏ₖ (aₖ, bₖ)` of `EuclideanSpace ℝ (Fin (n+1))`,
`∫ φ² ≤ (bᵢ - aᵢ)² / 2 · ∫ (∂ᵢφ)²`. The box lies in the slab `aᵢ < xᵢ < bᵢ`, so this is
`integral_sq_le_of_tsupport_subset_slab` for the coordinate functional `xᵢ`. -/
theorem slice_bound_euclBox (a b : Fin (n + 1) → ℝ) (_hab : ∀ k, a k ≤ b k)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn (euclBox a b) φ) (i : Fin (n + 1)) :
    ∫ x in euclBox a b, (φ x) ^ 2
      ≤ (b i - a i) ^ 2 / 2 * ∫ x in euclBox a b, (partialD i φ x) ^ 2 := by
  have hz : ∀ {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}, tsupport g ⊆ euclBox a b →
      ∫ x in euclBox a b, g x ^ 2 = ∫ x, g x ^ 2 := fun hg =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun hm => hx (hg hm)]; ring
  rw [hz h.tsupport_subset, hz ((tsupport_partialD_subset i φ).trans h.tsupport_subset)]
  exact integral_sq_le_of_tsupport_subset_slab (h.contDiff.of_le (by simp)) h.hasCompactSupport
    (EuclideanSpace.proj i) (by simp) (h.tsupport_subset.trans fun x hx => hx i)

/-- **Per-direction Poincaré bound for a subset of a box.** A test function of any
`Ω` inside the open box obeys the box slice bound with the integrals taken over `Ω`. -/
theorem slice_bound_of_subset_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hsub : Ω ⊆ euclBox a b)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn Ω φ) (i : Fin (n + 1)) :
    ∫ x in Ω, (φ x) ^ 2 ≤ (b i - a i) ^ 2 / 2 * ∫ x in Ω, (partialD i φ x) ^ 2 := by
  have hbox : IsTestFn (euclBox a b) φ := h.mono hsub
  -- Both box integrals restrict to `Ω`: the integrands vanish on `euclBox \ Ω`.
  have hφeq : ∫ x in euclBox a b, (φ x) ^ 2 = ∫ x in Ω, (φ x) ^ 2 :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isOpen_euclBox a b).measurableSet hsub
      (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hm => hx.2 (h.2.2 hm))]
        ring)
  have hdeq : ∫ x in euclBox a b, (partialD i φ x) ^ 2
      = ∫ x in Ω, (partialD i φ x) ^ 2 :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isOpen_euclBox a b).measurableSet hsub
      (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport
          (fun hm => hx.2 (((tsupport_partialD_subset i φ).trans h.2.2) hm))]
        ring)
  calc ∫ x in Ω, (φ x) ^ 2
      = ∫ x in euclBox a b, (φ x) ^ 2 := hφeq.symm
    _ ≤ (b i - a i) ^ 2 / 2 * ∫ x in euclBox a b, (partialD i φ x) ^ 2 :=
        slice_bound_euclBox a b hab hbox i
    _ = (b i - a i) ^ 2 / 2 * ∫ x in Ω, (partialD i φ x) ^ 2 := by rw [hdeq]

/-- **Poincaré inequality on `H₀¹(Ω)` for `Ω` inside a box** with sides at most `L`:
`‖U₀‖² ≤ L²/(2(n+1)) · ∑ᵢ ‖Uᵢ‖²`. -/
theorem poincare_H01_of_subset_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hsub : Ω ⊆ euclBox a b)
    {L : ℝ} (hL : ∀ i, b i - a i ≤ L)
    {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    ‖U 0‖ ^ 2 ≤ L ^ 2 / (2 * (n + 1)) * ∑ i : Fin (n + 1), ‖U i.succ‖ ^ 2 := by
  have hL0 : 0 ≤ L := le_trans (sub_nonneg.mpr (hab 0)) (hL 0)
  have hslice : ∀ {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      (h : IsTestFn Ω φ) (i : Fin (n + 1)),
      ∫ x in Ω, (φ x) ^ 2 ≤ L ^ 2 / 2 * ∫ x in Ω, (partialD i φ x) ^ 2 := by
    intro φ h i
    refine le_trans (slice_bound_of_subset_euclBox hab hsub h i)
      (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun x => sq_nonneg _))
    have hside : (b i - a i) ^ 2 ≤ L ^ 2 := by
      have h1 : 0 ≤ b i - a i := sub_nonneg.mpr (hab i)
      nlinarith [hL i]
    linarith
  have h := poincare_H01 (Ω := Ω) _
    (fun {_φ} hφ => poincare_testfn (Nat.succ_pos n) (L ^ 2 / 2)
      (fun {_ψ} h' i => hslice h' i) hφ) hU
  refine le_trans h (le_of_eq ?_)
  rw [div_div]
  norm_cast

/-- The test-function instance, in the slice-constant form the coercivity layer
consumes. Derived FROM `poincare_H01_of_subset_euclBox` (test graphs lie in `H₀¹`). -/
theorem testfn_bound_of_subset_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hsub : Ω ⊆ euclBox a b)
    {C : ℝ} (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn Ω φ) :
    ‖(h.testGraph 0 : L2D Ω)‖ ^ 2
      ≤ C / (n + 1) * ∑ i : Fin (n + 1), ‖h.testGraph i.succ‖ ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have h2C : (0 : ℝ) ≤ 2 * C := by linarith
  have hL : ∀ i, b i - a i ≤ Real.sqrt (2 * C) := by
    intro i
    have h1 : 0 ≤ b i - a i := sub_nonneg.mpr (hab i)
    have h2 : (b i - a i) ^ 2 ≤ 2 * C := by linarith [hC i]
    calc b i - a i = Real.sqrt ((b i - a i) ^ 2) := (Real.sqrt_sq h1).symm
      _ ≤ Real.sqrt (2 * C) := Real.sqrt_le_sqrt h2
  have hmem : h.testGraph ∈ H01 Ω :=
    (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨φ, h, rfl⟩)
  have hp := poincare_H01_of_subset_euclBox hab hsub hL hmem
  rw [Real.sq_sqrt h2C] at hp
  refine le_trans hp (le_of_eq ?_)
  rw [mul_div_mul_left C ((n : ℝ) + 1) two_ne_zero]

/-- **Poincaré inequality on a box** (Theorem `thm: poincare`). For every
`U ∈ H₀¹(Ω)` of the open coordinate box `Ω = ∏ₖ (aₖ, bₖ)` whose side lengths are bounded
by `L`,

  `‖u‖²_{L²(Ω)} ≤ L² / (2 (n + 1)) · ‖∇u‖²_{L²(Ω)}`,

i.e. `‖u‖_{L²} ≤ C_P ‖∇u‖_{L²}` with `C_P = L / √(2 (n + 1))`; taking `L` the maximal
side length gives the diameter-based constant. In the graph encoding the function part is
`U 0` and the gradient components are `U i.succ`. This is
`poincare_H01_of_subset_euclBox` for the box itself. -/
theorem poincare_H01_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {L : ℝ} (hL : ∀ i, b i - a i ≤ L)
    {U : H1amb (euclBox a b)} (hU : U ∈ H01 (euclBox a b)) :
    ‖U 0‖ ^ 2 ≤ L ^ 2 / (2 * (n + 1)) * ∑ i : Fin (n + 1), ‖U i.succ‖ ^ 2 :=
  poincare_H01_of_subset_euclBox hab subset_rfl hL hU

/-- The test-function instance of the box Poincaré inequality, in the slice-constant form
the coercivity layer consumes: with every side contribution `(bᵢ - aᵢ)² / 2` bounded by
`C`, every test function on the box obeys the graph-coordinate bound with constant
`C / (n + 1)`. -/
theorem testfn_bound_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {C : ℝ} (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn (euclBox a b) φ) :
    ‖(h.testGraph 0 : L2D (euclBox a b))‖ ^ 2
      ≤ C / (n + 1) * ∑ i : Fin (n + 1), ‖h.testGraph i.succ‖ ^ 2 :=
  testfn_bound_of_subset_euclBox hab subset_rfl hC h

end EllipticPdes.Poincare
