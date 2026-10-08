/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Basic
public import EllipticPdes.Regularity.DifferenceQuotient
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Smooth cutoff tower for the interior `H²` estimate

The interior second-derivative estimate (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8) localises the
difference-quotient method with a nested family of smooth cutoffs: an innermost cutoff `ζ` equal
to `1` on the region of interest `V`, a middle cutoff `ξ` equal to `1` on the support of `ζ`,
and an outermost cutoff `θ` equal to `1` on the support of `ξ`, all three compactly supported
inside the ambient domain `Ω`. The outermost support has a positive margin `δ`: every point of
`tsupport θ` stays inside `Ω` after a coordinate shift `h eₖ` of size `|h| < δ`, which is
exactly what lets the discrete difference quotient act inside `Ω` without losing mass.

This file provides:

* `exists_isTestFn_one_nhdsSet_of_isCompact`: the underlying smooth Urysohn-type cutoff lemma:
  for `K` compact inside an open `U`, a test function on `U` valued in `[0,1]` and equal to `1`
  on a neighbourhood of `K`. This specialises the classical smooth-partition-of-unity
  construction (`Mathlib.Geometry.Manifold.PartitionOfUnity`) to the trivial self-chart manifold
  structure that `EuclideanSpace ℝ (Fin d)` has as a finite-dimensional normed space, bridged
  back to plain `ContDiff` via `contMDiff_iff_contDiff`.
* `exists_margin_of_isCompact_subset_isOpen`: the positive-margin fact for a compact-in-open
  pair, from `IsCompact.exists_cthickening_subset_open`.
* `exists_one_margin`: a cutoff `≡ 1` near a compact set is `≡ 1` near every point within a
  margin of it.
* `ShiftAdmissible`: the conditions on a step `h` under which the Evans test element built from
  the cutoffs `ξ` and `θ` is admissible.
* `CutoffTower`: the bundle of the three nested cutoffs and the margin.
* `CutoffTower.exists_shiftAdmissible`, `CutoffTower.exists_zeta_shift`: every sufficiently
  small step is admissible for the tower, and a shifted point of `tsupport ζ` lies where `ξ = 1`.
* `cutoffTowerOfIsCompactSubsetIsOpen`: existence of a `CutoffTower` for every compact `V`
  inside an open `Ω`, built by three applications of the Urysohn-type cutoff lemma followed by
  one application of the margin lemma.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Urysohn-type smooth cutoff on a compact-in-open pair -/

/-- **Smooth Urysohn cutoff.** For `K` compact contained in an open `U`, a test function on `U`
(`EllipticPdes.Sobolev.IsTestFn`), valued in `[0,1]`, equal to `1` on a neighbourhood of `K`.
This is the smooth cutoff-function device used throughout interior regularity theory (Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1), obtained here from the manifold
smooth-partition-of-unity Urysohn lemma specialised to the self-chart manifold structure
`EuclideanSpace ℝ (Fin d)` has as a finite-dimensional normed space. -/
theorem exists_isTestFn_one_nhdsSet_of_isCompact {K U : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ζ : EuclideanSpace ℝ (Fin d) → ℝ,
      IsTestFn U ζ ∧ (∀ᶠ x in 𝓝ˢ K, ζ x = 1) ∧ ∀ x, ζ x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨δ, δpos, hδ⟩ := hK.exists_cthickening_subset_open hU hKU
  have ht_open : IsOpen (Metric.thickening δ K) := Metric.isOpen_thickening
  have ht_closure_compact : IsCompact (closure (Metric.thickening δ K)) :=
    (hK.cthickening (r := δ)).of_isClosed_subset isClosed_closure
      (Metric.closure_thickening_subset_cthickening δ K)
  have ht_closure_subset : closure (Metric.thickening δ K) ⊆ U :=
    (Metric.closure_thickening_subset_cthickening δ K).trans hδ
  obtain ⟨f, hf1, hf0, hfIcc⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d))) (n := (⊤ : ℕ∞)) hK.isClosed
    (t := Metric.thickening δ K)
    (by rw [ht_open.interior_eq]; exact Metric.self_subset_thickening δpos K)
  have hsupp : Function.support (f : EuclideanSpace ℝ (Fin d) → ℝ)
      ⊆ Metric.thickening δ K := by
    intro x hx
    by_contra hxt
    exact hx (hf0 x hxt)
  refine ⟨(f : EuclideanSpace ℝ (Fin d) → ℝ), ⟨?_, ?_, ?_⟩, hf1, hfIcc⟩
  · exact contMDiff_iff_contDiff.mp f.contMDiff
  · exact ht_closure_compact.of_isClosed_subset isClosed_closure (closure_mono hsupp)
  · exact (closure_mono hsupp).trans ht_closure_subset

/-! ### Positive shift margin on a compact-in-open pair -/

/-- **Positive margin.** For `K` compact inside an open `Ω`, there is `δ > 0` such that every
point of `K` stays inside `Ω` after any coordinate shift `h eₖ` with `|h| < δ`. This is the
finite-margin fact that lets the interior difference-quotient method translate a cutoff's
support without leaving the domain (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8). -/
theorem exists_margin_of_isCompact_subset_isOpen {K Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : Fin d) (h : ℝ), |h| < δ → ∀ x ∈ K, x + hshift k h ∈ Ω := by
  obtain ⟨δ, δpos, hδ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  refine ⟨δ, δpos, fun k h hh x hx => hδ (Metric.thickening_subset_cthickening δ K ?_)⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨x, hx, ?_⟩
  rw [dist_eq_norm, show x + hshift k h - x = hshift k h from by abel]
  calc ‖hshift k h‖ = |h| := by simp [hshift, norm_smul]
    _ < δ := hh

/-! ### Nested cutoff tower -/

/-- **Nested cutoff tower.** Three test functions on `Ω`: `ζ` equal to `1` on the base
compact set `V`, `ξ` equal to `1` on the support of `ζ`, `θ` equal to `1` on the support of
`ξ`, together with a positive coordinate-shift margin valid on the support of `θ`. This is
exactly the tower `ζ`, `ξ`, `θ` nested in that support-inclusion order, localising the
difference-quotient method of the interior `H²` estimate (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8). -/
structure CutoffTower (Ω V : Set (EuclideanSpace ℝ (Fin d))) where
  /-- The innermost cutoff, equal to `1` on `V`. -/
  ζ : EuclideanSpace ℝ (Fin d) → ℝ
  /-- The middle cutoff, equal to `1` on `tsupport ζ`. -/
  ξ : EuclideanSpace ℝ (Fin d) → ℝ
  /-- The outermost cutoff, equal to `1` on `tsupport ξ`. -/
  θ : EuclideanSpace ℝ (Fin d) → ℝ
  /-- `ζ` is a test function on `Ω`. -/
  hζ : IsTestFn Ω ζ
  /-- `ξ` is a test function on `Ω`. -/
  hξ : IsTestFn Ω ξ
  /-- `θ` is a test function on `Ω`. -/
  hθ : IsTestFn Ω θ
  /-- `ζ` is valued in `[0,1]`. -/
  hζ_Icc : ∀ x, ζ x ∈ Set.Icc (0 : ℝ) 1
  /-- `ξ` is valued in `[0,1]`. -/
  hξ_Icc : ∀ x, ξ x ∈ Set.Icc (0 : ℝ) 1
  /-- `θ` is valued in `[0,1]`. -/
  hθ_Icc : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1
  /-- `ζ ≡ 1` on a neighbourhood of `V`. -/
  hζ_one : ∀ᶠ x in 𝓝ˢ V, ζ x = 1
  /-- `ξ ≡ 1` on a neighbourhood of `tsupport ζ`. -/
  hξ_one : ∀ᶠ x in 𝓝ˢ (tsupport ζ), ξ x = 1
  /-- `θ ≡ 1` on a neighbourhood of `tsupport ξ`. -/
  hθ_one : ∀ᶠ x in 𝓝ˢ (tsupport ξ), θ x = 1
  /-- The positive coordinate-shift margin on `tsupport θ`. -/
  margin : ℝ
  /-- The margin is positive. -/
  hmargin_pos : 0 < margin
  /-- Below the margin, every point of `tsupport θ` stays inside `Ω` after a coordinate
  shift. -/
  hmargin : ∀ (k : Fin d) (h : ℝ), |h| < margin → ∀ x ∈ tsupport θ, x + hshift k h ∈ Ω

namespace CutoffTower

variable {Ω V : Set (EuclideanSpace ℝ (Fin d))}

/-- The innermost cutoff is equal to `1` at every point of `V`, rather than on a neighbourhood
of it. -/
theorem zeta_eqOn_one (T : CutoffTower Ω V) : Set.EqOn T.ζ 1 V :=
  fun x hx => T.hζ_one.self_of_nhdsSet x hx

/-- The middle cutoff is equal to `1` at every point of `tsupport ζ`. -/
theorem xi_eqOn_one (T : CutoffTower Ω V) : Set.EqOn T.ξ 1 (tsupport T.ζ) :=
  fun x hx => T.hξ_one.self_of_nhdsSet x hx

/-- The outermost cutoff is equal to `1` at every point of `tsupport ξ`. -/
theorem theta_eqOn_one (T : CutoffTower Ω V) : Set.EqOn T.θ 1 (tsupport T.ξ) :=
  fun x hx => T.hθ_one.self_of_nhdsSet x hx

end CutoffTower

/-- **One-neighbourhood margin.** If the cutoff `η` is `≡ 1` on a neighbourhood of a compact set
`K`, then there is a positive margin `δ` such that `η` is locally constant `≡ 1` near every
point within `δ` of `K`. -/
theorem exists_one_margin {η : EuclideanSpace ℝ (Fin d) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hη : ∀ᶠ x in 𝓝ˢ K, η x = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d),
      (∃ p ∈ K, dist x p < δ) → η =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
  obtain ⟨U, hUopen, hKU, hUsub⟩ := mem_nhdsSet_iff_exists.mp hη
  obtain ⟨δ, hδpos, hδ⟩ := hK.exists_cthickening_subset_open hUopen hKU
  refine ⟨δ, hδpos, fun x hx => ?_⟩
  have hxU : x ∈ U :=
    hδ (Metric.thickening_subset_cthickening δ K (Metric.mem_thickening_iff.mpr hx))
  exact Filter.eventually_of_mem (hUopen.mem_nhds hxU) (fun y hy => hUsub hy)

/-- **Admissible shift for a pair of cutoffs.** The conditions on the step `h` in the
direction `k` under which the difference-quotient test element built from the inner cutoff `ξ`
and the outer cutoff `θ` is admissible: shifting `tsupport ξ²` by `h eₖ` and `tsupport θ` by
`-h eₖ` stays inside `Ω`, and `θ ≡ 1` (hence `∂ⱼθ = 0`) on the part of `Ω` reachable from
`tsupport ξ²` by the shift. -/
structure ShiftAdmissible (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (ξ θ : EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) (h : ℝ) : Prop where
  /-- Shifting the inner support by `h eₖ` stays inside `Ω`. -/
  shift_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω
  /-- Shifting the outer support by `-h eₖ` stays inside `Ω`. -/
  shift_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω
  /-- `θ ≡ 1` on the part of `Ω` reachable from the inner support. -/
  theta_one : ∀ x ∈ Ω,
    x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y) →
      θ x = 1
  /-- `∂ⱼθ = 0` on the part of `Ω` reachable from the inner support. -/
  dtheta_zero : ∀ j : Fin d, ∀ x ∈ Ω,
    x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y) →
      partialD j θ x = 0

namespace CutoffTower

variable {Ω V : Set (EuclideanSpace ℝ (Fin d))}

/-- **Shift conditions from the tower.** Every sufficiently small step is admissible for the
pair `(ξ, θ)` of a cutoff tower, in every direction. -/
theorem exists_shiftAdmissible (T : CutoffTower Ω V) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ T.margin ∧ ∀ (k : Fin d) (h : ℝ), |h| < δ →
      ShiftAdmissible Ω T.ξ T.θ k h := by
  obtain ⟨δθ, hδθ, hθ1m⟩ := exists_one_margin T.hξ.2.1 T.hθ_one
  have hξ2 : tsupport (fun y => T.ξ y * T.ξ y) ⊆ tsupport T.ξ := tsupport_mul_subset_left
  have hξθ : tsupport T.ξ ⊆ tsupport T.θ := fun x hx =>
    subset_tsupport T.θ (by rw [Function.mem_support, T.theta_eqOn_one hx]; exact one_ne_zero)
  refine ⟨min T.margin δθ, lt_min T.hmargin_pos hδθ, min_le_left _ _, fun k h hh => ?_⟩
  have hm : |h| < T.margin := hh.trans_le (min_le_left _ _)
  have hθ : |h| < δθ := hh.trans_le (min_le_right _ _)
  have hev : ∀ x, x ∈ tsupport (fun y => T.ξ y * T.ξ y)
      ∨ x + hshift k (-h) ∈ tsupport (fun y => T.ξ y * T.ξ y) →
      T.θ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    rintro x (h1 | h2)
    · exact hθ1m x ⟨x, hξ2 h1, by rw [dist_self]; exact hδθ⟩
    · refine hθ1m x ⟨x + hshift k (-h), hξ2 h2, ?_⟩
      have hn : ‖hshift k h‖ = |h| := by simp [hshift, norm_smul]
      rwa [dist_eq_norm, show x - (x + hshift k (-h)) = hshift k h by rw [hshift_neg]; abel, hn]
  exact
    { shift_in := fun x hx => T.hmargin k h hm x (hξθ (hξ2 hx))
      shift_out := fun x hx => T.hmargin k (-h) (by rwa [abs_neg]) x hx
      theta_one := fun x _ hx => by simpa using (hev x hx).eq_of_nhds
      dtheta_zero := fun j x _ hx => by
        rw [partialD, (hev x hx).fderiv_eq]
        simp }

/-- **Localisation of the innermost cutoff.** For small steps, a shifted point of `tsupport ζ`
lies where the middle cutoff is `1`: `ζ(x + h eₖ) = 0 ∨ ξ x = 1`. -/
theorem exists_zeta_shift (T : CutoffTower Ω V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : Fin d) (h : ℝ), |h| < δ →
      ∀ x, T.ζ (x + hshift k h) = 0 ∨ T.ξ x = 1 := by
  obtain ⟨δ, hδ, hξ1⟩ := exists_one_margin T.hζ.2.1 T.hξ_one
  refine ⟨δ, hδ, fun k h hh x => ?_⟩
  by_cases hz : T.ζ (x + hshift k h) = 0
  · exact Or.inl hz
  · refine Or.inr ?_
    have hn : ‖hshift k h‖ = |h| := by simp [hshift, norm_smul]
    have hd : dist x (x + hshift k h) < δ := by
      rwa [dist_eq_norm, show x - (x + hshift k h) = -hshift k h by abel, norm_neg, hn]
    simpa using (hξ1 x ⟨x + hshift k h, subset_tsupport _ (Function.mem_support.mpr hz), hd⟩
      ).eq_of_nhds

end CutoffTower

/-- **Existence of the cutoff tower.** For any compact `V` inside an open `Ω`, a cutoff tower
based at `V` exists: three applications of `exists_isTestFn_one_nhdsSet_of_isCompact` build
`ζ`, `ξ`, `θ` in turn (each new cutoff's compact set is the topological support of the
previous one, which stays inside `Ω`), and `exists_margin_of_isCompact_subset_isOpen` supplies
the final margin on `tsupport θ`. -/
noncomputable def cutoffTowerOfIsCompactSubsetIsOpen {Ω V : Set (EuclideanSpace ℝ (Fin d))}
    (hV : IsCompact V) (hΩ : IsOpen Ω) (hVΩ : V ⊆ Ω) : CutoffTower Ω V := by
  choose ζ hζ hζ_one hζ_Icc using
    exists_isTestFn_one_nhdsSet_of_isCompact hV hΩ hVΩ
  choose ξ hξ hξ_one hξ_Icc using
    exists_isTestFn_one_nhdsSet_of_isCompact hζ.2.1 hΩ hζ.2.2
  choose θ hθ hθ_one hθ_Icc using
    exists_isTestFn_one_nhdsSet_of_isCompact hξ.2.1 hΩ hξ.2.2
  choose δ hδ_pos hδ using
    exists_margin_of_isCompact_subset_isOpen hθ.2.1 hΩ hθ.2.2
  exact
    { ζ := ζ
      ξ := ξ
      θ := θ
      hζ := hζ
      hξ := hξ
      hθ := hθ
      hζ_Icc := hζ_Icc
      hξ_Icc := hξ_Icc
      hθ_Icc := hθ_Icc
      hζ_one := hζ_one
      hξ_one := hξ_one
      hθ_one := hθ_one
      margin := δ
      hmargin_pos := hδ_pos
      hmargin := hδ }

end EllipticPdes.Regularity
