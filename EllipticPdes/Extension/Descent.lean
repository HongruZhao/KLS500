/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Descent of a linear map on representatives to `L²` classes

A linear map on functions that respects almost-everywhere equality on a submodule of
representatives, and bounds its image in `L²`, descends to a continuous linear map between spaces
of classes. This file proves that for vectors of `L²` classes, which is how an operator on
representatives becomes an operator on a Sobolev space.

## Main declarations

* `EllipticPdes.Extension.rep`: the representatives of the components of a vector of classes.
* `EllipticPdes.Extension.exists_clm_of_ae_compat`: the descent.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EllipticPdes.Extension

variable {α β ι κ : Type*} [MeasurableSpace α] [MeasurableSpace β] [Fintype κ]
  {μ : Measure α} {ν : Measure β}

/-- The representatives of the components of a vector of `L²` classes. -/
def rep (U : PiLp 2 fun _ : ι => Lp ℝ 2 μ) : ι → α → ℝ := fun i => ⇑(U i)

/-- The representatives of a sum are, almost everywhere, the sum of the representatives. -/
theorem rep_add (U V : PiLp 2 fun _ : ι => Lp ℝ 2 μ) (i : ι) :
    rep (U + V) i =ᵐ[μ] rep U i + rep V i := Lp.coeFn_add (U i) (V i)

/-- The representatives of a multiple are, almost everywhere, the multiple of the
representatives. -/
theorem rep_smul (a : ℝ) (U : PiLp 2 fun _ : ι => Lp ℝ 2 μ) (i : ι) :
    rep (a • U) i =ᵐ[μ] a • rep U i := Lp.coeFn_smul a (U i)

/-- **Descent of a bounded, almost-everywhere-compatible linear map to `L²` classes.** Let `T`
be a linear map on representatives, `G` a submodule of representatives containing those of the
submodule `S` of vectors of classes, on which `T` respects almost-everywhere equality. If the
image `T (rep U)` is in `L²` with seminorm at most `C ‖U‖` for `U ∈ S`, then `T` descends to a
continuous linear map on `S`. -/
theorem exists_clm_of_ae_compat [Fintype ι] (S : Submodule ℝ (PiLp 2 fun _ : ι => Lp ℝ 2 μ))
    (G : Submodule ℝ (ι → α → ℝ)) (hG : ∀ U ∈ S, rep U ∈ G)
    (T : (ι → α → ℝ) →ₗ[ℝ] (κ → β → ℝ))
    (hcompat : ∀ f ∈ G, ∀ g ∈ G, (∀ i, f i =ᵐ[μ] g i) → ∀ k, T f k =ᵐ[ν] T g k)
    (hmem : ∀ U ∈ S, ∀ k, MemLp (T (rep U) k) 2 ν) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ U ∈ S, ∀ k, eLpNorm (T (rep U) k) 2 ν ≤ ENNReal.ofReal (C * ‖U‖)) :
    ∃ E : S →L[ℝ] PiLp 2 (fun _ : κ => Lp ℝ 2 ν),
      (∀ (U : S) k, ⇑(E U k) =ᵐ[ν] T (rep (U : PiLp 2 fun _ : ι => Lp ℝ 2 μ)) k) ∧
      ∀ U, ‖E U‖ ≤ Real.sqrt (Fintype.card κ) * (C * ‖U‖) := by
  classical
  let Eg : S → PiLp 2 (fun _ : κ => Lp ℝ 2 ν) := fun U =>
    WithLp.toLp 2 fun k => (hmem U U.2 k).toLp _
  have hEg : ∀ (U : S) k, ⇑(Eg U k) =ᵐ[ν] T (rep (U : PiLp 2 fun _ : ι => Lp ℝ 2 μ)) k :=
    fun U k => (hmem U U.2 k).coeFn_toLp
  have hadd : ∀ U V : S, ∀ k, T (rep ((U + V : S) : PiLp 2 fun _ : ι => Lp ℝ 2 μ)) k
      =ᵐ[ν] T (rep (U : PiLp 2 fun _ : ι => Lp ℝ 2 μ)) k
        + T (rep (V : PiLp 2 fun _ : ι => Lp ℝ 2 μ)) k := fun U V k => by
    have h := hcompat _ (hG _ (U + V).2) (rep U.1 + rep V.1) (G.add_mem (hG U U.2) (hG V V.2))
      (fun i => rep_add U.1 V.1 i) k
    rwa [map_add] at h
  have hsmul : ∀ (a : ℝ) (U : S), ∀ k, T (rep ((a • U : S) : PiLp 2 fun _ : ι => Lp ℝ 2 μ)) k
      =ᵐ[ν] a • T (rep (U : PiLp 2 fun _ : ι => Lp ℝ 2 μ)) k := fun a U k => by
    have h := hcompat _ (hG _ (a • U).2) (a • rep U.1) (G.smul_mem a (hG U U.2))
      (fun i => rep_smul a U.1 i) k
    rwa [map_smul] at h
  let E₀ : S →ₗ[ℝ] PiLp 2 (fun _ : κ => Lp ℝ 2 ν) :=
    { toFun := Eg
      map_add' := fun U V => PiLp.ext fun k => Lp.ext <| by
        filter_upwards [hEg (U + V) k, hadd U V k, hEg U k, hEg V k,
          Lp.coeFn_add (Eg U k) (Eg V k)] with x h1 h2 h3 h4 h5
        simp only [PiLp.add_apply]
        rw [h5, Pi.add_apply, h1, h2, Pi.add_apply, h3, h4]
      map_smul' := fun a U => PiLp.ext fun k => Lp.ext <| by
        filter_upwards [hEg (a • U) k, hsmul a U k, hEg U k,
          Lp.coeFn_smul a (Eg U k)] with x h1 h2 h3 h4
        simp only [PiLp.smul_apply, RingHom.id_apply]
        rw [h4, Pi.smul_apply, h1, h2, Pi.smul_apply, h3] }
  have hnorm : ∀ U : S, ‖E₀ U‖ ≤ Real.sqrt (Fintype.card κ) * (C * ‖U‖) := fun U => by
    have hk : ∀ k, ‖Eg U k‖ ≤ C * ‖U‖ := fun k => by
      rw [Lp.norm_toLp]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hC U U.2 k)
    rw [PiLp.norm_eq_of_L2]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc ∑ k, ‖Eg U k‖ ^ 2 ≤ ∑ _k : κ, (C * ‖U‖) ^ 2 :=
          Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hk k) 2
      _ = (Real.sqrt (Fintype.card κ) * (C * ‖U‖)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_pow, mul_pow,
            Real.sq_sqrt (by positivity)]; ring
  exact ⟨E₀.mkContinuous (Real.sqrt (Fintype.card κ) * C) fun U => by
    simpa [mul_assoc] using hnorm U, hEg, fun U => by simpa [mul_assoc] using hnorm U⟩

end EllipticPdes.Extension
