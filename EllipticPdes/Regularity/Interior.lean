/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.Interior.NormBound

/-!
# Interior H² estimate

The capstone of the interior regularity chain. This file passes to the limit in the uniform
difference-quotient bound of `EllipticPdes.Regularity.Interior.NormBound` to produce the
second weak derivative, then assembles the coordinates into the interior H² estimate.

The module imports the whole chain (`Interior.Support`, `Interior.EnergyBound`,
`Interior.NormBound`).

## Main declarations

* `interior_secondWeakDeriv`: existence of the interior second weak derivative.
* `interior_H2_estimate`: the interior H² estimate.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Existence of the second weak derivative -/

/-- **Existence of the interior second weak derivative (Evans §6.3.1, VIII.2.1).** For each
`(k, i)` there is a constant `Cd`, fixed before the solution and the datum, such that for every
weak solution `u` of `L u = f` the whole-space extension of `ζ · ∂ᵢu` has an
`L²` weak `k`-derivative `w` with `‖w‖ ≤ Cd (‖f‖ + ‖u₀‖)`: this is the weak-limit converse
`weakDeriv_of_diffQuot_bounded` fed with the uniform difference-quotient bound
`interior_diffQuot_norm_bound`. Because `ζ ≡ 1` on `V`, the restriction of `w` to `V` is
`∂ₖ∂ᵢu` there. -/
theorem interior_secondWeakDeriv (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin d))} (T : CutoffTower Ω V) (k i : Fin d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ w : EucL2 d,
        HasWeakDeriv k (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ))) w
        ∧ ‖w‖ ≤ Cd * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  obtain ⟨Cd, hCd0, hCd⟩ := interior_diffQuot_norm_bound Op hΩm hA T k i
  refine ⟨Cd, hCd0, fun u f hu => ?_⟩
  obtain ⟨M, _hM0, hMbd, hMCd⟩ := hCd u f hu
  obtain ⟨w, hw, hwn⟩ :=
    weakDeriv_of_diffQuot_bounded k (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ))) M hMbd
  exact ⟨w, hw, le_trans hwn hMCd⟩

/-! ### Assembly of the interior H² estimate -/

/-- **Localised second derivative for one pair `(k, i)`.** There is a constant `G`, fixed before
the solution and the datum, such that the `V`-restriction of `∂ᵢu` has a weak `k`-derivative on
`V` whose norm, together with the norms of `∂ᵢu` and `u₀` on `V`, is at most `G (‖f‖ + ‖u₀‖)`.
The `V`-restriction of `ζ · ∂ᵢu` coincides with that of `∂ᵢu`, because `ζ ≡ 1` on `V`. -/
private lemma interior_secondDeriv_step (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff) {V : Set (EuclideanSpace ℝ (Fin d))}
    (hVm : MeasurableSet V) (hVΩ : V ⊆ Ω) (T : CutoffTower Ω V) (k i : Fin d) :
    ∃ G : ℝ, ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ wki : Lp ℝ 2 (volume.restrict V),
        HasWeakDerivOn V k (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))) wki ∧
        ‖wki‖ + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖
            + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖
          ≤ G * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  obtain ⟨Cd, _, hCd⟩ := interior_secondWeakDeriv Op hΩm hA T k i
  set dcoef : ℝ := Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) with hdcoef
  refine ⟨Cd + dcoef + 1, fun u f hu => ?_⟩
  obtain ⟨w, hw, hwCd⟩ := hCd u f hu
  set P : ℝ := ‖f‖ + ‖(u : H1amb Ω) 0‖ with hP
  have hDiuEq := restrictL2_extendL2_mulTest_of_eqOn hΩm hVm hVΩ T.hζ T.zeta_eqOn_one
    ((u : H1amb Ω) i.succ)
  refine ⟨restrictL2 w, ?_, ?_⟩
  · rw [← hDiuEq]; exact hasWeakDerivOn_of_hasWeakDeriv k hw
  · have h1 : ‖restrictL2 (Ω := V) w‖ ≤ Cd * P := (norm_restrictL2_le w).trans hwCd
    have h2 : ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖ ≤ dcoef * P :=
      (norm_restrictL2_le _).trans (by
        rw [norm_extendL2]; exact firstOrder_gradNorm_le Op u f hu i)
    have h3 : ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖ ≤ 1 * P :=
      (norm_restrictL2_le _).trans (by rw [norm_extendL2, one_mul, hP]; linarith [norm_nonneg f])
    calc _ ≤ Cd * P + dcoef * P + 1 * P := add_le_add (add_le_add h1 h2) h3
      _ = (Cd + dcoef + 1) * P := by ring

/-- **Interior H² estimate (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1;
Gilbarg-Trudinger, *Elliptic Partial Differential Equations of Second Order*, Theorem 8.8).**
For a weak solution `u ∈ H₀¹(Ω)` of `L u = f` with `W^{1,∞}` principal coefficients,
in the pointwise form of `IsLipCoeff`, and bounded transport and zeroth-order coefficients,
and for any compact `V ⋐ Ω`,
the second weak derivatives exist in `L²(V)` and are bounded by the data: for every direction
pair `(k, i)` there is a weak `k`-derivative `wki` of `∂ᵢu` on `V` (that is, `∂ₖ∂ᵢu ∈ L²(V)`)
with `‖∂ₖ∂ᵢu‖_{L²(V)} + ‖∂ᵢu‖_{L²(V)} + ‖u‖_{L²(V)} ≤ C (‖f‖ + ‖u‖)`. The constant is
quantified before the solution and the datum, so it depends only on the data
(`λ, Λ, A₁, d, ‖b‖∞, ‖c‖∞`, the cutoff tower for `V ⋐ Ω`) and on neither `u` nor `f`. This is
the `L²`-level statement that `u ∈ H²_loc(Ω)` with the interior estimate. -/
theorem interior_H2_estimate {n : ℕ} (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∀ k i : Fin (n + 1),
      ∃ wki : Lp ℝ 2 (volume.restrict V),
        HasWeakDerivOn V k
            (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))) wki ∧
          ‖wki‖
            + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖
            + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖
          ≤ C * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  choose G hG using fun k i =>
    interior_secondDeriv_step Op hΩm hA hVm hVΩ (cutoffTowerOfIsCompactSubsetIsOpen hVc hΩo hVΩ) k i
  obtain ⟨C, hC⟩ := Finite.exists_le (fun p : Fin (n + 1) × Fin (n + 1) => G p.1 p.2)
  refine ⟨max C 0, le_max_right _ _, fun u f hu k i => ?_⟩
  obtain ⟨wki, hHWD, hbound⟩ := hG k i u f hu
  exact ⟨wki, hHWD, hbound.trans (mul_le_mul_of_nonneg_right
    ((hC (k, i)).trans (le_max_left _ _)) (by positivity))⟩

end EllipticPdes.Regularity
