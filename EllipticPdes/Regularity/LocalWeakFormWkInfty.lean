/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.LocalWeakForm
public import EllipticPdes.Regularity.DifferentiatedWkInfty
public import EllipticPdes.Regularity.CoeffCk

/-!
# Differentiated identity for a weak solution under Guo's coefficient hypothesis

`EllipticPdes.Regularity.differentiated_weakForm_of_weakSolution` discharges every hypothesis
of the differentiated identity except the weak `ℓ`-derivative of the datum, for `C²` principal
and `C¹` lower-order coefficients. Guo, *Partial Differential Equations I and II* (Course
Lecture Notes), Theorem VIII.3.2 (p. 65) asks instead for `W^{k+2,∞}` and `W^{k+1,∞}`, and
`differentiated_weakForm_of_weakSolution_wkInfty` is the bridge under that hypothesis.

One hypothesis on the principal part remains beyond the bundles. The interior `H²`
estimate is proved by difference quotients, which asks the Lipschitz estimate of
`IsLipCoeff`, exactly as `higher_interior_regularity` asks for it in its base case. What
the `W^{k,∞}` bundles remove is the second classical derivative of the principal part and the
first of the lower-order coefficients.

## Main declarations

* `differentiated_weakForm_of_weakSolution`: Evans's equation (34) for a weak solution with
  `C²` principal and `C¹` lower-order coefficients.
* `differentiated_weakForm_of_weakSolution_wkInfty`: Evans's equation (34) for a weak solution,
  with every coefficient derivative read off a `W^{k,∞}` bundle.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

/-- **Differentiated-equation identity for a weak solution with `W^{k,∞}` coefficients.**
For a weak solution `u ∈ H₀¹(Ω)` of `L u = f` and any compact `V ⋐ Ω`, the second weak
derivatives of `u` on `V` exist and are bounded by the data, and for every direction `ℓ` in
which the datum has a weak derivative `Df`, the pair `(∂_ℓ∂ᵢu, Df)` satisfies Evans's equation
(34) against every test function supported in `V`, with each coefficient derivative read off its
bundle.

The `H²` estimate supplies the second derivatives and their bound,
`hasWeakDeriv_extendL2_of_mem_H01` the first derivatives, and `localWeakForm_of_fullBilin` the
localised weak identity. Only the
weak derivative of `f` is left as a hypothesis, since Evans's datum (36) contains `D^α f`. -/
theorem differentiated_weakForm_of_weakSolution_wkInfty {n : ℕ} (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsLipCoeff Op.toEllipticCoeff) {k m : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (m + 1))
    (ℓ : Fin (n + 1))
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω) (Df : L2D V),
      HasWeakDerivOn V ℓ (restrictL2 (Ω := V) (extendL2 hΩm f)) Df →
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ D2 : Fin (n + 1) → Fin (n + 1) → L2D V,
        (∀ p i, HasWeakDerivOn V p
            (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))) (D2 p i))
        ∧ (∀ p i, ‖D2 p i‖
              + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖
              + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖
            ≤ C * (‖f‖ + ‖(u : H1amb Ω) 0‖))
        ∧ ∀ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
            HasCompactSupport φ → tsupport φ ⊆ V →
          (∑ i, ∑ j, ∫ x in V, Op.a x i j * (D2 ℓ i x : ℝ) * partialD j φ x)
          = (∫ x in V, (Df x : ℝ) * φ x)
            - (∑ i, ∫ x in V, ((hbc.bReg i).D [ℓ] x
                  * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ)
                + Op.b x i * (D2 ℓ i x : ℝ)) * φ x)
            - (∫ x in V, (hbc.cReg.D [ℓ] x
                  * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)) x : ℝ)
                + Op.c x
                  * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ)) x : ℝ)) * φ x)
            + (∑ i, ∑ j, ∫ x in V, (hA.D [j, ℓ] i j x
                  * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ)
                + hA.D [ℓ] i j x * (D2 j i x : ℝ)) * φ x) := by
  classical
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  obtain ⟨C, hC0, hest⟩ := interior_H2_estimate Op hΩm hΩo hA1 hVc hVΩ
  refine ⟨C, hC0, fun u f Df hf_Df hu => ?_⟩
  choose D2 hD2w hD2n using hest u f hu
  refine ⟨D2, hD2w, hD2n, fun φ hφc hφcs hφV => ?_⟩
  exact differentiated_weakForm_wkInfty Op hA hbc ℓ
    (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))
    (fun i => restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)))
    D2 (restrictL2 (Ω := V) (extendL2 hΩm f)) Df
    (fun i => hD2w ℓ i) (fun i j => hD2w j i)
    (hasWeakDerivOn_of_hasWeakDeriv ℓ (hasWeakDeriv_extendL2_of_mem_H01 hΩm ℓ u.2))
    hf_Df
    (fun w hwc hwcs hwV => localWeakForm_of_fullBilin Op hΩm hVm hVΩ u f hu w hwc hwcs hwV)
    hφc hφcs hφV

/-- **Differentiated-equation identity for a weak solution (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1, Theorem 2).** For a weak solution `u ∈ H₀¹(Ω)` of `L u = f` with
`C²` principal coefficients and `C¹` lower-order coefficients, and any compact `V ⋐ Ω`, the
second weak derivatives of `u` on `V` exist and are bounded by the data, and for every direction
`ℓ` in which the datum has a weak derivative `Df`, the pair `(∂_ℓ∂ᵢu, Df)` satisfies Evans'
equation (34) against every test function supported in `V`.

The second derivatives come from `interior_H2_estimate`, the first derivatives from
`hasWeakDeriv_extendL2_of_mem_H01`, and the localised weak identity from
`localWeakForm_of_fullBilin`. The weak derivative of `f` is a hypothesis, since Evans (26)
assumes `f ∈ H^m(U)` and his datum (36) contains `D^α f`. -/
theorem differentiated_weakForm_of_weakSolution {n : ℕ} (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsC2Coeff Op.toEllipticCoeff) (ℓ : Fin (n + 1))
    (hb : ∀ i, ContDiff ℝ 1 (fun x => Op.b x i)) (hc : ContDiff ℝ 1 Op.c)
    (Mdb : Fin (n + 1) → ℝ)
    (hbdM : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      |partialD ℓ (fun y => Op.b y i) x| ≤ Mdb i)
    (Mdc : ℝ)
    (hcdM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      |partialD ℓ Op.c x| ≤ Mdc)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω) (Df : Lp ℝ 2 (volume.restrict V)),
      HasWeakDerivOn V ℓ (restrictL2 (Ω := V) (extendL2 hΩm f)) Df →
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ D2 : Fin (n + 1) → Fin (n + 1) → Lp ℝ 2 (volume.restrict V),
        (∀ k i, HasWeakDerivOn V k
            (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))) (D2 k i))
        ∧ (∀ k i, ‖D2 k i‖
              + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖
              + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖
            ≤ C * (‖f‖ + ‖(u : H1amb Ω) 0‖))
        ∧ ∀ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
            HasCompactSupport φ → tsupport φ ⊆ V →
          (∑ i, ∑ j, ∫ x in V, Op.a x i j * (D2 ℓ i x : ℝ) * partialD j φ x)
          = (∫ x in V, (Df x : ℝ) * φ x)
            - (∑ i, ∫ x in V, (partialD ℓ (fun y => Op.b y i) x
                  * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ)
                + Op.b x i * (D2 ℓ i x : ℝ)) * φ x)
            - (∫ x in V, (partialD ℓ Op.c x
                  * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)) x : ℝ)
                + Op.c x
                  * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ)) x : ℝ)) * φ x)
            + (∑ i, ∑ j, ∫ x in V,
                (partialD j (partialD ℓ (fun y => Op.a y i j)) x
                    * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ)
                  + partialD ℓ (fun y => Op.a y i j) x * (D2 j i x : ℝ)) * φ x) := by
  classical
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  obtain ⟨C, hC0, hest⟩ :=
    interior_H2_estimate Op hΩm hΩo hA.toIsC1Coeff.toIsLipCoeff hVc hVΩ
  refine ⟨C, hC0, fun u f Df hf_Df hu => ?_⟩
  choose D2 hD2w hD2n using hest u f hu
  refine ⟨D2, hD2w, hD2n, fun φ hφc hφcs hφV => ?_⟩
  exact differentiated_weakForm_of_pairs Op ℓ (fun i j => partialD ℓ (fun y => Op.a y i j))
    (fun i j => partialD j (partialD ℓ (fun y => Op.a y i j)))
    (fun i => partialD ℓ (fun y => Op.b y i)) (partialD ℓ Op.c)
    (fun i j => hA.toIsCkCoeff.toIsWkInftyCoeff.weakBddPair ℓ i j)
    (fun i j => hA.toIsCkCoeff.toIsWkInftyCoeff.weakBddPair_D j ℓ i j)
    (fun i => WeakBddPair.of_contDiff (hb i) ℓ ⟨_, Op.b_bdd i⟩ ⟨_, hbdM i⟩)
    (WeakBddPair.of_contDiff hc ℓ ⟨_, Op.c_bdd⟩ ⟨_, hcdM⟩)
    (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))
    (fun i => restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)))
    D2 (restrictL2 (Ω := V) (extendL2 hΩm f)) Df
    (fun i => hD2w ℓ i) (fun i j => hD2w j i)
    (hasWeakDerivOn_of_hasWeakDeriv ℓ (hasWeakDeriv_extendL2_of_mem_H01 hΩm ℓ u.2)) hf_Df
    (fun w hwc hwcs hwV => localWeakForm_of_fullBilin Op hΩm hVm hVΩ u f hu w hwc hwcs hwV)
    hφc hφcs hφV

end EllipticPdes.Regularity
