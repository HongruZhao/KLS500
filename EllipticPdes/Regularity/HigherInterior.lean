/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.HigherWeakDeriv
public import EllipticPdes.Regularity.LowerOrderWkInfty
public import EllipticPdes.Regularity.IteratedSum
public import EllipticPdes.Regularity.IteratedRestrict
public import EllipticPdes.Regularity.WeakFormDense
public import EllipticPdes.Regularity.LocalWeakFormWkInfty
public import EllipticPdes.Regularity.CutoffDeriv
public import EllipticPdes.Regularity.CutoffCommutator
public import EllipticPdes.Regularity.CollarIdentify
public import EllipticPdes.Regularity.DatumPiece
public import EllipticPdes.Regularity.CutoffDatum

/-!
# Higher interior regularity

Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem VIII.3.2
(*Higher Interior Regularity*, p. 65). For a weak solution `u` of `L u = f` with
`a_{ij} ∈ W^{k+1,∞}`, `b_i, c ∈ W^{k,∞}` and `f ∈ H^k`, the solution lies in `H^{k+2}_loc`
with

`‖u‖_{H^{k+2}(V)} ≤ C (‖f‖_{H^k(Ω)} + ‖u‖_{L²(Ω)})` for every `V ⋐ Ω`,

the constant depending on the data and the pair `V ⋐ Ω` and on neither `u` nor `f`. Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 (p. 332) is the same statement
with `C^{k+1}` coefficients, which `IsCkCoeff.toIsWkInftyCoeff` shows to be the stronger
hypothesis. The theorem below asks Guo's orders, together with `a_{ij} ∈ W^{1,∞}` for the base case.

## Shape of the induction

`InteriorRegularityAt Op Ω k` packages the conclusion at order `k`, and the theorem is an
induction on `k` over that predicate.

* Order `0` is `interior_H2_estimate` with its `(k, i)`-indexed second derivatives assembled
  into a `HasIteratedWeakDerivOn` family of order `2`.
* The step differentiates the equation once. Where `u` solves `L u = f`, the derivative `∂_l u`
  solves `L (∂_l u) = ∂_l f + R_l`, with `R_l` collecting the terms in which the differentiation
  lands on a coefficient rather than on `u`. Those terms pair one derivative of a coefficient
  against derivatives of `u` of order at most two, so `R_l` sits in `H^{k-1}` once the
  order-`k-1` conclusion is available for `u` itself. Applying the induction hypothesis to `∂_l
  u` on an intermediate `V ⋐ W ⋐ Ω` gives `∂_l u ∈ H^{k+1}(V)`, which is `u ∈ H^{k+2}(V)`.

The differentiated equation is `EllipticPdes.Regularity.differentiated_weakForm_wkInfty`, and
the admissibility of the test function it needs is `interior_cutoffGrad_mem_H01`.

## Main declarations

* `InteriorRegularityAt`: the order-`k` conclusion, as a predicate, so that the induction has
  something to be an induction over.
* `interiorRegularityAt_zero`: the base case.
* `exists_cutoffDeriv_weakForm`: the differentiated equation, as a weak formulation for the
  cutoff derivative, which is what the induction hypothesis consumes.
* `interiorRegularityAt_succ`: the induction step.
* `higher_interior_regularity`: the theorem.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **Order-`k` interior conclusion.** For every compact `V ⋐ Ω` there is a constant,
quantified before the solution and the datum, bounding every weak derivative of `u` of order at
most `k + 2` on `V` by `‖f‖_{H^k} + ‖u‖_{L²}`. The datum's `H^k` norm enters through a bound
`M` on its own iterated family, which `IteratedL2Bound.norm_le` shows to dominate `‖f‖`. -/
def InteriorRegularityAt (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (k : ℕ) : Prop :=
  ∀ {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}, IsCompact V → V ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω) (M : ℝ)
      (hfk : HasIteratedWeakDerivOn Ω k f), IteratedL2Bound hfk M →
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ hu : HasIteratedWeakDerivOn V (k + 2)
          (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))),
        IteratedL2Bound hu (C * (M + ‖(u : H1amb Ω) 0‖))

/-- **Base case: order zero is the interior `H²` estimate.** The estimate
`interior_H2_estimate` returns, for each direction pair `(k, i)`, a weak `k`-derivative of
`∂ᵢu` on `V` together with its bound. Assembling those into a `HasIteratedWeakDerivOn` family
of order `2` is a matter of naming: the empty list is `u`, a singleton `[i]` is `∂ᵢu`, a pair
`[k, i]` is the returned `wki`, and longer lists are unconstrained because `D_step` is asked
only of lists shorter than `2`.

The first-order step, which the `H²` estimate does not itself provide, is
`hasWeakDeriv_extendL2_of_mem_H01`: the ambient encoding's coordinate `i.succ` is the weak
`i`-derivative of coordinate `0` on the whole space, and `hasWeakDerivOn_of_hasWeakDeriv`
localises it to `V`.

No constant is spent. The `H²` estimate bounds the sum of the three norms, so each of them is
bounded on its own, and `IteratedL2Bound.norm_le` supplies `‖f‖ ≤ M`. -/
theorem interiorRegularityAt_zero (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff) :
    InteriorRegularityAt Op hΩm 0 := by
  classical
  intro V hVc hVΩ
  obtain ⟨C, hC0, hC⟩ := interior_H2_estimate Op hΩm hΩo hA hVc hVΩ
  refine ⟨C, hC0, fun u f M hfk hM hu => ?_⟩
  choose W hW hWb using hC u f hu
  -- The family: the empty list is `u`, a singleton is a first derivative, a pair is the
  -- second derivative the `H²` estimate returned. Longer lists are never asked about.
  refine ⟨⟨fun α =>
      match α with
      | [] => restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))
      | [i] => restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))
      | [k, i] => W k i
      | _ => 0, rfl, ?_⟩, ?_⟩
  · rintro m (_ | ⟨i, _ | ⟨j, rest⟩⟩) hα
    · exact hasWeakDerivOn_of_hasWeakDeriv m (hasWeakDeriv_extendL2_of_mem_H01 hΩm m u.2)
    · exact hW m i
    · simp at hα
  -- Each of the three norms is dominated by the sum the `H²` estimate bounds.
  · have hfM : ‖f‖ ≤ M := hM.norm_le
    have hshift : C * (‖f‖ + ‖(u : H1amb Ω) 0‖) ≤ C * (M + ‖(u : H1amb Ω) 0‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    rintro (_ | ⟨i, _ | ⟨j, rest⟩⟩) hα
    · refine le_trans ?_ hshift
      have h := hWb 0 0
      have h1 := norm_nonneg (W 0 0)
      have h2 := norm_nonneg (restrictL2 (Ω := V)
        (extendL2 hΩm ((u : H1amb Ω) (0 : Fin (n + 1)).succ)))
      linarith
    · refine le_trans ?_ hshift
      have h := hWb 0 i
      have h1 := norm_nonneg (W 0 i)
      have h2 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))
      linarith
    · rcases rest with _ | ⟨p, rest'⟩
      · refine le_trans ?_ hshift
        have h := hWb i j
        have h1 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) j.succ)))
        have h2 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))
        linarith
      · simp at hα

/-- **Weak formulation of the cut-off derivative against a test function.** Let `U` be the
cut-off derivative `ξ · ∂_ℓ u`, with gradient given in closed form by `hgrad`, and let `HuN` be
the family of derivatives of `u` on the collar `N`. Then `B[U, v]` is the datum
`cutoffDatumPairing` for every test function `v`: expanding the bilinear form
(`setIntegral_blocks_eq`) and the differentiated equation tested against `ξ v`
(`differentiated_weakForm_wkInfty`) gives the same twelve shapes, once the mixed second
derivatives are swapped under the cutoff `ϑ`. -/
private lemma cutoffDeriv_pairing_eq (Op : FullEllipticOp (n + 1))
    {Ω N : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω)
    (hNm : MeasurableSet N) (hNΩ : N ⊆ Ω) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (k + 1))
    {ξ ϑ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hξNt : IsTestFn N ξ) (hϑ : IsTestFn N ϑ)
    (hϑ_eqOn : Set.EqOn ϑ 1 (tsupport ξ)) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ))
    (hfk : HasIteratedWeakDerivOn Ω (k + 1) f)
    (HuN : HasIteratedWeakDerivOn N (k + 2) (restrictL2 (Ω := N) (extendL2 hΩm ((u : H1amb Ω) 0))))
    (hDu : ∀ i : Fin (n + 1),
      HuN.D [i] = restrictL2 (Ω := N) (extendL2 hΩm ((u : H1amb Ω) i.succ)))
    (ℓ : Fin (n + 1)) {Uamb : H1amb Ω} (hUmem : Uamb ∈ H01 Ω)
    (hgrad : ∀ i : Fin (n + 1), extendL2 hΩm (Uamb i.succ)
      = extendL2 hNm (mulTest (isTestFn_partialD hξNt i) (HuN.D [ℓ])
        + mulTest hξNt (HuN.D [i, ℓ])))
    (hU0N : extendL2 hΩm (Uamb 0) = extendL2 hNm (mulTest hξNt (HuN.D [ℓ])))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : IsTestFn Ω v) :
    Op.fullBilin Ω ⟨Uamb, hUmem⟩ ⟨hv.testGraph, testGraph_mem_H01 hv⟩
      = cutoffDatumPairing Op hA hbc ξ ℓ (restrictL2 (Ω := N) (extendL2 hΩm (hfk.D [ℓ])))
          HuN v := by
  have hD2 : ∀ i : Fin (n + 1), HasWeakDerivOn N i (HuN.D [ℓ]) (HuN.D [i, ℓ]) :=
    fun i => HuN.D_step i [ℓ] (Nat.succ_lt_succ (Nat.succ_pos k))
  refine (fullBilin_testGraph_eq Op ⟨Uamb, hUmem⟩ hv).trans
    ((setIntegral_blocks_eq Op hΩm hNm hξNt hA hbc (p := HuN.D [ℓ])
      (D2 := fun i => HuN.D [i, ℓ]) hgrad hU0N hD2 hv.1).trans ?_)
  unfold cutoffDatumPairing
  -- The mixed second derivative, swapped into the order the equation names.
  have hsymm : ∀ i : Fin (n + 1),
      (fun x => ϑ x * (HuN.D [i, ℓ] x : ℝ))
        =ᵐ[volume.restrict N] fun x => ϑ x * (HuN.D [ℓ, i] x : ℝ) := by
    intro i
    have h := mulTest_mixed_weakDeriv_comm hNm hϑ
      (HuN.D_step i [] (Nat.succ_pos _)) (HuN.D_step ℓ [] (Nat.succ_pos _))
      (HuN.D_step ℓ [i] (Nat.succ_lt_succ (Nat.succ_pos k)))
      (HuN.D_step i [ℓ] (Nat.succ_lt_succ (Nat.succ_pos k)))
    filter_upwards [mulCutoff_coeFn hϑ (HuN.D [ℓ, i]), mulCutoff_coeFn hϑ (HuN.D [i, ℓ])]
      with x h1 h2
    rw [← h2, ← h, h1]
  have hψ : ∀ j : Fin (n + 1), ∀ x, ϑ x * partialD j (fun y => ξ y * v y) x
      = partialD j (fun y => ξ y * v y) x := fun j =>
    mul_eq_self_of_eqOn_one hϑ_eqOn
      ((tsupport_partialD_subset j _).trans tsupport_mul_subset_left)
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    setIntegral_weight_mul_congr_of_cutoff_ae (hsymm i) (fun x => Op.a x i j) (hψ j)))]
  -- The differentiated equation on the collar, tested against the cut-off test function.
  have hfDf : HasWeakDerivOn N ℓ (restrictL2 (Ω := N) (extendL2 hΩm f))
      (restrictL2 (Ω := N) (extendL2 hΩm (hfk.D [ℓ]))) := by
    have h := hfk.D_step ℓ [] (Nat.succ_pos k)
    rw [hfk.D_nil] at h
    exact h.restrict hΩm hNm hNΩ
  have hLoc : ∀ v' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v' →
      HasCompactSupport v' → tsupport v' ⊆ N →
      (∑ i, ∑ j, ∫ x in N, Op.a x i j * (HuN.D [i] x : ℝ) * partialD j v' x)
        + (∑ i, ∫ x in N, Op.b x i * (HuN.D [i] x : ℝ) * v' x)
        + (∫ x in N, Op.c x * (HuN.D [] x : ℝ) * v' x)
        = ∫ x in N, (restrictL2 (Ω := N) (extendL2 hΩm f) x : ℝ) * v' x := by
    intro v' h1 h2 h3
    simp only [hDu, HuN.D_nil]
    exact localWeakForm_of_fullBilin Op hΩm hNm hNΩ u f hu v' h1 h2 h3
  have hdiffeq := differentiated_weakForm_wkInfty Op hA hbc ℓ (HuN.D [])
    (fun i => HuN.D [i]) (fun m i => HuN.D [m, i])
    (restrictL2 (Ω := N) (extendL2 hΩm f))
    (restrictL2 (Ω := N) (extendL2 hΩm (hfk.D [ℓ])))
    (fun i => HuN.D_step ℓ [i] (Nat.succ_lt_succ (Nat.succ_pos k)))
    (fun i j => HuN.D_step j [i] (Nat.succ_lt_succ (Nat.succ_pos k)))
    (HuN.D_step ℓ [] (Nat.succ_pos _)) hfDf hLoc
    (hξNt.1.mul hv.1) hξNt.2.1.mul_right (tsupport_mul_subset_left.trans hξNt.2.2)
  have hT : ∀ i : Fin (n + 1),
      (∫ x in N, ((hbc.bReg i).D [ℓ] x * (HuN.D [i] x : ℝ)
          + Op.b x i * (HuN.D [ℓ, i] x : ℝ)) * (ξ x * v x))
        = (∫ x in N, ξ x * ((hbc.bReg i).D [ℓ] x * (HuN.D [i] x : ℝ)) * v x)
          + ∫ x in N, ξ x * (Op.b x i * (HuN.D [ℓ, i] x : ℝ)) * v x := fun i =>
    setIntegral_add_weight_mul_cutoff ((hbc.bReg i).measurable_D_singleton ℓ)
      ((hbc.bReg i).ae_abs_D_singleton_le ℓ) (hbc.bReg i).measurable_self
      (hbc.bReg i).ae_abs_le (HuN.D [i]) (HuN.D [ℓ, i]) hξNt.1 hξNt.2.1 hv.1
  have hZ : (∫ x in N, (hbc.cReg.D [ℓ] x * (HuN.D [] x : ℝ) + Op.c x * (HuN.D [ℓ] x : ℝ))
        * (ξ x * v x))
      = (∫ x in N, ξ x * (hbc.cReg.D [ℓ] x * (HuN.D [] x : ℝ)) * v x)
        + ∫ x in N, ξ x * (Op.c x * (HuN.D [ℓ] x : ℝ)) * v x :=
    setIntegral_add_weight_mul_cutoff (hbc.cReg.measurable_D_singleton ℓ)
      (hbc.cReg.ae_abs_D_singleton_le ℓ) hbc.cReg.measurable_self hbc.cReg.ae_abs_le
      (HuN.D []) (HuN.D [ℓ]) hξNt.1 hξNt.2.1 hv.1
  have hAA : ∀ i j : Fin (n + 1),
      (∫ x in N, (hA.D [j, ℓ] i j x * (HuN.D [i] x : ℝ)
          + hA.D [ℓ] i j x * (HuN.D [j, i] x : ℝ)) * (ξ x * v x))
        = (∫ x in N, ξ x * (hA.D [j, ℓ] i j x * (HuN.D [i] x : ℝ)) * v x)
          + ∫ x in N, ξ x * (hA.D [ℓ] i j x * (HuN.D [j, i] x : ℝ)) * v x := fun i j =>
    setIntegral_add_weight_mul_cutoff (hA.D_meas i j [j, ℓ] (Nat.le_add_left 2 k))
      (hA.ess_bdd i j [j, ℓ] (Nat.le_add_left 2 k))
      (hA.D_meas i j [ℓ] (Nat.le_add_left 1 (k + 1)))
      (hA.ess_bdd i j [ℓ] (Nat.le_add_left 1 (k + 1))) (HuN.D [i]) (HuN.D [j, i])
      hξNt.1 hξNt.2.1 hv.1
  have hDf : (∫ x in N, (restrictL2 (Ω := N) (extendL2 hΩm (hfk.D [ℓ])) x : ℝ)
        * (ξ x * v x))
      = ∫ x in N, ξ x * ((1 : ℝ)
          * (restrictL2 (Ω := N) (extendL2 hΩm (hfk.D [ℓ])) x : ℝ)) * v x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hdiffeq]
  simp only [hT, hZ, hAA, hDf]
  simp only [HuN.D_nil, Finset.sum_add_distrib]
  ring

/-- **The cut-off derivative as a weak solution.** An element `U ∈ H₀¹(Ω)` agreeing with
`∂_ℓ u` on `V`, a datum `F ∈ L²(Ω)` with `k` weak derivatives, and the weak formulation
`B[U, w] = ⟪F, w⟫` for every `w ∈ H₀¹(Ω)`, with the norms of `U` and the `H^k` bound on `F`
controlled by `B`. -/
structure CutoffDerivWeakForm (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω)
    (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) (u : H01 Ω) (ℓ : Fin (n + 1)) (k : ℕ)
    (B : ℝ) where
  /-- The cut-off derivative. -/
  U : H01 Ω
  /-- The datum of its equation. -/
  datum : L2D Ω
  /-- The weak derivatives of the datum. -/
  hFk : HasIteratedWeakDerivOn Ω k datum
  /-- `U` agrees with `∂_ℓ u` on `V`. -/
  restrict_eq : restrictL2 (Ω := V) (extendL2 hΩm ((U : H1amb Ω) 0))
    = restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ))
  /-- The weak formulation of the equation of `U`. -/
  weakForm : ∀ w : H01 Ω, Op.fullBilin Ω U w
    = ∫ x in Ω, (datum x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)
  /-- The `H^k` bound on the datum. -/
  bound_F : IteratedL2Bound hFk B
  /-- The bound on the function value of `U`. -/
  bound_U : ‖(U : H1amb Ω) 0‖ ≤ B

/-- **Differentiated equation as a weak formulation for a cutoff derivative.** For a weak
solution `u` of `L u = f` and each direction `ℓ`, there is an element `U ∈ H₀¹(Ω)` agreeing with
`∂_ℓ u` on `V`, a datum `F ∈ L²(Ω)` with `k` weak derivatives, and a weak formulation `B[U, w] =
⟪F, w⟫` for every `w ∈ H₀¹(Ω)`, with both `‖U‖` and the `H^k` bound on `F` controlled by the
data.

This is Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2, step 3 in the
shape the induction consumes, and it is where the analytic content of the step sits.

`U` is `ξ · ∂_ℓ u` for the middle cutoff of a tower for `V ⋐ Ω`, which
`EllipticPdes.Regularity.interior_cutoffGrad_mem_H01` places in `H₀¹(Ω)` and
`EllipticPdes.Regularity.restrictL2_extendL2_mulTest_of_eqOn` makes invisible on `V`. `F` collects
`∂_ℓ f`, the terms of `EllipticPdes.Regularity.differentiated_weakForm_wkInfty` in which the
differentiation lands on a coefficient, and the commutator with `ξ`. Each of those is a
`W^{k,∞}` weight against a derivative of `u` of order at most two, so
`EllipticPdes.Regularity.exists_iteratedWeakDeriv_mul` and
`EllipticPdes.Regularity.HasIteratedWeakDerivOn.sum` assemble the family and its bound, and
`EllipticPdes.Regularity.weakForm_of_testFn` extends the identity from test functions to
`H₀¹(Ω)`.

## Order-`k` conclusion as a hypothesis

`F` pairs second derivatives of `u` against first derivatives of the coefficients, so `F ∈ H^k`
asks for `u ∈ H^{k+2}` on a neighbourhood of `tsupport ξ`, which is the order-`k` conclusion at
that compact set. Evans reaches for it at the same point: the datum (36) of §6.3.1, Theorem 2
contains `D²u`, and its `H^k` bound is read off the inductive hypothesis rather than off the
solution's membership of `H₀¹(Ω)`. Passing `hk` here rather than deriving it is what keeps the
step an induction. -/
theorem exists_cutoffDeriv_weakForm (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsLipCoeff Op.toEllipticCoeff) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (k + 1))
    (hk : InteriorRegularityAt Op hΩm k)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω) (M : ℝ)
      (hfk : HasIteratedWeakDerivOn Ω (k + 1) f), IteratedL2Bound hfk M →
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∀ ℓ : Fin (n + 1),
        Nonempty (CutoffDerivWeakForm Op hΩm V u ℓ k (C * (M + ‖(u : H1amb Ω) 0‖))) := by
  -- The cutoff tower for `V ⋐ Ω`, and an open collar around its middle cutoff.
  obtain ⟨T⟩ : Nonempty (CutoffTower Ω V) :=
    ⟨cutoffTowerOfIsCompactSubsetIsOpen hVc hΩo hVΩ⟩
  obtain ⟨N, hNo, hξN, hNW, hθN⟩ := T.exists_isOpen_collar
  have hWm : MeasurableSet (tsupport T.θ) := T.hθ.2.1.isClosed.measurableSet
  have hWΩ : tsupport T.θ ⊆ Ω := T.hθ.2.2
  have hNm : MeasurableSet N := hNo.measurableSet
  have hNΩ : N ⊆ Ω := hNW.trans hWΩ
  have hξNt : IsTestFn N T.ξ := ⟨T.hξ.1, T.hξ.2.1, hξN⟩
  have hθWt : IsTestFn (tsupport T.θ) T.θ := ⟨T.hθ.1, T.hθ.2.1, subset_rfl⟩
  -- A fourth cutoff, identically one near the middle cutoff and supported in the collar. The
  -- symmetry of the mixed second derivatives is only available after a cutoff, and this is the
  -- one that is invisible against everything the datum pairs with.
  obtain ⟨ϑ, hϑ, hϑ_one, _hϑ_Icc⟩ :=
    exists_isTestFn_one_nhdsSet_of_isCompact T.hξ.2.1 hNo hξN
  have hϑ_eqOn : Set.EqOn ϑ 1 (tsupport T.ξ) := fun x hx => hϑ_one.self_of_nhdsSet x hx
  -- The datum, and the inductive hypothesis at the outer support of the tower.
  obtain ⟨KD, hKD0, hDat⟩ := exists_cutoffDatum Op hNm hNΩ hA hbc hξNt
  obtain ⟨C₁, hC₁0, hIH⟩ := hk T.hθ.2.1 hWΩ
  have hCξ0 : (0 : ℝ) ≤ hξNt.supNorm := hξNt.supNorm_nonneg
  refine ⟨KD * (C₁ + 1) + hξNt.supNorm * C₁,
    add_nonneg (mul_nonneg hKD0 (add_nonneg hC₁0 zero_le_one)) (mul_nonneg hCξ0 hC₁0),
    fun u f M hfk hM hu ℓ => ?_⟩
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg f) hM.norm_le
  have hu00 : (0 : ℝ) ≤ ‖(u : H1amb Ω) 0‖ := norm_nonneg _
  -- The solution's derivatives to order `k + 2` on the outer support, then on the collar.
  obtain ⟨HuW, hHuW⟩ :=
    hIH u f M (hfk.mono (Nat.le_succ k)) (hM.mono_order (Nat.le_succ k)) hu
  obtain ⟨HuN, hHuNbd, hDu⟩ := exists_collarFamily hΩm hWm hNm hNW hθWt hθN
    (fun i => hasWeakDeriv_extendL2_of_mem_H01 hΩm i u.2) HuW hHuW
  -- The cut-off derivative, and the closed form of its gradient.
  obtain ⟨Uamb, hUmem, hU0, hUgrad⟩ := interior_cutoffGrad_mem_H01 Op hΩm hA1 T u f hu ℓ
  have hDgℓ : ∀ i : Fin (n + 1),
      HasWeakDerivOn N i (restrictL2 (Ω := N) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ)))
        (HuN.D [i, ℓ]) := by
    intro i
    have h := HuN.D_step i [ℓ] (Nat.succ_lt_succ (Nat.succ_pos k))
    rwa [hDu ℓ] at h
  have hgrad : ∀ i : Fin (n + 1), extendL2 hΩm (Uamb i.succ)
      = extendL2 hNm (mulTest (isTestFn_partialD hξNt i)
          (restrictL2 (Ω := N) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ)))
        + mulTest hξNt (HuN.D [i, ℓ])) :=
    fun i => extendL2_cutoffGrad_eq hΩm hNm hNΩ T.hξ hξNt ((u : H1amb Ω) ℓ.succ) hUgrad hDgℓ i
  -- The datum's own derivative, cut down to the collar.
  obtain ⟨HDfN, hDfNbd⟩ := exists_restrictFamily hΩm hNm hNΩ (hfk.deriv ℓ) (hM.deriv ℓ)
  -- One bound serving the solution's derivatives and the datum's alike.
  have hMu : (0 : ℝ) ≤ M + ‖(u : H1amb Ω) 0‖ := add_nonneg hM0 hu00
  have hC₁Mu : (0 : ℝ) ≤ C₁ * (M + ‖(u : H1amb Ω) 0‖) := mul_nonneg hC₁0 hMu
  have hle1 : C₁ * (M + ‖(u : H1amb Ω) 0‖) ≤ C₁ * (M + ‖(u : H1amb Ω) 0‖) + M :=
    le_add_of_nonneg_right hM0
  have hle2 : M ≤ C₁ * (M + ‖(u : H1amb Ω) 0‖) + M := le_add_of_nonneg_left hC₁Mu
  obtain ⟨F, HF, hFbd, hFpair⟩ := hDat ℓ _ _ HuN HDfN
    (C₁ * (M + ‖(u : H1amb Ω) 0‖) + M) (hHuNbd.mono_const hle1) (hDfNbd.mono_const hle2)
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  have hDℓnorm : ‖HuN.D [ℓ]‖ ≤ C₁ * (M + ‖(u : H1amb Ω) 0‖) :=
    hHuNbd [ℓ] (Nat.succ_le_succ (Nat.zero_le _))
  refine ⟨⟨⟨Uamb, hUmem⟩, F, HF, ?_, ?_, ?_, ?_⟩⟩
  · -- The cutoff is invisible on the base set, so nothing is lost there.
    change restrictL2 (Ω := V) (extendL2 hΩm (Uamb 0)) = _
    rw [hU0]
    exact restrictL2_extendL2_mulTest_of_eqOn hΩm hVm hVΩ T.hξ T.xi_eqOn_one_base
      ((u : H1amb Ω) ℓ.succ)
  · -- The weak formulation, extended from test functions by density.
    intro w
    refine weakForm_of_testFn Op ⟨Uamb, hUmem⟩ F (fun v hv => ?_) w
    refine (cutoffDeriv_pairing_eq Op hΩm hNm hNΩ hA hbc hξNt hϑ hϑ_eqOn u f hu hfk HuN hDu ℓ
      hUmem (fun i => by rw [hDu ℓ]; exact hgrad i) ?_ hv).trans (hFpair v hv.1 hv.2.1).symm
    rw [hU0, hDu ℓ]
    exact extendL2_mulTest_eq hΩm hNm hNΩ T.hξ hξNt ((u : H1amb Ω) ℓ.succ)
  · -- The datum's bound, in the data.
    refine hFbd.mono_const ?_
    have h1 : C₁ * (M + ‖(u : H1amb Ω) 0‖) + M ≤ (C₁ + 1) * (M + ‖(u : H1amb Ω) 0‖) := by
      linarith only [hu00]
    calc KD * (C₁ * (M + ‖(u : H1amb Ω) 0‖) + M)
        ≤ KD * ((C₁ + 1) * (M + ‖(u : H1amb Ω) 0‖)) := mul_le_mul_of_nonneg_left h1 hKD0
      _ = KD * (C₁ + 1) * (M + ‖(u : H1amb Ω) 0‖) := by ring
      _ ≤ (KD * (C₁ + 1) + hξNt.supNorm * C₁) * (M + ‖(u : H1amb Ω) 0‖) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hCξ0 hC₁0)) hMu
  · -- The cut-off derivative's norm, read on the collar where the cutoff lives.
    change ‖Uamb 0‖ ≤ _
    rw [hU0]
    calc ‖mulTest T.hξ ((u : H1amb Ω) ℓ.succ)‖
        = ‖mulTest hξNt (HuN.D [ℓ])‖ := by
          rw [← norm_extendL2 hΩm, extendL2_mulTest_eq hΩm hNm hNΩ T.hξ hξNt, norm_extendL2,
            hDu ℓ]
      _ ≤ hξNt.supNorm * ‖HuN.D [ℓ]‖ := norm_mulTest_le_supNorm hξNt _
      _ ≤ hξNt.supNorm * (C₁ * (M + ‖(u : H1amb Ω) 0‖)) :=
          mul_le_mul_of_nonneg_left hDℓnorm hCξ0
      _ = hξNt.supNorm * C₁ * (M + ‖(u : H1amb Ω) 0‖) := by ring
      _ ≤ (KD * (C₁ + 1) + hξNt.supNorm * C₁) * (M + ‖(u : H1amb Ω) 0‖) :=
          mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left (mul_nonneg hKD0 (add_nonneg hC₁0 zero_le_one))) hMu

/-- **Induction step.** Differentiating the equation once raises the order-`k` conclusion to
order `k + 1`, under one more order of regularity on every coefficient.

`∂_ℓ u` lies outside `H₀¹(Ω)`: it is a first derivative of an `H₀¹` function and lies only in
`H¹_loc`, so `InteriorRegularityAt`, which quantifies over `H01 Ω`, cannot be applied to it.
`exists_cutoffDeriv_weakForm` supplies the cutoff that can be, together with its datum, and
this step is what remains once that is in hand.

The induction hypothesis returns `k + 2` weak derivatives of the cutoff derivative on `V`,
which `HasIteratedWeakDerivOn.congr` reads as `k + 2` weak derivatives of `∂_ℓ u` itself,
the cutoff being `1` there. Reassembling over `ℓ` through `HasIteratedWeakDerivOn.ofDeriv`
gives `u ∈ H^{k + 3}(V)`.

The constant is `2 C₁ C₀ + 1`, with `C₀` from the datum and `C₁` from the induction
hypothesis. The two summands of `C₀ (M + ‖u‖) + ‖U‖` are each at most `C₀ (M + ‖u‖)`, which
is where the factor of two comes from, and the `+ 1` covers `‖u‖` itself, which the order-zero
entry of the assembled family needs and which no derivative bound supplies. -/
theorem interiorRegularityAt_succ (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsLipCoeff Op.toEllipticCoeff) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2))
    (hbc : IsWkInftyLower Op (k + 1)) (hk : InteriorRegularityAt Op hΩm k) :
    InteriorRegularityAt Op hΩm (k + 1) := by
  classical
  intro V hVc hVΩ
  obtain ⟨C₀, hC₀0, hdat⟩ := exists_cutoffDeriv_weakForm Op hΩm hΩo hA1 hA hbc hk hVc hVΩ
  obtain ⟨C₁, hC₁0, hIH⟩ := hk hVc hVΩ
  refine ⟨2 * C₁ * C₀ + 1, by nlinarith [mul_nonneg hC₁0 hC₀0], fun u f M hfk hM hu => ?_⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM.norm_le
  have hu00 : (0 : ℝ) ≤ ‖(u : H1amb Ω) 0‖ := norm_nonneg _
  -- Each first derivative of `u` has `k + 2` weak derivatives on `V`, read off the induction
  -- hypothesis applied to the cutoff derivative and transported along `ξ ≡ 1`.
  have hstep : ∀ ℓ : Fin (n + 1), ∃ H : HasIteratedWeakDerivOn V (k + 2)
      (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ))),
      IteratedL2Bound H ((2 * C₁ * C₀ + 1) * (M + ‖(u : H1amb Ω) 0‖)) := by
    intro ℓ
    obtain ⟨S⟩ := hdat u f M hfk hM hu ℓ
    obtain ⟨HU, hHU⟩ := hIH S.U S.datum (C₀ * (M + ‖(u : H1amb Ω) 0‖)) S.hFk S.bound_F S.weakForm
    exact ⟨HU.congr S.restrict_eq, hHU.congr.mono_const (by nlinarith [S.bound_U])⟩
  choose H hH using hstep
  refine ⟨HasIteratedWeakDerivOn.ofDeriv
    (fun ℓ => hasWeakDerivOn_of_hasWeakDeriv ℓ
      (hasWeakDeriv_extendL2_of_mem_H01 hΩm ℓ u.2)) H, IteratedL2Bound.ofDeriv ?_ hH⟩
  refine le_trans (norm_restrictL2_le _) ?_
  rw [norm_extendL2]
  have hprod : (0 : ℝ) ≤ 2 * C₁ * C₀ * (M + ‖(u : H1amb Ω) 0‖) :=
    mul_nonneg (mul_nonneg (by linarith) hC₀0) (by linarith)
  nlinarith [hprod]

/-- **Higher interior regularity (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1, Theorem 2, p. 332; Guo, *Partial Differential Equations I and II* (Course Lecture
Notes), Theorem VIII.3.2, p. 65).** Evans states the result for `C^{m+1}` coefficients; the
`W^{k,∞}` hypotheses below are Guo's, and nothing in the differentiated equation asks a
coefficient to be continuous. A weak solution with `W^{k+1,∞}` principal coefficients that are
`W^{1,∞}`, `W^{k,∞}` lower-order coefficients and an `H^k` datum has weak derivatives of every order
up to `k + 2` on each compact `V ⋐ Ω`, bounded by the data with a constant quantified before
the solution and the datum.

The coefficient hypotheses are `W^{k+1,∞}` for `a_{ij}` and `W^{k,∞}` for `b_i, c`, with
`a_{ij}` also `W^{1,∞}` in the pointwise form of `IsLipCoeff` for the base case, which at
`k = 0` is the whole of what the proof reads: `interiorRegularityAt_zero` takes `hA1` alone
and the order-one bundle passed with it goes unused. The step to order `k + 1` differentiates
the equation once: its datum pairs second derivatives of each `a_{ij}` and first derivatives of
`b_i, c` against derivatives of `u` of order at most two, so an `H^k` datum asks
`a_{ij} ∈ W^{k+2,∞}` and `b_i, c ∈ W^{k+1,∞}` (`exists_cutoffDatum`), and the induction
hypothesis at order `k` asks no more. -/
theorem higher_interior_regularity (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsLipCoeff Op.toEllipticCoeff) (k : ℕ)
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 1))
    (hbc : IsWkInftyLower Op k) :
    InteriorRegularityAt Op hΩm k := by
  induction k with
  | zero => exact interiorRegularityAt_zero Op hΩm hΩo hA1
  | succ j ih =>
    exact interiorRegularityAt_succ (k := j) Op hΩm hΩo hA1 hA hbc
      (ih (hA.mono (by omega)) (hbc.mono (by omega)))

end EllipticPdes.Regularity
