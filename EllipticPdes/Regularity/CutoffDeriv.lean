/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.Interior
public import EllipticPdes.Regularity.WeakLimit

/-!
# Membership of a cut-off directional derivative in `H₀¹(Ω)`

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 bootstraps interior
regularity by running the interior `H²` estimate on a derivative `∂_ℓ u` of the weak solution.
`EllipticPdes.Regularity.interior_H2_estimate` quantifies its solution over `H₀¹(Ω)`, and `∂_ℓ
u` has no boundary condition, so the derivative has to be cut off before it can be fed back in.
This file supplies the resulting admissibility statement: for the middle cutoff `ξ` of a cutoff
tower, the product `ξ · ∂_ℓ u` is again an element of `H₀¹(Ω)`.

The route is a weak limit of the discrete family `cutoffMul ξ (diffQuotG ℓ h u)`, every member
of which lies in `H₀¹(Ω)` by `cutoffMul_diffQuotG_mem_H01`. The family is bounded in the graph
norm uniformly in the step: the function coordinate and the second Leibniz summand of each
gradient coordinate are controlled by the first-order bound `‖Dₖ^h u‖ ≤ ‖∂ₖu‖`, and the first
Leibniz summand `ξ · Dₖ^h ∂ᵢu` is exactly what the master energy estimate
`interior_diffQuot_energy_bound` controls. Weak sequential compactness then produces a limit,
which stays in `H₀¹(Ω)` because a closed subspace equals its double orthogonal complement, and
the function coordinate of the limit is pinned by the weak `L²` convergence of the difference
quotients.

## Main declarations

* `inner_mulTest_comm`: multiplication by a cutoff is self-adjoint on `L²(Ω)`.
* `exists_mem_H01_mulTest_gradient`: the cutoff of a directional derivative lies in `H₀¹(Ω)`.
* `interior_cutoffGrad_mem_H01`: the same, together with the weak gradient it has.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Self-adjointness of the cutoff multipliers -/

/-- **Self-adjointness of the cutoff multiplier on `L²(Ω)`.** Both pairings are the integral of the
triple product `∫_Ω η · g · w`. -/
theorem inner_mulTest_comm {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η)
    (g w : L2D Ω) : ⟪mulTest hη g, w⟫ = ⟪g, mulTest hη w⟫ := by
  have key : ∀ p q : L2D Ω, ⟪mulTest hη p, q⟫ = ∫ x in Ω, η x * (p x : ℝ) * (q x : ℝ) :=
    fun p q => inner_mulCoeffL_eq _ _ p q
  rw [key g w, real_inner_comm, key w g]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-! ### Uniform graph-norm bound on the discrete family -/

/-- **Uniform graph-norm bound.** For a weak solution `u` and a cutoff tower `T`, the discrete
family `ξ · Dₗ^h u` is bounded in the ambient graph norm uniformly over all steps below a
positive margin. The function coordinate and the second Leibniz summand of each gradient
coordinate are handled by the first-order bound `‖Dₗ^h u₀‖ ≤ ‖∂ₗu‖`; the first Leibniz summand
`ξ · Dₗ^h ∂ᵢu` is the quantity the master energy estimate
`interior_diffQuot_energy_bound` controls, once the step is admissible for the tower (Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma exists_cutoffMul_diffQuotG_norm_bound (Op : FullEllipticOp d)
    (hΩm : MeasurableSet Ω) (hA : IsLipCoeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin d))} (T : CutoffTower Ω V)
    (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) (ℓ : Fin d) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ h : ℝ, |h| < δ →
      ‖cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))‖ ≤ M := by
  classical
  have hlam : (0 : ℝ) < Op.lam := Op.toEllipticCoeff.lam_pos
  obtain ⟨δ, hδ, -, hS⟩ := T.exists_shiftAdmissible
  obtain ⟨CE, hCE0, hCE⟩ := interior_diffQuot_energy_bound Op hΩm hA T.hξ T.hθ ℓ
  set Dl : ℝ := ‖(u : H1amb Ω) ℓ.succ‖ with hDl
  set Q : ℝ := ‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2 with hQ
  set Btot : ℝ := (T.hξ.supNorm * Dl) ^ 2 + (2 * (2 * CE * Q / Op.lam)
      + 2 * ∑ i : Fin d, (T.hξ.partialSupNorm i * Dl) ^ 2) with hBtot
  refine ⟨δ, hδ, Real.sqrt Btot, fun h hsmall => ?_⟩
  rcases eq_or_ne h 0 with rfl | hh
  · have hzero : diffQuotG ℓ (0 : ℝ) hΩm (u : H1amb Ω) = 0 := by
      refine PiLp.ext fun j => ?_
      rw [diffQuotG_apply]
      simp [diffQuotD]
    rw [hzero, map_zero, norm_zero]
    exact Real.sqrt_nonneg _
  have hmaster := hCE u f hu h hh (hS ℓ h hsmall)
  have hE : ∑ i : Fin d, ‖mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ))‖ ^ 2
      ≤ 2 * CE * Q / Op.lam := by
    simp only [norm_extendL2] at hmaster
    rw [le_div_iff₀ hlam]
    linarith only [hmaster]
  have hD0 : ‖diffQuotD ℓ h hΩm ((u : H1amb Ω) 0)‖ ≤ Dl := norm_diffQuotD_le_grad hΩm ℓ u h
  have hnorm0 : ‖(cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))) 0‖ ≤ T.hξ.supNorm * Dl := by
    rw [cutoffMulOn_apply_zero, diffQuotG_apply]
    exact (norm_mulTest_le_supNorm _ _).trans (mul_le_mul_of_nonneg_left hD0 T.hξ.supNorm_nonneg)
  have hstep : ∀ i : Fin d,
      ‖(cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))) i.succ‖ ^ 2
        ≤ 2 * ‖mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ))‖ ^ 2
          + 2 * (T.hξ.partialSupNorm i * Dl) ^ 2 := by
    intro i
    rw [cutoffMulOn_apply_succ, diffQuotG_apply, diffQuotG_apply]
    have h2 : ‖mulTestPartial T.hξ i (diffQuotD ℓ h hΩm ((u : H1amb Ω) 0))‖
        ≤ T.hξ.partialSupNorm i * Dl :=
      (norm_mulTestPartial_le_supNorm _ _ _).trans
        (mul_le_mul_of_nonneg_left hD0 (T.hξ.partialSupNorm_nonneg i))
    have h3 := (norm_add_le (mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ)))
      (mulTestPartial T.hξ i (diffQuotD ℓ h hΩm ((u : H1amb Ω) 0)))).trans (add_le_add le_rfl h2)
    calc _ ≤ (‖mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ))‖
            + T.hξ.partialSupNorm i * Dl) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ ≤ _ := by
        nlinarith only [sq_nonneg (‖mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ))‖
          - T.hξ.partialSupNorm i * Dl)]
  have hsum : ∑ i : Fin d, ‖(cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))) i.succ‖ ^ 2
      ≤ 2 * (2 * CE * Q / Op.lam) + 2 * ∑ i : Fin d, (T.hξ.partialSupNorm i * Dl) ^ 2 := by
    refine (Finset.sum_le_sum fun i _ => hstep i).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left hE (by norm_num)) le_rfl
  have hsq : ‖cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))‖ ^ 2 ≤ Btot := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, hBtot]
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hnorm0 2) hsum
  exact Real.le_sqrt_of_sq_le hsq

/-! ### Membership of a cut-off directional derivative in `H₀¹(Ω)` -/

/-- **Cutoff of a directional derivative is admissible (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1, Theorem 2, step 3).** For a weak solution `u ∈ H₀¹(Ω)` of
`L u = f` with `W^{1,∞}` principal coefficients and a cutoff tower `T` for `V ⋐ Ω`, the product
`ξ · ∂_ℓ u` of the middle tower cutoff with a directional derivative of `u` is again an element
of `H₀¹(Ω)`: there is `W ∈ H₀¹(Ω)` whose function coordinate is `ξ · ∂_ℓ u`. Since `H₀¹(Ω)`
sits inside the weak-gradient graph space, the gradient coordinates of `W` are then the weak
derivatives of `ξ · ∂_ℓ u`, which `hasWeakDeriv_extendL2_of_mem_H01` reads off.

This is the admissibility step the `H^k` bootstrap needs and that Evans does not: his interior
`H²` theorem asks only `u ∈ H¹(U)`, so he differentiates the equation without cutting off,
whereas `EllipticPdes.Regularity.interior_H2_estimate` quantifies its solution over `H₀¹(Ω)` and
`∂_ℓ u` has no boundary condition.

The proof takes a weak limit of the admissible discrete family `ξ · Dₗ^h u`, whose members lie
in `H₀¹(Ω)` by `cutoffMul_diffQuotG_mem_H01` and which is bounded in the graph norm by
`exists_cutoffMul_diffQuotG_norm_bound`. The limit stays in `H₀¹(Ω)` because a closed subspace
of a Hilbert space equals its double orthogonal complement, and its function coordinate is
pinned by the weak `L²` convergence `Dₗ^h u ⇀ ∂_ℓ u`. -/
theorem exists_mem_H01_mulTest_gradient (Op : FullEllipticOp d)
    (hΩm : MeasurableSet Ω) (hA : IsLipCoeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin d))} (T : CutoffTower Ω V)
    (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) (ℓ : Fin d) :
    ∃ W : H1amb Ω, W ∈ H01 Ω ∧ W 0 = mulTest T.hξ ((u : H1amb Ω) ℓ.succ) := by
  classical
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have htξθ : tsupport T.ξ ⊆ tsupport T.θ := fun x hx =>
    subset_tsupport T.θ (by rw [Function.mem_support, T.theta_eqOn_one hx]; exact one_ne_zero)
  obtain ⟨δ, hδpos, M, hM⟩ := exists_cutoffMul_diffQuotG_norm_bound Op hΩm hA T u f hu ℓ
  set δ₀ : ℝ := min δ T.margin with hδ₀def
  have hδ₀pos : (0 : ℝ) < δ₀ := lt_min hδpos T.hmargin_pos
  -- A step sequence shrinking to zero inside the margin.
  set hs : ℕ → ℝ := fun m => δ₀ / ((m : ℝ) + 2) with hsdef
  have hs_pos : ∀ m, 0 < hs m := by
    intro m; simp only [hsdef]; positivity
  have hs_ne : ∀ m, hs m ≠ 0 := fun m => ne_of_gt (hs_pos m)
  have hs_small : ∀ m, |hs m| < δ₀ := by
    intro m
    rw [abs_of_pos (hs_pos m)]
    simp only [hsdef]
    refine div_lt_self hδ₀pos ?_
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hs_lim : Filter.Tendsto hs Filter.atTop (nhds 0) := by
    simp only [hsdef]
    exact tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right Filter.atTop 2 tendsto_natCast_atTop_atTop)
  -- The admissible discrete family and its uniform bound.
  set Wn : ℕ → H1amb Ω := fun m => cutoffMul T.hξ (diffQuotG ℓ (hs m) hΩm (u : H1amb Ω))
    with hWndef
  have hWn_mem : ∀ m, Wn m ∈ H01 Ω := by
    intro m
    refine cutoffMul_diffQuotG_mem_H01 T.hξ ℓ hΩm ?_ u.2
    intro x hx
    exact T.hmargin ℓ (hs m) (lt_of_lt_of_le (hs_small m) (min_le_right _ _)) x (htξθ hx)
  have hWn_bd : ∀ m, ‖Wn m‖ ≤ M := fun m =>
    hM (hs m) (lt_of_lt_of_le (hs_small m) (min_le_left _ _))
  obtain ⟨W, σ, hσ, _hWnorm, hWweak⟩ := exists_weak_limit_of_bounded_hilbert hWn_bd
  refine ⟨W, ?_, ?_⟩
  · -- The weak limit of a sequence in a closed subspace stays in it.
    have hperp : W ∈ ((H01 Ω)ᗮ)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      have hz : ∀ m : ℕ, ⟪Wn (σ m), y⟫ = (0 : ℝ) := fun m =>
        (Submodule.mem_orthogonal (H01 Ω) y).mp hy _ (hWn_mem (σ m))
      have hlim : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds ⟪W, y⟫) :=
        (hWweak y).congr hz
      rw [real_inner_comm]
      exact tendsto_nhds_unique hlim tendsto_const_nhds
    rwa [Submodule.orthogonal_orthogonal] at hperp
  · -- The function coordinate of the limit is `ξ · ∂_ℓ u`.
    refine ext_inner_left ℝ ?_
    intro z
    have hrw : ∀ X : H1amb Ω, ⟪X, PiLp.single 2 (0 : Fin (d + 1)) z⟫ = ⟪z, X 0⟫ := by
      intro X
      rw [real_inner_comm, inner_single_left]
    have hA1 : Filter.Tendsto (fun m => ⟪z, (Wn (σ m)) 0⟫) Filter.atTop (nhds ⟪z, W 0⟫) := by
      have hbase := hWweak (PiLp.single 2 (0 : Fin (d + 1)) z)
      simpa only [hrw] using hbase
    have hstep : ∀ m : ℕ, ⟪z, (Wn m) 0⟫
        = ⟪diffQuot ℓ (hs m) (extendL2 hΩm ((u : H1amb Ω) 0)),
            extendL2 hΩm (mulTest T.hξ z)⟫ := by
      intro m
      have h0 : (Wn m) 0 = mulTest T.hξ (diffQuotD ℓ (hs m) hΩm ((u : H1amb Ω) 0)) := by
        simp only [hWndef]
        rw [cutoffMulOn_apply_zero, diffQuotG_apply]
      rw [h0, ← inner_mulTest_comm T.hξ z _, ← restrictL2_diffQuot_extendL2,
        ← extendL2_inner_restrictL2]
      exact real_inner_comm _ _
    have hη0 : ∀ m, hs (σ m) ≠ 0 := fun m => hs_ne (σ m)
    have hηlim : Filter.Tendsto (fun m => hs (σ m)) Filter.atTop (nhds 0) :=
      hs_lim.comp hσ.tendsto_atTop
    have hA2 : Filter.Tendsto (fun m => ⟪z, (Wn (σ m)) 0⟫) Filter.atTop
        (nhds ⟪extendL2 hΩm ((u : H1amb Ω) ℓ.succ), extendL2 hΩm (mulTest T.hξ z)⟫) := by
      have hbase := tendsto_inner_diffQuot_of_hasWeakDeriv ℓ
        (hasWeakDeriv_extendL2_of_mem_H01 hΩm ℓ u.2) hη0 hηlim
        (extendL2 hΩm (mulTest T.hξ z))
      exact hbase.congr (fun m => (hstep (σ m)).symm)
    have hval : ⟪extendL2 hΩm ((u : H1amb Ω) ℓ.succ), extendL2 hΩm (mulTest T.hξ z)⟫
        = ⟪z, mulTest T.hξ ((u : H1amb Ω) ℓ.succ)⟫ := by
      rw [extendL2_inner_restrictL2, restrictL2_extendL2,
        ← inner_mulTest_comm T.hξ z ((u : H1amb Ω) ℓ.succ)]
      exact real_inner_comm _ _
    rw [hval] at hA2
    exact tendsto_nhds_unique hA1 hA2

/-- **Cutoff derivative is an `H₀¹` function with its weak gradient (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1, Theorem 2, step 3).** For a weak solution
`u ∈ H₀¹(Ω)` of `L u = f` with `W^{1,∞}` principal coefficients and a cutoff tower `T` for
`V ⋐ Ω`, the product `ξ · ∂_ℓ u` of the middle tower cutoff with a directional derivative of
`u` is an element `W` of `H₀¹(Ω)`, and each gradient coordinate `W_{k+1}` of that element is
the weak `k`-derivative of `ξ · ∂_ℓ u` on the whole space.

This is the admissibility step that lets `EllipticPdes.Regularity.interior_H2_estimate`, whose
solution is quantified over `H₀¹(Ω)`, be applied to a derivative of `u`, which has no boundary
condition of its own. Because `ξ ≡ 1` on `tsupport ζ`, and `ζ ≡ 1` on `V`, the function
coordinate agrees with `∂_ℓ u` on a neighbourhood of `V`, so nothing is lost on the region of
interest. -/
theorem interior_cutoffGrad_mem_H01 (Op : FullEllipticOp d)
    (hΩm : MeasurableSet Ω) (hA : IsLipCoeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin d))} (T : CutoffTower Ω V)
    (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) (ℓ : Fin d) :
    ∃ W : H1amb Ω, W ∈ H01 Ω ∧ W 0 = mulTest T.hξ ((u : H1amb Ω) ℓ.succ)
      ∧ ∀ k : Fin d, HasWeakDeriv k
          (extendL2 hΩm (mulTest T.hξ ((u : H1amb Ω) ℓ.succ))) (extendL2 hΩm (W k.succ)) := by
  obtain ⟨W, hWmem, hW0⟩ := exists_mem_H01_mulTest_gradient Op hΩm hA T u f hu ℓ
  refine ⟨W, hWmem, hW0, fun k => ?_⟩
  rw [← hW0]
  exact hasWeakDeriv_extendL2_of_mem_H01 hΩm k hWmem

/-! ### Triviality of the cutoff on the base set -/

/-- **Middle tower cutoff as `1` on the base set.** `ζ ≡ 1` on `V`, so `V` sits
inside `tsupport ζ`, where `ξ ≡ 1`. -/
theorem CutoffTower.xi_eqOn_one_base {V : Set (EuclideanSpace ℝ (Fin d))}
    (T : CutoffTower Ω V) : Set.EqOn T.ξ 1 V := by
  intro x hx
  refine T.xi_eqOn_one (subset_tsupport T.ζ ?_)
  rw [Function.mem_support, T.zeta_eqOn_one hx]
  exact one_ne_zero

end EllipticPdes.Regularity
