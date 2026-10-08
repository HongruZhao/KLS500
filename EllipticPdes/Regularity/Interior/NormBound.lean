/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.Interior.EnergyBound

/-!
# Uniform interior difference-quotient norm bound

The master energy bound of `EllipticPdes.Regularity.Interior.EnergyBound` is run along a
cutoff tower to produce a bound
on `‖Dₖ^h (ζ ∂ᵢu)‖` that is uniform in the step `h`, which is the hypothesis the weak-limit
converse consumes to produce the second weak derivative.

## Main declarations

* `firstOrder_gradNorm_le`: each gradient component of a weak solution is bounded by the data.
* `interior_diffQuot_norm_bound`: the `h`-uniform bound on the difference quotient of the
  cut-off first derivatives.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
  {ξ θ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### First-order gradient bound -/

/-- **First-order gradient bound.** Each gradient component of a weak solution is bounded in
`L²` by the data: `‖∂ᵢu‖ ≤ √((1 + 4γ) / (2λ)) (‖f‖ + ‖u₀‖)`, where `γ` is the Gårding shift
constant, through which the transport and zeroth-order coefficients enter. This is the
first-order energy estimate `firstOrder_energy_le` combined with the arithmetic-geometric
mean inequality. -/
lemma firstOrder_gradNorm_le (Op : FullEllipticOp d) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) (i : Fin d) :
    ‖(u : H1amb Ω) i.succ‖
      ≤ Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  have hlam : (0 : ℝ) < Op.lam := Op.toEllipticCoeff.lam_pos
  have hγ : (0 : ℝ) ≤ Op.gardingγ := Op.gardingγ_nonneg
  have hfo := firstOrder_energy_le Op u f hu
  have hle : ‖(u : H1amb Ω) i.succ‖ ^ 2 ≤ ∑ j : Fin d, ‖(u : H1amb Ω) j.succ‖ ^ 2 :=
    single_le_sum_fin (fun j => ‖(u : H1amb Ω) j.succ‖ ^ 2) (fun j => sq_nonneg _) i
  set P : ℝ := ‖f‖ + ‖(u : H1amb Ω) 0‖ with hP
  have hP0 : 0 ≤ P := by positivity
  have hamgm : ‖f‖ * ‖(u : H1amb Ω) 0‖ ≤ P ^ 2 / 4 := by
    rw [hP]; nlinarith only [sq_nonneg (‖f‖ - ‖(u : H1amb Ω) 0‖)]
  have hu0P : ‖(u : H1amb Ω) 0‖ ^ 2 ≤ P ^ 2 := by
    rw [hP]; nlinarith only [norm_nonneg f, norm_nonneg ((u : H1amb Ω) 0)]
  refine le_sqrt_mul_of_sq_le (norm_nonneg _) hP0 ?_
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Op.lam)]
  have h1 := mul_le_mul_of_nonneg_left hle (by linarith only [hlam] : (0 : ℝ) ≤ Op.lam / 2)
  have h2 := mul_le_mul_of_nonneg_left hu0P hγ
  nlinarith only [h1, hfo, hamgm, h2]

/-! ### The discrete Leibniz rule for a cutoff -/

/-- **Uniform bound on the difference quotient of a test function.** A test function is
Lipschitz, so its difference quotient is bounded independently of the step `h` and the
direction `k` (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma exists_abs_diffQuot_bound {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : IsTestFn Ω η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (k : Fin d) (h : ℝ), h ≠ 0 → ∀ x,
      |(η (x + hshift k h) - η x) / h| ≤ L := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hη.2.1 hη.1 (by simp)
  exact ⟨K, K.2, fun k h hh x => abs_diffQuot_le_of_lipschitzWith hK k hh x⟩

/-- **Operator bound for the difference quotient.** `‖Dₖʰ g‖ ≤ 2‖g‖/|h|`. -/
private lemma norm_diffQuot_le_two_div (k : Fin d) (h : ℝ) (g : EucL2 d) :
    ‖diffQuot k h g‖ ≤ 2 * ‖g‖ / |h| := by
  have hval : diffQuot k h g = h⁻¹ • (transL2 (hshift k h) g - g) := by
    simp only [diffQuot, _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.id_apply, LinearIsometry.coe_toContinuousLinearMap]
  have hti : ‖transL2 (hshift k h) g - g‖ ≤ 2 * ‖g‖ :=
    (norm_sub_le _ _).trans (by rw [(transL2 (hshift k h)).norm_map]; linarith)
  rw [hval, norm_smul, Real.norm_eq_abs, abs_inv, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hti (by positivity)

/-- **Discrete Leibniz rule for a cutoff.** If `ζ(x + h eₖ) = 0 ∨ ξ x = 1` for every `x` and
the difference quotient of `ζ` is bounded by `L`, then
`Dₖʰ (ζ g) = ζ(· + h eₖ) · (ξ Dₖʰ g) + (Dₖʰ ζ) g`, and so
`‖Dₖʰ (ζ g)‖ ≤ ‖ζ‖∞ ‖ξ Dₖʰ g‖ + L ‖g‖`. -/
private lemma norm_diffQuotD_mulTest_le (hΩm : MeasurableSet Ω) {ζ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hζ : IsTestFn Ω ζ) (hξ : IsTestFn Ω ξ) (k : Fin d) {h : ℝ}
    (hloc : ∀ x, ζ (x + hshift k h) = 0 ∨ ξ x = 1) {L : ℝ}
    (hL : ∀ x, |(ζ (x + hshift k h) - ζ x) / h| ≤ L) (g : L2D Ω) :
    ‖diffQuotD k h hΩm (mulTest hζ g)‖
      ≤ hζ.supNorm * ‖mulTest hξ (diffQuotD k h hΩm g)‖ + L * ‖g‖ := by
  have hqmp : MeasureTheory.QuasiMeasurePreserving (· + hshift k h) volume volume :=
    (measurePreserving_add_right volume (hshift k h)).quasiMeasurePreserving
  -- `extendL2 (ζ g) = ζ · extendL2 g` a.e., and its shift.
  have hζext : (extendL2 hΩm (mulTest hζ g) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume] fun y => ζ y * (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) y := by
    have hg : ∀ᵐ x ∂volume, x ∈ Ω → (mulTest hζ g x : ℝ) = ζ x * (g x : ℝ) :=
      (ae_restrict_iff' hΩm).mp (mulCutoff_coeFn hζ g)
    filter_upwards [coeFn_extendL2 hΩm (mulTest hζ g), coeFn_extendL2 hΩm g, hg] with y h1 h2 h3
    rw [h1, h2]
    by_cases hyΩ : y ∈ Ω
    · rw [Set.indicator_of_mem hyΩ, Set.indicator_of_mem hyΩ]; exact h3 hyΩ
    · rw [Set.indicator_of_notMem hyΩ, Set.indicator_of_notMem hyΩ, mul_zero]
  have hm1 : Measurable (fun y => ζ (y + hshift k h)) :=
    (hζ.continuous.comp (continuous_id.add continuous_const)).measurable
  have hm1b : ∀ᵐ x ∂(volume.restrict Ω), |ζ (x + hshift k h)| ≤ hζ.supNorm :=
    ae_of_all _ fun x => hζ.abs_le_supNorm _
  have hm2 : Measurable (fun y => (ζ (y + hshift k h) - ζ y) / h) :=
    (((hζ.continuous.comp (continuous_id.add continuous_const)).sub hζ.continuous).div_const
      h).measurable
  have hm2b : ∀ᵐ x ∂(volume.restrict Ω), |(ζ (x + hshift k h) - ζ x) / h| ≤ L :=
    ae_of_all _ hL
  have hLeibniz : diffQuotD k h hΩm (mulTest hζ g)
      = mulCoeffL hm1 hm1b (mulTest hξ (diffQuotD k h hΩm g)) + mulCoeffL hm2 hm2b g := by
    apply Lp.ext
    have hζext' : ∀ᵐ x ∂volume, (extendL2 hΩm (mulTest hζ g) : EuclideanSpace ℝ (Fin d) → ℝ)
        (x + hshift k h) = ζ (x + hshift k h)
          * (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h) := hqmp.ae hζext
    filter_upwards [coeFn_diffQuotD k h hΩm (mulTest hζ g),
      mulCoeffL_add_coeFn hm1 hm1b hm2 hm2b (mulTest hξ (diffQuotD k h hΩm g)) g,
      mulCutoff_coeFn hξ (diffQuotD k h hΩm g), coeFn_diffQuotD k h hΩm g,
      ae_restrict_of_ae hζext', mulCutoff_coeFn hζ g] with x hx1 hx2 hx3 hx4 hx5 hx6
    rw [hx1, hx5, hx6, hx2, hx3, hx4]
    rcases hloc x with hz | hone
    · rw [hz]; field_simp; ring
    · rw [hone]; field_simp; ring
  rw [hLeibniz]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mulCoeffL_le hm2 hm2b g))
  exact norm_mulCoeffL_le hm1 hm1b _

/-- The whole-space difference quotient of the extension of `ζ g` has the norm of the interior
difference quotient of `ζ g`, provided the backward shift of `tsupport ζ` stays in `Ω`. -/
private lemma norm_diffQuot_extendL2_mulTest (hΩm : MeasurableSet Ω)
    {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) (k : Fin d) (h : ℝ)
    (hback : ∀ x ∈ tsupport ζ, x + hshift k (-h) ∈ Ω) (g : L2D Ω) :
    ‖diffQuot k h (extendL2 hΩm (mulTest hζ g))‖ = ‖diffQuotD k h hΩm (mulTest hζ g)‖ := by
  have hqmp : MeasureTheory.QuasiMeasurePreserving (· + hshift k h) volume volume :=
    (measurePreserving_add_right volume (hshift k h)).quasiMeasurePreserving
  have hsupp := extendL2_supp_of_ae_restrict hΩm (mulTest hζ g)
    (mulTest_ae_eq_zero_off_tsupport hζ g)
  rw [← extendL2_diffQuotD_eq k h hΩm (mulTest hζ g), norm_extendL2]
  filter_upwards [hqmp.ae hsupp] with x hx hne
  have := hback _ (hx hne)
  rwa [show x + hshift k h + hshift k (-h) = x by rw [hshift_neg]; abel] at this

/-! ### Uniform difference-quotient norm bound for the limit passage -/

/-- **Uniform difference-quotient norm bound (Evans §5.8.2 / §6.3.1).** For a cutoff tower `T`
and each `(k, i)`, there is a constant `Cd` such that every weak solution `u` of
`L u = f` has the whole-space difference quotient of the extension of `ζ · ∂ᵢu` bounded in `L²`
by `M`, uniformly over all steps `h ≠ 0`, with `M ≤ Cd (‖f‖ + ‖u₀‖)`. The step-uniform bound
`M` depends on `u` and `f`; `Cd` is quantified before both, so it depends only on
`λ, Λ, A₁, d, γ, ‖b‖∞, ‖c‖∞` and the tower. For small `h` the discrete
Leibniz split localises the difference quotient onto the master energy bound
(`interior_diffQuot_energy_bound`) and the first-order energy; for large `h` the crude
operator bound `‖Dₖʰ g‖ ≤ 2‖g‖/|h|` closes it. This uniform bound is exactly the hypothesis of
the weak-limit converse `weakDeriv_of_diffQuot_bounded`. -/
theorem interior_diffQuot_norm_bound (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin d))} (T : CutoffTower Ω V) (k i : Fin d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ M : ℝ, 0 ≤ M
        ∧ (∀ h : ℝ, h ≠ 0 →
            ‖diffQuot k h (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ)))‖ ≤ M)
        ∧ M ≤ Cd * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  classical
  have hlam : (0 : ℝ) < Op.lam := Op.toEllipticCoeff.lam_pos
  have hMζ := T.hζ.supNorm_nonneg
  obtain ⟨L, hL0, hLbd⟩ := exists_abs_diffQuot_bound T.hζ
  obtain ⟨δ₁, hδ₁, hδ₁m, hS⟩ := T.exists_shiftAdmissible
  obtain ⟨δ₂, hδ₂, hloc⟩ := T.exists_zeta_shift
  have hζθ : tsupport T.ζ ⊆ tsupport T.θ := fun x hx => by
    have hξ : x ∈ tsupport T.ξ := subset_tsupport T.ξ
      (by rw [Function.mem_support, T.xi_eqOn_one hx]; exact one_ne_zero)
    exact subset_tsupport T.θ (by rw [Function.mem_support, T.theta_eqOn_one hξ]; exact one_ne_zero)
  set δ₀ : ℝ := min δ₁ δ₂ with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hδ₁ hδ₂
  have hδ₀₁ : δ₀ ≤ δ₁ := min_le_left _ _
  have hδ₀₂ : δ₀ ≤ δ₂ := min_le_right _ _
  obtain ⟨CD2, hCD20, hD2⟩ := interior_diffQuot_energy_bound Op hΩm hA T.hξ T.hθ k
  set dcoef : ℝ := Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) with hdcoef
  set CD2coef : ℝ := Real.sqrt (2 * CD2 / Op.lam) with hCD2coef
  have hdcoef0 : 0 ≤ dcoef := Real.sqrt_nonneg _
  have hCD2coef0 : 0 ≤ CD2coef := Real.sqrt_nonneg _
  refine ⟨max (T.hζ.supNorm * CD2coef + L * dcoef) (2 * T.hζ.supNorm * dcoef / δ₀),
    le_max_of_le_left (add_nonneg (mul_nonneg hMζ hCD2coef0) (mul_nonneg hL0 hdcoef0)), ?_⟩
  intro u f hu
  set di : L2D Ω := (u : H1amb Ω) i.succ with hdi_def
  set P : ℝ := ‖f‖ + ‖(u : H1amb Ω) 0‖ with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hQ : ‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2 ≤ P ^ 2 := by
    rw [hP]; nlinarith only [norm_nonneg f, norm_nonneg ((u : H1amb Ω) 0)]
  have hdi : ‖di‖ ≤ dcoef * P := firstOrder_gradNorm_le Op u f hu i
  refine ⟨max (T.hζ.supNorm * (CD2coef * P) + L * ‖di‖) (2 * (T.hζ.supNorm * ‖di‖) / δ₀),
    le_max_of_le_left (add_nonneg (mul_nonneg hMζ (mul_nonneg hCD2coef0 hP0))
      (mul_nonneg hL0 (norm_nonneg _))), ?_, ?_⟩
  · intro h hh
    by_cases hsmall : |h| < δ₀
    · refine le_trans ?_ (le_max_left _ _)
      have hSh := hS k h (hsmall.trans_le hδ₀₁)
      have hB : ‖mulTest T.hξ (diffQuotD k h hΩm di)‖ ≤ CD2coef * P := by
        have hmaster := hD2 u f hu h hh hSh
        have hsingle : ‖mulTest T.hξ (diffQuotD k h hΩm di)‖ ^ 2
            ≤ ∑ j : Fin d, ‖mulTest T.hξ (diffQuotD k h hΩm ((u : H1amb Ω) j.succ))‖ ^ 2 :=
          single_le_sum_fin
            (fun j => ‖mulTest T.hξ (diffQuotD k h hΩm ((u : H1amb Ω) j.succ))‖ ^ 2)
            (fun j => sq_nonneg _) i
        simp only [norm_extendL2] at hmaster
        refine le_sqrt_mul_of_sq_le (norm_nonneg _) hP0 ?_
        rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
        nlinarith only [mul_le_mul_of_nonneg_left hsingle hlam.le, hmaster,
          mul_le_mul_of_nonneg_left hQ hCD20]
      rw [norm_diffQuot_extendL2_mulTest hΩm T.hζ k h
        (fun x hx => hSh.shift_out _ (hζθ hx)) di]
      exact (norm_diffQuotD_mulTest_le hΩm T.hζ T.hξ k (hloc k h (hsmall.trans_le hδ₀₂))
        (hLbd k h hh) di).trans (add_le_add (mul_le_mul_of_nonneg_left hB hMζ) le_rfl)
    · refine le_trans ?_ (le_max_right _ _)
      have hge : δ₀ ≤ |h| := not_lt.mp hsmall
      refine (norm_diffQuot_le_two_div k h _).trans ?_
      rw [norm_extendL2]
      have hg : ‖mulTest T.hζ di‖ ≤ T.hζ.supNorm * ‖di‖ := norm_mulTest_le_supNorm _ _
      calc 2 * ‖mulTest T.hζ di‖ / |h| ≤ 2 * (T.hζ.supNorm * ‖di‖) / |h| := by gcongr
        _ ≤ 2 * (T.hζ.supNorm * ‖di‖) / δ₀ := by gcongr
  · apply max_le
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) hP0)
      nlinarith only [mul_le_mul_of_nonneg_left hdi hL0]
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) hP0)
      calc 2 * (T.hζ.supNorm * ‖di‖) / δ₀ ≤ 2 * (T.hζ.supNorm * (dcoef * P)) / δ₀ := by gcongr
        _ = _ := by ring

end EllipticPdes.Regularity
