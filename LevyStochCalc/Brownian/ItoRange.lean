/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoIntegrandComplete

/-!
# The range of the Itô integral on a horizon

An integrand supported in `[0, T]`, jointly and progressively measurable and of finite energy,
is admissible for the Itô integral up to `T`. Such integrands are closed under sums and scalar
multiples, and the integral is additive and homogeneous on them, so their integrals form a
submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence of integrands to
an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- An integrand admissible for the Itô integral, supported in the horizon `[0, T]`. -/
structure HorizonIntegrand (P : Measure Ω) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) where
  /-- The underlying process. -/
  toFun : Ω → ℝ → ℝ
  /-- Joint measurability in the sample point and the time. -/
  measurable_uncurry : Measurable (Function.uncurry toFun)
  /-- Progressive measurability for the filtration. -/
  progressive : Probability.ProgressivelyMeasurable ℱ toFun
  /-- The process vanishes off the horizon. -/
  vanishing : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → toFun ω s = 0
  /-- The energy on the horizon is finite. -/
  energy_ne_top : energy P T toFun ≠ ⊤

section Energy

variable {T : ℝ}

/-- A deterministic constant process is progressively measurable. -/
theorem progressivelyMeasurable_const (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (c : ℝ) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => c) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  exact Measurable.stronglyMeasurable
    ((measurable_const.indicator measurableSet_Iic).comp measurable_snd)

omit [IsProbabilityMeasure P] in
/-- An integrand dominated by twice the sum of two finite energies has finite energy. -/
theorem energy_ne_top_of_bound {H₁ H₂ K : Ω → ℝ → ℝ}
    (hbound : ∀ ω s, (‖K ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2))
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (h1 : energy P T H₁ ≠ ⊤) (h2 : energy P T H₂ ≠ ⊤) :
    energy P T K ≠ ⊤ := by
  have e1 := measurable_energyDensity hm₁ T
  have e2 := measurable_energyDensity hm₂ T
  have hstep : energy P T K
      ≤ 2 * energy P T H₁ + 2 * energy P T H₂ := by
    rw [energy, energy, energy, ← lintegral_const_mul 2 e1, ← lintegral_const_mul 2 e2,
      ← lintegral_add_left (e1.const_mul 2)]
    refine lintegral_mono fun ω => ?_
    have h1' : Measurable fun s => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnnorm.comp (hm₁.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    have h2' : Measurable fun s => (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnnorm.comp (hm₂.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    rw [← lintegral_const_mul 2 h1', ← lintegral_const_mul 2 h2',
      ← lintegral_add_left (h1'.const_mul 2)]
    refine lintegral_mono fun s => ?_
    calc (‖K ω s‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) := hbound ω s
      _ = 2 * (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 := by ring
  refine ne_top_of_le_ne_top ?_ hstep
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (by simp) h1, ENNReal.mul_ne_top (by simp) h2⟩

omit [IsProbabilityMeasure P] in
/-- The energy of a sum is finite when both energies are. -/
theorem energy_add_ne_top {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (h1 : energy P T H₁ ≠ ⊤) (h2 : energy P T H₂ ≠ ⊤) :
    energy P T (fun ω s => H₁ ω s + H₂ ω s) ≠ ⊤ :=
  energy_ne_top_of_bound (fun _ _ => sq_nnnorm_add_le_two_mul _ _) hm₁ hm₂ h1 h2

omit [IsProbabilityMeasure P] in
/-- The energy of a scalar multiple is finite when the energy is. -/
theorem energy_const_mul_ne_top {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (h : energy P T H ≠ ⊤) (c : ℝ) :
    energy P T (fun ω s => c * H ω s) ≠ ⊤ := by
  rw [energy, lintegral_energy_const_mul hm c T]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h

end Energy

namespace HorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

omit [IsProbabilityMeasure P] in
/-- The global square-integrability the Itô integral asks for. -/
theorem sq_int_global (G : HorizonIntegrand P ℱ T) :
    ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G.toFun ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun T' _ =>
  lt_of_le_of_lt (energy_le_of_vanishing G.vanishing T')
    (lt_top_iff_ne_top.mpr G.energy_ne_top)

/-- The Itô integral of an admissible integrand over the horizon. -/
noncomputable def integral (W : LevyStochCalc.Brownian.BrownianMotion P)
    (hℱ : IsBrownianFiltration W ℱ) (G : HorizonIntegrand P ℱ T) : Ω → ℝ :=
  stochasticIntegralBrownian W ℱ hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global T

/-- The zero integrand. -/
def zero (P : Measure Ω) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) :
    HorizonIntegrand P ℱ T where
  toFun := fun _ _ => 0
  measurable_uncurry := measurable_const
  progressive := progressivelyMeasurable_const ℱ 0
  vanishing := fun _ _ _ => rfl
  energy_ne_top := by simp [energy]

/-- The sum of two admissible integrands. -/
noncomputable def add (G₁ G₂ : HorizonIntegrand P ℱ T) : HorizonIntegrand P ℱ T where
  toFun := fun ω s => G₁.toFun ω s + G₂.toFun ω s
  measurable_uncurry := G₁.measurable_uncurry.add G₂.measurable_uncurry
  progressive := G₁.progressive.add G₂.progressive
  vanishing := fun ω s hs => by rw [G₁.vanishing ω s hs, G₂.vanishing ω s hs, add_zero]
  energy_ne_top := energy_add_ne_top G₁.measurable_uncurry G₂.measurable_uncurry
    G₁.energy_ne_top G₂.energy_ne_top

/-- A scalar multiple of an admissible integrand. -/
noncomputable def smul (c : ℝ) (G : HorizonIntegrand P ℱ T) : HorizonIntegrand P ℱ T where
  toFun := fun ω s => c * G.toFun ω s
  measurable_uncurry := measurable_const.mul G.measurable_uncurry
  progressive := Probability.ProgressivelyMeasurable.mul
    (progressivelyMeasurable_const ℱ c) G.progressive
  vanishing := fun ω s hs => by rw [G.vanishing ω s hs, mul_zero]
  energy_ne_top := energy_const_mul_ne_top G.measurable_uncurry G.energy_ne_top c

section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

/-- The Itô integral of an admissible integrand is square integrable. -/
theorem memLp (G : HorizonIntegrand P ℱ T) : MemLp (G.integral W hℱ) 2 P :=
  stochasticIntegralBrownian_memLp W ℱ hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global T

/-- The isometry of differences in terms of the energy. -/
theorem lintegral_sq_integral_sub (hT : 0 < T) (G₁ G₂ : HorizonIntegrand P ℱ T) :
    ∫⁻ ω, (‖G₁.integral W hℱ ω - G₂.integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = energy P T (fun ω s => G₁.toFun ω s - G₂.toFun ω s) :=
  isometry_diff_stochasticIntegralBrownian W ℱ hℱ G₁.toFun G₂.toFun
    G₁.measurable_uncurry G₂.measurable_uncurry G₁.progressive G₂.progressive
    G₁.sq_int_global G₂.sq_int_global hT

/-- The integral of the zero integrand vanishes. -/
theorem integral_zero (hT : 0 < T) :
    (HorizonIntegrand.zero P ℱ T).integral W hℱ =ᵐ[P] 0 := by
  have hiso := isometry_stochasticIntegralBrownian W ℱ hℱ
    (HorizonIntegrand.zero P ℱ T).toFun (HorizonIntegrand.zero P ℱ T).measurable_uncurry
    (HorizonIntegrand.zero P ℱ T).progressive (HorizonIntegrand.zero P ℱ T).sq_int_global hT
  have h0 : energy P T (HorizonIntegrand.zero P ℱ T).toFun = 0 := by
    simp [energy, HorizonIntegrand.zero]
  have hzero : ∫⁻ ω, (‖(HorizonIntegrand.zero P ℱ T).integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 :=
    hiso.trans h0
  have hae : AEMeasurable
      (fun ω => (‖(HorizonIntegrand.zero P ℱ T).integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2) P :=
    ((((memLp W hℱ (HorizonIntegrand.zero P ℱ T)).aestronglyMeasurable.aemeasurable).nnnorm
      ).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hzero] with ω hω
  have h2 : (‖(HorizonIntegrand.zero P ℱ T).integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2 = 0 := hω
  have h3 : (‖(HorizonIntegrand.zero P ℱ T).integral W hℱ ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
  simpa using h3

/-- Additivity of the integral on admissible integrands. -/
theorem integral_add (hT : 0 < T) (G₁ G₂ : HorizonIntegrand P ℱ T) :
    (G₁.add G₂).integral W hℱ
      =ᵐ[P] fun ω => G₁.integral W hℱ ω + G₂.integral W hℱ ω :=
  stochasticIntegralBrownian_add W ℱ hℱ G₁.measurable_uncurry G₂.measurable_uncurry
    G₁.progressive G₂.progressive G₁.sq_int_global G₂.sq_int_global
    (G₁.add G₂).measurable_uncurry (G₁.add G₂).progressive (G₁.add G₂).sq_int_global hT

/-- Homogeneity of the integral on admissible integrands. -/
theorem integral_smul (hT : 0 < T) (c : ℝ) (G : HorizonIntegrand P ℱ T) :
    (G.smul c).integral W hℱ =ᵐ[P] fun ω => c * G.integral W hℱ ω :=
  stochasticIntegralBrownian_const_mul W ℱ hℱ G.measurable_uncurry G.progressive
    G.sq_int_global c (G.smul c).measurable_uncurry (G.smul c).progressive
    (G.smul c).sq_int_global hT

/-- The Itô integral over the horizon has mean zero. -/
theorem integral_mean_zero (hT : 0 ≤ T) (G : HorizonIntegrand P ℱ T) :
    ∫ ω, G.integral W hℱ ω ∂P = 0 := by
  obtain ⟨F, hF⟩ := martingale_stochasticIntegral W ℱ hℱ G.toFun G.measurable_uncurry
    G.progressive G.sq_int_global
  haveI : SigmaFinite (P.trim (F.le 0)) := (isFiniteMeasure_trim (F.le 0)).toSigmaFinite
  have hcond := hF.2 0 T hT
  have hz : stochasticIntegral W ℱ hℱ G.toFun G.measurable_uncurry G.progressive
      G.sq_int_global 0 =ᵐ[P] 0 :=
    stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ G.toFun G.measurable_uncurry
      G.progressive G.sq_int_global le_rfl
  calc ∫ ω, G.integral W hℱ ω ∂P
      = ∫ ω, condExp (F 0) P (fun x => stochasticIntegral W ℱ hℱ G.toFun
          G.measurable_uncurry G.progressive G.sq_int_global T x) ω ∂P :=
        (integral_condExp (F.le 0)).symm
    _ = ∫ ω, stochasticIntegral W ℱ hℱ G.toFun G.measurable_uncurry G.progressive
          G.sq_int_global 0 ω ∂P := integral_congr_ae hcond
    _ = 0 := by rw [integral_congr_ae hz]; simp

end Integral


end HorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

/-- The Itô integrals of admissible integrands, as a submodule of `L²`. -/
noncomputable def itoRange (hT : 0 < T) : Submodule ℝ (Lp ℝ 2 P) where
  carrier := {u : Lp ℝ 2 P | ∃ G : HorizonIntegrand P ℱ T, (u : Ω → ℝ) =ᵐ[P] G.integral W hℱ}
  zero_mem' := by
    refine ⟨HorizonIntegrand.zero P ℱ T, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 P, HorizonIntegrand.integral_zero W hℱ hT] with ω h1 h2
    rw [h1, h2]
  add_mem' := by
    intro u v hu hv
    obtain ⟨G₁, h₁⟩ := hu
    obtain ⟨G₂, h₂⟩ := hv
    refine ⟨G₁.add G₂, ?_⟩
    filter_upwards [Lp.coeFn_add u v, h₁, h₂, HorizonIntegrand.integral_add W hℱ hT G₁ G₂]
      with ω e1 e2 e3 e4
    rw [e1, Pi.add_apply, e2, e3, e4]
  smul_mem' := by
    intro c u hu
    obtain ⟨G, h⟩ := hu
    refine ⟨G.smul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c u, h, HorizonIntegrand.integral_smul W hℱ hT c G]
      with ω e1 e2 e3
    rw [e1, Pi.smul_apply, e2, e3, smul_eq_mul]

/-- The `L²`-distance between two Itô integrals is the energy of the difference. -/
theorem energy_eq_edist_sq (hT : 0 < T) {u v : Lp ℝ 2 P} {G₁ G₂ : HorizonIntegrand P ℱ T}
    (h₁ : (u : Ω → ℝ) =ᵐ[P] G₁.integral W hℱ) (h₂ : (v : Ω → ℝ) =ᵐ[P] G₂.integral W hℱ) :
    energy P T (fun ω s => G₁.toFun ω s - G₂.toFun ω s) = edist u v ^ 2 := by
  rw [Lp.edist_def, eLpNorm_sq_eq_lintegral _ ((u : Ω → ℝ) - (v : Ω → ℝ))
    ((Lp.aestronglyMeasurable u).sub (Lp.aestronglyMeasurable v)),
    ← HorizonIntegrand.lintegral_sq_integral_sub W hℱ hT G₁ G₂]
  refine lintegral_congr_ae ?_
  filter_upwards [h₁, h₂] with ω e1 e2
  simp only [Pi.sub_apply]
  rw [e1, e2]

/-- **The Itô integrals form a closed submodule of `L²`.** -/
theorem isClosed_itoRange (hT : 0 < T) :
    IsClosed ((itoRange W hℱ hT : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) := by
  refine IsSeqClosed.isClosed ?_
  intro u v hu huv
  choose G hG using hu
  have hCau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      energy P T (fun ω s => (G m).toFun ω s - (G n).toFun ω s) < ε := by
    intro ε hε
    have hcs : CauchySeq u := huv.cauchySeq
    rw [EMetric.cauchySeq_iff] at hcs
    obtain ⟨N, hN⟩ := hcs (min ε 1) (lt_min hε one_pos)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [energy_eq_edist_sq W hℱ hT (hG m) (hG n)]
    refine lt_of_lt_of_le (ENNReal.pow_lt_pow_left (by norm_num) (hN m hm n hn)) ?_
    calc (min ε 1) ^ 2 = min ε 1 * min ε 1 := sq _
      _ ≤ min ε 1 * 1 := mul_le_mul_right (min_le_right ε 1) _
      _ = min ε 1 := mul_one _
      _ ≤ ε := min_le_left ε 1
  obtain ⟨K, hKm, hKp, hKz, hKfin, hKtend⟩ :=
    exists_progressive_energy_limit ℱ (fun n => (G n).measurable_uncurry)
      (fun n => (G n).progressive) (fun n => (G n).vanishing)
      (fun n => (G n).energy_ne_top) hCau
  obtain ⟨tgt, htgt⟩ : ∃ t : Lp ℝ 2 P,
      (t : Ω → ℝ) =ᵐ[P] (⟨K, hKm, hKp, hKz, hKfin⟩ : HorizonIntegrand P ℱ T).integral W hℱ :=
    ⟨_, MemLp.coeFn_toLp (HorizonIntegrand.memLp W hℱ _)⟩
  have hlim : Tendsto u atTop (𝓝 tgt) := by
    rw [EMetric.tendsto_atTop]
    intro ε hε
    have hpos : (0 : ℝ≥0∞) < (min ε 1) ^ 2 :=
      zero_lt_iff.mpr (pow_ne_zero 2 (ne_of_gt (lt_min hε one_pos)))
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hKtend.eventually_lt_const hpos)
    refine ⟨N, fun n hn => ?_⟩
    have hedist : energy P T (fun ω s => (G n).toFun ω s - K ω s) = edist (u n) tgt ^ 2 :=
      energy_eq_edist_sq W hℱ hT (hG n) htgt
    have hlt : edist (u n) tgt ^ 2 < (min ε 1) ^ 2 := hedist ▸ hN n hn
    rcases lt_or_ge (edist (u n) tgt) (min ε 1) with h | h
    · exact lt_of_lt_of_le h (min_le_left ε 1)
    · exact absurd hlt (not_lt.mpr (pow_le_pow_left' h 2))
  refine ⟨⟨K, hKm, hKp, hKz, hKfin⟩, ?_⟩
  rw [tendsto_nhds_unique huv hlim]
  exact htgt

end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

/-- The Itô integral over the horizon is measurable before `T`. -/
theorem HorizonIntegrand.aestronglyMeasurable (G : HorizonIntegrand P ℱ T) :
    AEStronglyMeasurable[ℱ T] (G.integral W hℱ) P :=
  stochasticIntegralBrownian_aesm W ℱ hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global T |>.congr
    (stochasticIntegralBrownian_ae_eq W ℱ hℱ G.toFun G.measurable_uncurry G.progressive
      G.sq_int_global T).symm

/-- **The representation half of the Brownian predictable representation property.** If the only
square-integrable weight of mean zero, measurable before `T` and orthogonal to every Itô integral,
is the zero weight, then every square-integrable weight of mean zero that is measurable before `T`
is an Itô integral. -/
theorem exists_horizonIntegrand_of_mean_zero (hT : 0 < T)
    (hsep : ∀ r : Ω → ℝ, MemLp r 2 P → AEStronglyMeasurable[ℱ T] r P →
      (∫ ω, r ω ∂P = 0) →
      (∀ G : HorizonIntegrand P ℱ T, ∫ ω, r ω * G.integral W hℱ ω ∂P = 0) → r =ᵐ[P] 0)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ G : HorizonIntegrand P ℱ T, Z =ᵐ[P] G.integral W hℱ := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  haveI hcl : IsClosed ((itoRange W hℱ hT : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
    isClosed_itoRange W hℱ hT
  haveI : CompleteSpace (itoRange W hℱ hT) := hcl.completeSpace_coe
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (itoRange W hℱ hT).exists_add_mem_mem_orthogonal (hZ2.toLp Z)
  obtain ⟨G₀, hG₀⟩ := hy
  have hsplit : Z =ᵐ[P] fun ω => G₀.integral W hℱ ω + (z : Ω → ℝ) ω := by
    filter_upwards [hZ2.coeFn_toLp, Lp.coeFn_add y z, hG₀] with ω e1 e2 e3
    rw [← e1, hyz, e2, Pi.add_apply, e3]
  have hzmem : MemLp (z : Ω → ℝ) 2 P := Lp.memLp z
  have hzmeas : AEStronglyMeasurable[ℱ T] (z : Ω → ℝ) P := by
    have hd : (z : Ω → ℝ) =ᵐ[P] fun ω => Z ω - G₀.integral W hℱ ω := by
      filter_upwards [hsplit] with ω e1
      rw [e1]; ring
    exact (hZm.sub (HorizonIntegrand.aestronglyMeasurable W hℱ G₀)).congr hd.symm
  have hymean : ∫ ω, G₀.integral W hℱ ω ∂P = 0 :=
    HorizonIntegrand.integral_mean_zero W hℱ hT.le G₀
  have hzint : Integrable (z : Ω → ℝ) P := hzmem.integrable (by norm_num)
  have hyint : Integrable (G₀.integral W hℱ) P :=
    (HorizonIntegrand.memLp W hℱ G₀).integrable (by norm_num)
  have hzmean : ∫ ω, (z : Ω → ℝ) ω ∂P = 0 := by
    have := integral_congr_ae (μ := P) hsplit
    rw [integral_add hyint hzint, hymean, zero_add] at this
    rw [← this, hZ0]
  have hzperp : ∀ G : HorizonIntegrand P ℱ T,
      ∫ ω, (z : Ω → ℝ) ω * G.integral W hℱ ω ∂P = 0 := by
    intro G
    have hmem : (HorizonIntegrand.memLp W hℱ G).toLp (G.integral W hℱ)
        ∈ itoRange W hℱ hT := ⟨G, MemLp.coeFn_toLp _⟩
    have hinner := (Submodule.mem_orthogonal _ z).mp hz _ hmem
    rw [L2.inner_def] at hinner
    have hcongr : ∫ ω, (((HorizonIntegrand.memLp W hℱ G).toLp (G.integral W hℱ) :
          Ω → ℝ) ω * (z : Ω → ℝ) ω) ∂P = ∫ ω, G.integral W hℱ ω * (z : Ω → ℝ) ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (HorizonIntegrand.memLp W hℱ G)] with ω e1
      rw [e1]
    have hrw : ∫ ω, G.integral W hℱ ω * (z : Ω → ℝ) ω ∂P = 0 := by
      rw [← hcongr, ← hinner]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        simp [RCLike.inner_apply, mul_comm])
    rw [← hrw]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have hzzero := hsep (z : Ω → ℝ) hzmem hzmeas hzmean hzperp
  refine ⟨G₀, ?_⟩
  filter_upwards [hsplit, hzzero] with ω e1 e2
  rw [e1, e2]
  simp

end Representation

end LevyStochCalc.Brownian.Ito
