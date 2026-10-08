/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedLinear
import LevyStochCalc.Brownian.ItoRange

/-!
# The range of the compensated Poisson integral on a horizon

A marked integrand supported in `[0, T]`, jointly and progressively measurable and of finite
energy, is admissible for the compensated integral up to `T`. Such integrands are closed under
sums and scalar multiples, and the integral is additive and homogeneous on them, so their
integrals form a submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence
of integrands to an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Progressive

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- The zero marked process is progressively measurable. -/
theorem markedProgressivelyMeasurable_zero (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Probability.MarkedProgressivelyMeasurable (E := E) ℱ
      fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ) := by
  intro t
  have hrw : (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun _ => (0 : ℝ)) p.2.1)
      = fun _ : Ω × ℝ × E => (0 : ℝ) := by
    funext p
    simp
  rw [hrw]
  exact stronglyMeasurable_const

/-- Sums of progressively measurable marked processes are progressively measurable. -/
theorem markedProgressivelyMeasurable_add {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (h₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (h₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => φ₁ ω s e + φ₂ ω s e := by
  intro t
  have hrw : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => φ₁ p.1 s p.2.2 + φ₂ p.1 s p.2.2) p.2.1)
      = fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => φ₁ p.1 s p.2.2) p.2.1
        + (Set.Iic t).indicator (fun s => φ₂ p.1 s p.2.2) p.2.1 := by
    funext p
    by_cases hp : p.2.1 ∈ Set.Iic t
    · simp [Set.indicator_of_mem hp]
    · simp [Set.indicator_of_notMem hp]
  rw [hrw]
  exact (h₁ t).add (h₂ t)

/-- Scalar multiples of progressively measurable marked processes are progressively
measurable. -/
theorem markedProgressivelyMeasurable_const_mul {φ : Ω → ℝ → E → ℝ}
    (h : Probability.MarkedProgressivelyMeasurable ℱ φ) (c : ℝ) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => c * φ ω s e :=
  (continuous_const.mul continuous_id).comp_markedProgressivelyMeasurable (mul_zero c) h

end Progressive

/-- A marked integrand admissible for the compensated integral, supported in the horizon
`[0, T]`. -/
structure MarkedHorizonIntegrand (P : Measure Ω) (ν : Measure E)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) where
  /-- The underlying marked process. -/
  toFun : Ω → ℝ → E → ℝ
  /-- Joint measurability in the sample point, the time and the mark. -/
  measurable_uncurry : Measurable fun p : Ω × ℝ × E => toFun p.1 p.2.1 p.2.2
  /-- Progressive measurability for the filtration. -/
  progressive : Probability.MarkedProgressivelyMeasurable ℱ toFun
  /-- The process vanishes off the horizon. -/
  vanishing : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → toFun ω s e = 0
  /-- The energy on the horizon is finite. -/
  energy_ne_top : markedEnergy P ν T toFun ≠ ⊤

namespace MarkedHorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The global square-integrability the compensated integral asks for. -/
theorem sq_int_global (G : MarkedHorizonIntegrand P ν ℱ T) :
    ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖G.toFun ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := fun T' _ =>
  lt_of_le_of_lt (markedEnergy_le_of_vanishing G.vanishing T')
    (lt_top_iff_ne_top.mpr G.energy_ne_top)

/-- The compensated integral of an admissible marked integrand over the horizon. -/
noncomputable def integral (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (G : MarkedHorizonIntegrand P ν ℱ T) : Ω → ℝ :=
  stochasticIntegral N ℱ hℱ G.toFun G.measurable_uncurry G.progressive G.sq_int_global T

/-- The zero integrand. -/
def zero (P : Measure Ω) (ν : Measure E) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) :
    MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun _ _ _ => 0
  measurable_uncurry := measurable_const
  progressive := markedProgressivelyMeasurable_zero ℱ
  vanishing := fun _ _ _ _ => rfl
  energy_ne_top := by simp [markedEnergy]

/-- The sum of two admissible marked integrands. -/
noncomputable def add (G₁ G₂ : MarkedHorizonIntegrand P ν ℱ T) :
    MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun ω s e => G₁.toFun ω s e + G₂.toFun ω s e
  measurable_uncurry := G₁.measurable_uncurry.add G₂.measurable_uncurry
  progressive := markedProgressivelyMeasurable_add G₁.progressive G₂.progressive
  vanishing := fun ω s e hs => by rw [G₁.vanishing ω s e hs, G₂.vanishing ω s e hs, add_zero]
  energy_ne_top := markedEnergy_add_ne_top G₁.measurable_uncurry G₂.measurable_uncurry
    G₁.energy_ne_top G₂.energy_ne_top

/-- A scalar multiple of an admissible marked integrand. -/
noncomputable def smul (c : ℝ) (G : MarkedHorizonIntegrand P ν ℱ T) :
    MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun ω s e => c * G.toFun ω s e
  measurable_uncurry := measurable_const.mul G.measurable_uncurry
  progressive := markedProgressivelyMeasurable_const_mul G.progressive c
  vanishing := fun ω s e hs => by rw [G.vanishing ω s e hs, mul_zero]
  energy_ne_top := markedEnergy_const_mul_ne_top G.measurable_uncurry G.energy_ne_top c

section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

/-- The compensated integral of an admissible marked integrand is square integrable. -/
theorem memLp (G : MarkedHorizonIntegrand P ν ℱ T) : MemLp (G.integral N hℱ) 2 P :=
  stochasticIntegral_memLp N ℱ hℱ G.toFun G.measurable_uncurry G.progressive G.sq_int_global T

/-- The isometry of differences in terms of the marked energy. -/
theorem lintegral_sq_integral_sub (hT : 0 < T) (G₁ G₂ : MarkedHorizonIntegrand P ν ℱ T) :
    ∫⁻ ω, (‖G₁.integral N hℱ ω - G₂.integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = markedEnergy P ν T fun ω s e => G₁.toFun ω s e - G₂.toFun ω s e :=
  itoIsometry_diff_compensated N ℱ hℱ G₁.toFun G₂.toFun G₁.measurable_uncurry
    G₂.measurable_uncurry G₁.progressive G₂.progressive G₁.sq_int_global G₂.sq_int_global T hT

/-- The integral of the zero integrand vanishes. -/
theorem integral_zero (hT : 0 < T) :
    (MarkedHorizonIntegrand.zero P ν ℱ T).integral N hℱ =ᵐ[P] 0 := by
  have hiso := isometry_stochasticIntegral N ℱ hℱ (MarkedHorizonIntegrand.zero P ν ℱ T).toFun
    (MarkedHorizonIntegrand.zero P ν ℱ T).measurable_uncurry
    (MarkedHorizonIntegrand.zero P ν ℱ T).progressive
    (MarkedHorizonIntegrand.zero P ν ℱ T).sq_int_global T hT
  have h0 : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖(MarkedHorizonIntegrand.zero P ν ℱ T).toFun ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) = 0 := by
    simp [MarkedHorizonIntegrand.zero]
  have hzero : ∫⁻ ω,
      (‖(MarkedHorizonIntegrand.zero P ν ℱ T).integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 :=
    hiso.trans h0
  have hae : AEMeasurable
      (fun ω => (‖(MarkedHorizonIntegrand.zero P ν ℱ T).integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2) P :=
    ((((memLp N hℱ (MarkedHorizonIntegrand.zero P ν ℱ T)).aestronglyMeasurable.aemeasurable
      ).nnnorm).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hzero] with ω hω
  have h2 : (‖(MarkedHorizonIntegrand.zero P ν ℱ T).integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2 = 0 := hω
  have h3 : (‖(MarkedHorizonIntegrand.zero P ν ℱ T).integral N hℱ ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
  simpa using h3

/-- Additivity of the integral on admissible marked integrands. -/
theorem integral_add (hT : 0 < T) (G₁ G₂ : MarkedHorizonIntegrand P ν ℱ T) :
    (G₁.add G₂).integral N hℱ =ᵐ[P] fun ω => G₁.integral N hℱ ω + G₂.integral N hℱ ω :=
  stochasticIntegral_add N ℱ hℱ G₁.measurable_uncurry G₂.measurable_uncurry
    G₁.progressive G₂.progressive G₁.sq_int_global G₂.sq_int_global
    (G₁.add G₂).measurable_uncurry (G₁.add G₂).progressive (G₁.add G₂).sq_int_global hT

/-- Homogeneity of the integral on admissible marked integrands. -/
theorem integral_smul (hT : 0 < T) (c : ℝ) (G : MarkedHorizonIntegrand P ν ℱ T) :
    (G.smul c).integral N hℱ =ᵐ[P] fun ω => c * G.integral N hℱ ω :=
  stochasticIntegral_const_mul N ℱ hℱ G.measurable_uncurry G.progressive G.sq_int_global c
    (G.smul c).measurable_uncurry (G.smul c).progressive (G.smul c).sq_int_global hT

/-- The compensated integral over the horizon has mean zero. -/
theorem integral_mean_zero (hT : 0 ≤ T) (G : MarkedHorizonIntegrand P ν ℱ T) :
    ∫ ω, G.integral N hℱ ω ∂P = 0 := by
  obtain ⟨F, hF⟩ := martingale_stochasticIntegral N ℱ hℱ G.toFun G.measurable_uncurry
    G.progressive G.sq_int_global
  haveI : SigmaFinite (P.trim (F.le 0)) := (isFiniteMeasure_trim (F.le 0)).toSigmaFinite
  have hcond := hF.2 0 T hT
  have hz : stochasticIntegral N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
      G.sq_int_global 0 =ᵐ[P] 0 :=
    (stochasticIntegral_ae_eq_process N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
      G.sq_int_global 0).trans
      (process_ae_zero_of_nonpos N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
        G.sq_int_global le_rfl)
  calc ∫ ω, G.integral N hℱ ω ∂P
      = ∫ ω, condExp (F 0) P (fun x => stochasticIntegral N ℱ hℱ G.toFun
          G.measurable_uncurry G.progressive G.sq_int_global T x) ω ∂P :=
        (integral_condExp (F.le 0)).symm
    _ = ∫ ω, stochasticIntegral N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
          G.sq_int_global 0 ω ∂P := integral_congr_ae hcond
    _ = 0 := by rw [integral_congr_ae hz]; simp

end Integral

end MarkedHorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

/-- The compensated integrals of admissible marked integrands, as a submodule of `L²`. -/
noncomputable def compensatedRange (hT : 0 < T) : Submodule ℝ (Lp ℝ 2 P) where
  carrier := {u : Lp ℝ 2 P |
    ∃ G : MarkedHorizonIntegrand P ν ℱ T, (u : Ω → ℝ) =ᵐ[P] G.integral N hℱ}
  zero_mem' := by
    refine ⟨MarkedHorizonIntegrand.zero P ν ℱ T, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 P, MarkedHorizonIntegrand.integral_zero N hℱ hT]
      with ω h1 h2
    rw [h1, h2]
  add_mem' := by
    intro u v hu hv
    obtain ⟨G₁, h₁⟩ := hu
    obtain ⟨G₂, h₂⟩ := hv
    refine ⟨G₁.add G₂, ?_⟩
    filter_upwards [Lp.coeFn_add u v, h₁, h₂,
      MarkedHorizonIntegrand.integral_add N hℱ hT G₁ G₂] with ω e1 e2 e3 e4
    rw [e1, Pi.add_apply, e2, e3, e4]
  smul_mem' := by
    intro c u hu
    obtain ⟨G, h⟩ := hu
    refine ⟨G.smul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c u, h, MarkedHorizonIntegrand.integral_smul N hℱ hT c G]
      with ω e1 e2 e3
    rw [e1, Pi.smul_apply, e2, e3, smul_eq_mul]

/-- The `L²`-distance between two compensated integrals is the energy of the difference. -/
theorem markedEnergy_eq_edist_sq (hT : 0 < T) {u v : Lp ℝ 2 P}
    {G₁ G₂ : MarkedHorizonIntegrand P ν ℱ T}
    (h₁ : (u : Ω → ℝ) =ᵐ[P] G₁.integral N hℱ) (h₂ : (v : Ω → ℝ) =ᵐ[P] G₂.integral N hℱ) :
    markedEnergy P ν T (fun ω s e => G₁.toFun ω s e - G₂.toFun ω s e) = edist u v ^ 2 := by
  rw [Lp.edist_def, LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral _
    ((u : Ω → ℝ) - (v : Ω → ℝ))
    ((Lp.aestronglyMeasurable u).sub (Lp.aestronglyMeasurable v)),
    ← MarkedHorizonIntegrand.lintegral_sq_integral_sub N hℱ hT G₁ G₂]
  refine lintegral_congr_ae ?_
  filter_upwards [h₁, h₂] with ω e1 e2
  simp only [Pi.sub_apply]
  rw [e1, e2]

/-- **The compensated integrals form a closed submodule of `L²`.** -/
theorem isClosed_compensatedRange (hT : 0 < T) :
    IsClosed ((compensatedRange N hℱ hT : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) := by
  refine IsSeqClosed.isClosed ?_
  intro u v hu huv
  choose G hG using hu
  have hCau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N₀, ∀ m, N₀ ≤ m → ∀ n, N₀ ≤ n →
      markedEnergy P ν T (fun ω s e => (G m).toFun ω s e - (G n).toFun ω s e) < ε := by
    intro ε hε
    have hcs : CauchySeq u := huv.cauchySeq
    rw [EMetric.cauchySeq_iff] at hcs
    obtain ⟨N₀, hN₀⟩ := hcs (min ε 1) (lt_min hε one_pos)
    refine ⟨N₀, fun m hm n hn => ?_⟩
    rw [markedEnergy_eq_edist_sq N hℱ hT (hG m) (hG n)]
    refine lt_of_lt_of_le (ENNReal.pow_lt_pow_left (by norm_num) (hN₀ m hm n hn)) ?_
    calc (min ε 1) ^ 2 = min ε 1 * min ε 1 := sq _
      _ ≤ min ε 1 * 1 := by gcongr; exact min_le_right ε 1
      _ = min ε 1 := mul_one _
      _ ≤ ε := min_le_left ε 1
  obtain ⟨K, hKm, hKp, hKz, hKfin, hKtend⟩ :=
    exists_marked_progressive_energy_limit ℱ (fun n => (G n).measurable_uncurry)
      (fun n => (G n).progressive) (fun n => (G n).vanishing)
      (fun n => (G n).energy_ne_top) hCau
  obtain ⟨tgt, htgt⟩ : ∃ t : Lp ℝ 2 P, (t : Ω → ℝ)
      =ᵐ[P] (⟨K, hKm, hKp, hKz, hKfin⟩ : MarkedHorizonIntegrand P ν ℱ T).integral N hℱ :=
    ⟨_, MemLp.coeFn_toLp (MarkedHorizonIntegrand.memLp N hℱ _)⟩
  have hlim : Tendsto u atTop (𝓝 tgt) := by
    rw [EMetric.tendsto_atTop]
    intro ε hε
    have hpos : (0 : ℝ≥0∞) < (min ε 1) ^ 2 :=
      zero_lt_iff.mpr (pow_ne_zero 2 (ne_of_gt (lt_min hε one_pos)))
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hKtend.eventually_lt_const hpos)
    refine ⟨N₀, fun n hn => ?_⟩
    have hedist : markedEnergy P ν T (fun ω s e => (G n).toFun ω s e - K ω s e)
        = edist (u n) tgt ^ 2 := markedEnergy_eq_edist_sq N hℱ hT (hG n) htgt
    have hlt : edist (u n) tgt ^ 2 < (min ε 1) ^ 2 := hedist ▸ hN₀ n hn
    rcases lt_or_ge (edist (u n) tgt) (min ε 1) with h | h
    · exact lt_of_lt_of_le h (min_le_left ε 1)
    · exact absurd hlt (not_lt.mpr (pow_le_pow_left' h 2))
  refine ⟨⟨K, hKm, hKp, hKz, hKfin⟩, ?_⟩
  rw [tendsto_nhds_unique huv hlim]
  exact htgt

end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

/-- The compensated integral over the horizon is measurable before `T`. -/
theorem MarkedHorizonIntegrand.aestronglyMeasurable (G : MarkedHorizonIntegrand P ν ℱ T) :
    AEStronglyMeasurable[ℱ T] (G.integral N hℱ) P :=
  ((process_stronglyAdapted N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global T).aestronglyMeasurable).congr
    (stochasticIntegral_ae_eq_process N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
      G.sq_int_global T).symm

/-- **The representation half of the predictable representation property for the compensated
Poisson integral.** If the only square-integrable weight of mean zero, measurable before `T` and
orthogonal to every compensated integral, is the zero weight, then every square-integrable weight
of mean zero that is measurable before `T` is a compensated integral. -/
theorem exists_markedHorizonIntegrand_of_mean_zero (hT : 0 < T)
    (hsep : ∀ r : Ω → ℝ, MemLp r 2 P → AEStronglyMeasurable[ℱ T] r P →
      (∫ ω, r ω ∂P = 0) →
      (∀ G : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, r ω * G.integral N hℱ ω ∂P = 0) → r =ᵐ[P] 0)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ G : MarkedHorizonIntegrand P ν ℱ T, Z =ᵐ[P] G.integral N hℱ := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  haveI hcl : IsClosed ((compensatedRange N hℱ hT : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
    isClosed_compensatedRange N hℱ hT
  haveI : CompleteSpace (compensatedRange N hℱ hT) := hcl.completeSpace_coe
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (compensatedRange N hℱ hT).exists_add_mem_mem_orthogonal (hZ2.toLp Z)
  obtain ⟨G₀, hG₀⟩ := hy
  have hsplit : Z =ᵐ[P] fun ω => G₀.integral N hℱ ω + (z : Ω → ℝ) ω := by
    filter_upwards [hZ2.coeFn_toLp, Lp.coeFn_add y z, hG₀] with ω e1 e2 e3
    rw [← e1, hyz, e2, Pi.add_apply, e3]
  have hzmem : MemLp (z : Ω → ℝ) 2 P := Lp.memLp z
  have hzmeas : AEStronglyMeasurable[ℱ T] (z : Ω → ℝ) P := by
    have hd : (z : Ω → ℝ) =ᵐ[P] fun ω => Z ω - G₀.integral N hℱ ω := by
      filter_upwards [hsplit] with ω e1
      rw [e1]; ring
    exact (hZm.sub (MarkedHorizonIntegrand.aestronglyMeasurable N hℱ G₀)).congr hd.symm
  have hymean : ∫ ω, G₀.integral N hℱ ω ∂P = 0 :=
    MarkedHorizonIntegrand.integral_mean_zero N hℱ hT.le G₀
  have hzint : Integrable (z : Ω → ℝ) P := hzmem.integrable (by norm_num)
  have hyint : Integrable (G₀.integral N hℱ) P :=
    (MarkedHorizonIntegrand.memLp N hℱ G₀).integrable (by norm_num)
  have hzmean : ∫ ω, (z : Ω → ℝ) ω ∂P = 0 := by
    have := integral_congr_ae (μ := P) hsplit
    rw [integral_add hyint hzint, hymean, zero_add] at this
    rw [← this, hZ0]
  have hzperp : ∀ G : MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, (z : Ω → ℝ) ω * G.integral N hℱ ω ∂P = 0 := by
    intro G
    have hmem : (MarkedHorizonIntegrand.memLp N hℱ G).toLp (G.integral N hℱ)
        ∈ compensatedRange N hℱ hT := ⟨G, MemLp.coeFn_toLp _⟩
    have hinner := (Submodule.mem_orthogonal _ z).mp hz _ hmem
    rw [L2.inner_def] at hinner
    have hcongr : ∫ ω, (((MarkedHorizonIntegrand.memLp N hℱ G).toLp (G.integral N hℱ) :
          Ω → ℝ) ω * (z : Ω → ℝ) ω) ∂P = ∫ ω, G.integral N hℱ ω * (z : Ω → ℝ) ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (MarkedHorizonIntegrand.memLp N hℱ G)] with ω e1
      rw [e1]
    have hrw : ∫ ω, G.integral N hℱ ω * (z : Ω → ℝ) ω ∂P = 0 := by
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

end LevyStochCalc.Poisson.Compensated
