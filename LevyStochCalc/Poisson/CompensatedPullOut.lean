/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedRange

/-!
# Pulling a past weight inside a compensated integral

A bounded weight measurable at time `a` times the compensated integral of a marked integrand
vanishing up to `a` is the compensated integral of the weighted integrand. The identity is proved
in `L²`: the squared distance between the two sides expands, through the Itô–Lévy isometry and
the quadratic-variation martingale started at `a`, into a combination of weighted compensators
that cancels.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] [SigmaFinite ν] [MeasurableSpace E] in
/-- The product of two square-integrable functions is integrable. -/
theorem integrable_mul_of_memLp_two {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := by
  have hdom : Integrable (fun ω => 1 / 2 * f ω ^ 2 + 1 / 2 * g ω ^ 2) P :=
    (hf.integrable_sq.const_mul (1 / 2 : ℝ)).add (hg.integrable_sq.const_mul (1 / 2 : ℝ))
  refine Integrable.mono' hdom (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_abs (f ω), sq_abs (g ω), sq_nonneg (|f ω| - |g ω|)]

section Vanishing

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The compensator of an integrand vanishing up to `a` vanishes at `a`. -/
theorem compensator_eq_zero_of_vanishing {a : ℝ} (hφa : ∀ ω s e, s ≤ a → φ ω s e = 0) :
    compensator ν φ a = fun _ => 0 := by
  funext ω
  rw [compensator, setIntegral_congr_fun measurableSet_Icc (g := fun _ => (0 : ℝ))
    (fun u hu => by
      have h := fun e => hφa ω u e hu.2
      simp [h])]
  simp

include hℱ in
/-- The compensated integral of an integrand vanishing up to `a` vanishes at `a`. -/
theorem stochasticIntegral_ae_zero_of_vanishing {a : ℝ} (ha : 0 ≤ a)
    (hφa : ∀ ω s e, s ≤ a → φ ω s e = 0) :
    stochasticIntegral N ℱ hℱ φ hm hp hq a =ᵐ[P] 0 := by
  have hiso := process_lintegral_sq' N ℱ hℱ φ hm hp hq ha
  have h0 : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) a, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      = 0 := by
    have hin : ∀ ω,
        ∫⁻ s in Set.Icc (0 : ℝ) a, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume = 0 := by
      intro ω
      rw [setLIntegral_congr_fun measurableSet_Icc (g := fun _ => (0 : ℝ≥0∞))
        (fun s hs => by
          have h := fun e => hφa ω s e hs.2
          simp [h])]
      simp
    simp [hin]
  have hzero : ∫⁻ ω, (‖process N ℱ hℱ φ hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := hiso.trans h0
  have hae : AEMeasurable (fun ω => (‖process N ℱ hℱ φ hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2) P :=
    ((((process_memLp N ℱ hℱ φ hm hp hq a).aestronglyMeasurable.aemeasurable).nnnorm
      ).coe_nnreal_ennreal).pow_const 2
  have hproc : process N ℱ hℱ φ hm hp hq a =ᵐ[P] 0 := by
    filter_upwards [(lintegral_eq_zero_iff' hae).mp hzero] with ω hω
    have h2 : (‖process N ℱ hℱ φ hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 = 0 := hω
    have h3 : (‖process N ℱ hℱ φ hm hp hq a ω‖₊ : ℝ≥0∞) = 0 :=
      (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
    simpa using h3
  exact (stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq a).trans hproc

include hℱ in
/-- **The weighted quadratic variation.** For a bounded weight measurable at `a` and an
integrand vanishing up to `a`, the weighted second moment of the compensated integral at
`T ≥ a` is the weighted compensator. -/
theorem integral_mul_sq_stochasticIntegral {a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (hφa : ∀ ω s e, s ≤ a → φ ω s e = 0) {U : Ω → ℝ} (hUm : StronglyMeasurable[ℱ a] U)
    {M : ℝ} (hUb : ∀ ω, |U ω| ≤ M) :
    ∫ ω, U ω * (stochasticIntegral N ℱ hℱ φ hm hp hq T ω) ^ 2 ∂P
      = ∫ ω, U ω * compensator ν φ T ω ∂P := by
  haveI : SigmaFinite (P.trim (ℱ.rightCont.le a)) := by infer_instance
  set f : ℝ → Ω → ℝ := fun t ω =>
    (stochasticIntegral N ℱ hℱ φ hm hp hq t ω) ^ 2 - compensator ν φ t ω with hf
  have hmart : Martingale f ℱ.rightCont P :=
    martingale_quadVar_stochasticIntegral_rightCont N ℱ hℱ φ hm hp hq
  have hsq : ∀ t, Integrable (fun ω => (stochasticIntegral N ℱ hℱ φ hm hp hq t ω) ^ 2) P :=
    fun t => (stochasticIntegral_memLp N ℱ hℱ φ hm hp hq t).integrable_sq
  have hcomp : ∀ t, Integrable (compensator ν φ t) P := fun t =>
    integrable_compensator φ hm hq t
  have hint : ∀ t, Integrable (f t) P := fun t => (hsq t).sub (hcomp t)
  have hUmeas : Measurable U := hUm.measurable.mono (ℱ.le a) le_rfl
  have hUnorm : ∀ᵐ ω ∂P, ‖U ω‖ ≤ M :=
    Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hUb ω
  have hprod : Integrable (fun ω => U ω * f T ω) P :=
    (hint T).bdd_mul hUmeas.aestronglyMeasurable hUnorm
  have hUm' : StronglyMeasurable[ℱ.rightCont a] U := hUm.mono (ℱ.le_rightCont a)
  have hpull : P[(fun ω => U ω * f T ω) | ℱ.rightCont a]
      =ᵐ[P] fun ω => U ω * (P[f T | ℱ.rightCont a]) ω :=
    condExp_mul_of_stronglyMeasurable_left hUm' hprod (hint T)
  have hcond : P[f T | ℱ.rightCont a] =ᵐ[P] f a := hmart.condExp_ae_eq haT
  have hfa : f a =ᵐ[P] 0 := by
    filter_upwards [stochasticIntegral_ae_zero_of_vanishing N hℱ φ hm hp hq ha hφa] with ω hω
    simp only [hf, hω, compensator_eq_zero_of_vanishing φ hφa, Pi.zero_apply]
    norm_num
  have hUf : ∫ ω, U ω * f T ω ∂P = 0 := by
    rw [← integral_condExp (ℱ.rightCont.le a)]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hpull, hcond, hfa] with ω e1 e2 e3
    rw [e1]
    simp only [e2, e3, Pi.zero_apply, mul_zero]
  have hexp : ∀ ω, U ω * f T ω
      = U ω * (stochasticIntegral N ℱ hℱ φ hm hp hq T ω) ^ 2 - U ω * compensator ν φ T ω :=
    fun ω => by simp only [hf]; ring
  simp_rw [hexp] at hUf
  rw [integral_sub ((hsq T).bdd_mul hUmeas.aestronglyMeasurable hUnorm)
    ((hcomp T).bdd_mul hUmeas.aestronglyMeasurable hUnorm), sub_eq_zero] at hUf
  exact hUf

end Vanishing

section Weighted

/-- A weight measurable at `a` times an integrand vanishing up to `a` is progressive. -/
theorem markedProgressivelyMeasurable_mul_of_vanishing {φ : Ω → ℝ → E → ℝ}
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ) {a : ℝ}
    (hφa : ∀ ω s e, s ≤ a → φ ω s e = 0) {V : Ω → ℝ} (hVm : StronglyMeasurable[ℱ a] V) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => V ω * φ ω s e := by
  intro t
  change @StronglyMeasurable (Ω × ℝ × E) ℝ _
    (@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance)
    fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => V p.1 * φ p.1 s p.2.2) p.2.1
  rcases lt_or_ge t a with hta | hat
  · have h0 : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => V p.1 * φ p.1 s p.2.2) p.2.1) = fun _ => 0 := by
      funext p
      by_cases hs : p.2.1 ∈ Set.Iic t
      · rw [Set.indicator_of_mem hs, hφa _ _ _ (le_trans hs hta.le), mul_zero]
      · rw [Set.indicator_of_notMem hs]
    rw [h0]
    exact stronglyMeasurable_const
  · have h1 : @StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance) fun p => V p.1 :=
      (hVm.mono (ℱ.mono hat)).comp_measurable (@measurable_fst Ω (ℝ × E) (ℱ t) _)
    have h2 := hp t
    have h3 : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => V p.1 * φ p.1 s p.2.2) p.2.1)
        = fun p => V p.1 * (Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1 := by
      funext p
      exact Set.indicator_const_mul _ _ _ _
    rw [h3]
    exact h1.mul h2

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The energy of a boundedly weighted integrand is finite when the energy is. -/
theorem markedEnergy_mul_ne_top {φ : Ω → ℝ → E → ℝ} {T : ℝ} (h : markedEnergy P ν T φ ≠ ⊤)
    {V : Ω → ℝ} {M : ℝ} (hVb : ∀ ω, |V ω| ≤ M) :
    markedEnergy P ν T (fun ω s e => V ω * φ ω s e) ≠ ⊤ := by
  have hM : ENNReal.ofReal (M ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hM h) ?_
  unfold markedEnergy
  rw [← lintegral_const_mul' _ _ hM]
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_const_mul' _ _ hM]
  refine lintegral_mono fun s => ?_
  rw [← lintegral_const_mul' _ _ hM]
  refine lintegral_mono fun e => ?_
  rw [coe_nnnorm_sq_eq_ofReal_sq, coe_nnnorm_sq_eq_ofReal_sq,
    ← ENNReal.ofReal_mul (sq_nonneg M)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_pow, ← sq_abs (V ω)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hVb ω) 2) (sq_nonneg _)

namespace MarkedHorizonIntegrand

variable {T : ℝ}

/-- A marked integrand vanishing up to `a`, multiplied by a bounded weight measurable at `a`. -/
noncomputable def mulLeft (G : MarkedHorizonIntegrand P ν ℱ T) {a : ℝ}
    (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {V : Ω → ℝ} (hVm : StronglyMeasurable[ℱ a] V)
    {M : ℝ} (hVb : ∀ ω, |V ω| ≤ M) : MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun ω s e => V ω * G.toFun ω s e
  measurable_uncurry :=
    ((hVm.measurable.mono (ℱ.le a) le_rfl).comp measurable_fst).mul G.measurable_uncurry
  progressive := markedProgressivelyMeasurable_mul_of_vanishing G.progressive hGa hVm
  vanishing := fun ω s e hs => by rw [G.vanishing ω s e hs, mul_zero]
  energy_ne_top := markedEnergy_mul_ne_top G.energy_ne_top hVb

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

/-- The compensated integral depends only on the underlying process. -/
theorem integral_congr_toFun {G₁ G₂ : MarkedHorizonIntegrand P ν ℱ T} (h : G₁.toFun = G₂.toFun) :
    G₁.integral N hℱ = G₂.integral N hℱ := by
  cases G₁
  cases G₂
  cases h
  rfl

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The compensator of a weighted integrand is the squared weight times the compensator. -/
theorem compensator_mulLeft (G : MarkedHorizonIntegrand P ν ℱ T) {a : ℝ}
    (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {V : Ω → ℝ} (hVm : StronglyMeasurable[ℱ a] V)
    {M : ℝ} (hVb : ∀ ω, |V ω| ≤ M) :
    compensator ν (G.mulLeft hGa hVm hVb).toFun T
      = fun ω => V ω ^ 2 * compensator ν G.toFun T ω := by
  funext ω
  change (∫ u in Set.Icc (0 : ℝ) T, ∫ e, (V ω * G.toFun ω u e) ^ 2 ∂ν ∂volume)
    = V ω ^ 2 * ∫ u in Set.Icc (0 : ℝ) T, ∫ e, (G.toFun ω u e) ^ 2 ∂ν ∂volume
  simp_rw [mul_pow, integral_const_mul]

/-- The weighted second moment of the compensated integral of an integrand vanishing up to
`a`, against a bounded weight measurable at `a`, is the weighted compensator. -/
theorem integral_mul_sq_integral (G : MarkedHorizonIntegrand P ν ℱ T) {a : ℝ} (ha : 0 ≤ a)
    (haT : a ≤ T) (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ a] U) {M : ℝ} (hUb : ∀ ω, |U ω| ≤ M) :
    ∫ ω, U ω * (G.integral N hℱ ω) ^ 2 ∂P = ∫ ω, U ω * compensator ν G.toFun T ω ∂P :=
  integral_mul_sq_stochasticIntegral N hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global ha haT hGa hUm hUb

/-- **Pulling a past weight inside the compensated integral.** For a bounded weight `V`
measurable at `a` and an integrand `G` vanishing up to `a`, `V · ∫G dÑ = ∫ V·G dÑ`. -/
theorem integral_mulLeft (hT : 0 < T) (G : MarkedHorizonIntegrand P ν ℱ T) {a : ℝ} (ha : 0 ≤ a)
    (haT : a ≤ T) (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {V : Ω → ℝ}
    (hVm : StronglyMeasurable[ℱ a] V) {M : ℝ} (hVb : ∀ ω, |V ω| ≤ M) :
    (G.mulLeft hGa hVm hVb).integral N hℱ =ᵐ[P] fun ω => V ω * G.integral N hℱ ω := by
  have hVb' : ∀ ω, |V ω| ≤ |M| := fun ω => (hVb ω).trans (le_abs_self M)
  have hM0 : 0 ≤ |M| := abs_nonneg M
  have hVm1 : StronglyMeasurable[ℱ a] fun ω => V ω + 1 := hVm.add stronglyMeasurable_const
  have hVb1 : ∀ ω, |V ω + 1| ≤ |M| + 1 := fun ω =>
    (abs_add_le _ _).trans (by simpa using add_le_add_right (hVb' ω) 1)
  set X := (G.mulLeft hGa hVm hVb).integral N hℱ with hX
  set Y := G.integral N hℱ with hY
  set S := (G.mulLeft hGa hVm1 hVb1).integral N hℱ with hS
  have hSXY : S =ᵐ[P] fun ω => X ω + Y ω := by
    have h1 := integral_add N hℱ hT (G.mulLeft hGa hVm hVb) G
    have h2 : ((G.mulLeft hGa hVm hVb).add G).integral N hℱ = S :=
      integral_congr_toFun N hℱ (by funext ω s e; simp only [add, mulLeft]; ring)
    rw [h2] at h1
    exact h1
  have hX2 : MemLp X 2 P := memLp N hℱ _
  have hY2 : MemLp Y 2 P := memLp N hℱ G
  have hS2 : MemLp S 2 P := memLp N hℱ _
  have hVmeas : Measurable V := hVm.measurable.mono (ℱ.le a) le_rfl
  have hVnorm : ∀ᵐ ω ∂P, ‖V ω‖ ≤ M :=
    Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hVb ω
  have hcomp : Integrable (compensator ν G.toFun T) P :=
    integrable_compensator G.toFun G.measurable_uncurry G.sq_int_global T
  -- integrability of bounded multiples of the compensator
  have hbdd : ∀ (U : Ω → ℝ), Measurable U → ∀ C : ℝ, (∀ ω, |U ω| ≤ C) →
      Integrable (fun ω => U ω * compensator ν G.toFun T ω) P := fun U hU C hC =>
    hcomp.bdd_mul hU.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  -- the five weighted second moments
  have hXX : ∫ ω, X ω ^ 2 ∂P = ∫ ω, V ω ^ 2 * compensator ν G.toFun T ω ∂P := by
    have h := integral_mul_sq_integral N hℱ (G.mulLeft hGa hVm hVb) ha haT
      (fun ω s e hs => by
        change V ω * G.toFun ω s e = 0
        rw [hGa ω s e hs, mul_zero])
      (U := fun _ => (1 : ℝ)) stronglyMeasurable_const (M := 1) (fun _ => by simp)
    simp only [one_mul, compensator_mulLeft] at h
    exact h
  have hYY : ∫ ω, V ω ^ 2 * Y ω ^ 2 ∂P = ∫ ω, V ω ^ 2 * compensator ν G.toFun T ω ∂P :=
    integral_mul_sq_integral N hℱ G ha haT hGa (hVm.pow 2) (M := M ^ 2)
      (fun ω => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hVb ω) 2)
  have hVSS : ∫ ω, V ω * S ω ^ 2 ∂P
      = ∫ ω, V ω * ((V ω + 1) ^ 2 * compensator ν G.toFun T ω) ∂P := by
    have h := integral_mul_sq_integral N hℱ (G.mulLeft hGa hVm1 hVb1) ha haT
      (fun ω s e hs => by
        change (V ω + 1) * G.toFun ω s e = 0
        rw [hGa ω s e hs, mul_zero]) hVm hVb
    simp only [compensator_mulLeft] at h
    exact h
  have hVXX : ∫ ω, V ω * X ω ^ 2 ∂P
      = ∫ ω, V ω * (V ω ^ 2 * compensator ν G.toFun T ω) ∂P := by
    have h := integral_mul_sq_integral N hℱ (G.mulLeft hGa hVm hVb) ha haT
      (fun ω s e hs => by
        change V ω * G.toFun ω s e = 0
        rw [hGa ω s e hs, mul_zero]) hVm hVb
    simp only [compensator_mulLeft] at h
    exact h
  have hVYY : ∫ ω, V ω * Y ω ^ 2 ∂P = ∫ ω, V ω * compensator ν G.toFun T ω ∂P :=
    integral_mul_sq_integral N hℱ G ha haT hGa hVm hVb
  -- the cross term by polarisation
  have hXYint : Integrable (fun ω => V ω * (X ω * Y ω)) P :=
    (integrable_mul_of_memLp_two hX2 hY2).bdd_mul hVmeas.aestronglyMeasurable hVnorm
  have hVS2 : Integrable (fun ω => V ω * S ω ^ 2) P :=
    hS2.integrable_sq.bdd_mul hVmeas.aestronglyMeasurable hVnorm
  have hVX2 : Integrable (fun ω => V ω * X ω ^ 2) P :=
    hX2.integrable_sq.bdd_mul hVmeas.aestronglyMeasurable hVnorm
  have hVY2 : Integrable (fun ω => V ω * Y ω ^ 2) P :=
    hY2.integrable_sq.bdd_mul hVmeas.aestronglyMeasurable hVnorm
  have hXY : ∫ ω, V ω * (X ω * Y ω) ∂P = ∫ ω, V ω ^ 2 * compensator ν G.toFun T ω ∂P := by
    have hpt : (fun ω => V ω * (X ω * Y ω))
        =ᵐ[P] fun ω => (1 / 2 : ℝ) * (V ω * S ω ^ 2 - V ω * X ω ^ 2 - V ω * Y ω ^ 2) := by
      filter_upwards [hSXY] with ω hω
      rw [hω]
      ring
    have hVSX : Integrable (fun ω => V ω * S ω ^ 2 - V ω * X ω ^ 2) P := hVS2.sub hVX2
    rw [integral_congr_ae hpt, integral_const_mul, integral_sub hVSX hVY2,
      integral_sub hVS2 hVX2, hVSS, hVXX, hVYY]
    have i1 : Integrable (fun ω => (V ω * (V ω + 1) ^ 2) * compensator ν G.toFun T ω) P :=
      hbdd (fun ω => V ω * (V ω + 1) ^ 2) (hVmeas.mul ((hVmeas.add_const 1).pow_const 2))
        (|M| * (|M| + 1) ^ 2) (fun ω => by
          rw [abs_mul, abs_pow]
          exact mul_le_mul (hVb' ω) (pow_le_pow_left₀ (abs_nonneg _) (hVb1 ω) 2)
            (by positivity) hM0)
    have i2 : Integrable (fun ω => (V ω * V ω ^ 2) * compensator ν G.toFun T ω) P :=
      hbdd (fun ω => V ω * V ω ^ 2) (hVmeas.mul (hVmeas.pow_const 2)) (|M| * |M| ^ 2)
        (fun ω => by
          rw [abs_mul, abs_pow]
          exact mul_le_mul (hVb' ω) (pow_le_pow_left₀ (abs_nonneg _) (hVb' ω) 2)
            (by positivity) hM0)
    have i3 : Integrable (fun ω => V ω * compensator ν G.toFun T ω) P := hbdd V hVmeas M hVb
    have i12 : Integrable (fun ω => (V ω * (V ω + 1) ^ 2) * compensator ν G.toFun T ω
        - (V ω * V ω ^ 2) * compensator ν G.toFun T ω) P := i1.sub i2
    have e1 : (fun ω => V ω * ((V ω + 1) ^ 2 * compensator ν G.toFun T ω))
        = fun ω => (V ω * (V ω + 1) ^ 2) * compensator ν G.toFun T ω := by
      funext ω; ring
    have e2 : (fun ω => V ω * (V ω ^ 2 * compensator ν G.toFun T ω))
        = fun ω => (V ω * V ω ^ 2) * compensator ν G.toFun T ω := by
      funext ω; ring
    rw [e1, e2, ← integral_sub i1 i2, ← integral_sub i12 i3, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    ring
  -- the squared distance vanishes
  have hpt : ∀ ω, (X ω - V ω * Y ω) ^ 2
      = X ω ^ 2 - 2 * (V ω * (X ω * Y ω)) + V ω ^ 2 * Y ω ^ 2 := fun ω => by ring
  have hV2Y2 : Integrable (fun ω => V ω ^ 2 * Y ω ^ 2) P :=
    hY2.integrable_sq.bdd_mul (hVmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hVb ω) 2)
  have hint : Integrable (fun ω => (X ω - V ω * Y ω) ^ 2) P := by
    have : (fun ω => (X ω - V ω * Y ω) ^ 2)
        = fun ω => X ω ^ 2 - 2 * (V ω * (X ω * Y ω)) + V ω ^ 2 * Y ω ^ 2 := funext hpt
    rw [this]
    exact (hX2.integrable_sq.sub (hXYint.const_mul 2)).add hV2Y2
  have hA : Integrable (fun ω => X ω ^ 2 - 2 * (V ω * (X ω * Y ω))) P :=
    hX2.integrable_sq.sub (hXYint.const_mul 2)
  have hZ : ∫ ω, (X ω - V ω * Y ω) ^ 2 ∂P = 0 := by
    simp_rw [hpt]
    rw [MeasureTheory.integral_add hA hV2Y2, integral_sub hX2.integrable_sq (hXYint.const_mul 2),
      integral_const_mul, hXX, hXY, hYY]
    ring
  have hnn : 0 ≤ fun ω => (X ω - V ω * Y ω) ^ 2 := fun ω => sq_nonneg _
  filter_upwards [(integral_eq_zero_iff_of_nonneg hnn hint).mp hZ] with ω hω
  have h2 : (X ω - V ω * Y ω) ^ 2 = 0 := hω
  exact sub_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h2)

end MarkedHorizonIntegrand

end Weighted

end LevyStochCalc.Poisson.Compensated
