/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoIntegrandComplete
import LevyStochCalc.Probability.Progressive

/-!
# Completeness of the marked integrands

The marked energy of an integrand over a horizon is the square of its `L²`-seminorm for the
product of the sample measure, Lebesgue measure on the horizon and the mark measure. That space is
complete, so an energy-Cauchy sequence of admissible marked integrands has a limit; a pointwise
`limsup` along an almost-everywhere convergent subsequence provides a genuinely progressively
measurable representative of it.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The product of the sample measure, Lebesgue measure on the horizon and the mark measure. -/
noncomputable def markedEnergyMeasure (P : Measure Ω) (ν : Measure E) (T : ℝ) :
    Measure (Ω × ℝ × E) :=
  P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)

/-- The energy of a marked integrand over the horizon `[0, T]`. -/
noncomputable def markedEnergy (P : Measure Ω) (ν : Measure E) (T : ℝ) (φ : Ω → ℝ → E → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P

omit [IsProbabilityMeasure P] in
/-- The marked energy is the square of the `L²`-seminorm on the product space. -/
theorem markedEnergy_eq_eLpNorm_sq {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (T : ℝ) :
    markedEnergy P ν T φ
      = eLpNorm (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (markedEnergyMeasure P ν T) ^ 2 := by
  have hme : Measurable fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2
  rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral _ _ hm.aestronglyMeasurable, markedEnergyMeasure, markedEnergy,
    lintegral_prod _ hme.aemeasurable]
  refine lintegral_congr fun ω => ?_
  exact (lintegral_prod (μ := volume.restrict (Set.Icc (0 : ℝ) T)) (ν := ν)
    (fun y : ℝ × E => (‖φ ω y.1 y.2‖₊ : ℝ≥0∞) ^ 2)
    (hme.comp (measurable_prodMk_left (x := ω))).aemeasurable).symm

omit [IsProbabilityMeasure P] in
/-- A marked integrand of finite energy is square integrable on the product space. -/
theorem memLp_of_markedEnergy_ne_top {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) {T : ℝ}
    (hfin : markedEnergy P ν T φ ≠ ⊤) :
    MemLp (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (markedEnergyMeasure P ν T) := by
  change eLpNorm (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (markedEnergyMeasure P ν T) < ⊤
  refine lt_top_iff_ne_top.mpr fun hcon => hfin ?_
  rw [markedEnergy_eq_eLpNorm_sq hm T, hcon]
  simp

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A marked integrand vanishing off the horizon has no more energy on any other horizon. -/
theorem markedEnergy_le_of_vanishing {φ : Ω → ℝ → E → ℝ} {T : ℝ}
    (hz : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → φ ω s e = 0) (T' : ℝ) :
    markedEnergy P ν T' φ ≤ markedEnergy P ν T φ := by
  refine lintegral_mono fun ω => ?_
  have hind : (fun s => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      = Set.indicator (Set.Icc (0 : ℝ) T) (fun s => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) := by
    funext s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      have hzero : (fun e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2) = fun _ => (0 : ℝ≥0∞) := by
        funext e; rw [hz ω s e hs]; simp
      rw [hzero]
      simp
  calc ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
      = ∫⁻ s in Set.Icc (0 : ℝ) T ∩ Set.Icc (0 : ℝ) T',
          ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
        conv_lhs => rw [hind]
        rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume :=
        lintegral_mono' (Measure.restrict_mono Set.inter_subset_left le_rfl) le_rfl

section Complete

variable {T : ℝ} {φ : ℕ → Ω → ℝ → E → ℝ}

omit [IsProbabilityMeasure P] in
/-- An energy-Cauchy sequence of marked integrands has an `L²`-limit on the product space. -/
theorem exists_markedEnergy_limit
    (hm : ∀ n, Measurable fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2)
    (hfin : ∀ n, markedEnergy P ν T (φ n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      markedEnergy P ν T (fun ω s e => φ m ω s e - φ n ω s e) < ε) :
    ∃ g : Ω × ℝ × E → ℝ, MemLp g 2 (markedEnergyMeasure P ν T)
      ∧ Tendsto (fun n => eLpNorm
          ((fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2) - g) 2 (markedEnergyMeasure P ν T))
          atTop (𝓝 0) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hMem : ∀ n, MemLp (fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2) 2
      (markedEnergyMeasure P ν T) := fun n => memLp_of_markedEnergy_ne_top (hm n) (hfin n)
  have hcs : CauchySeq fun n => (hMem n).toLp fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2 := by
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm' n hn' => ?_⟩
    rw [Lp.edist_def]
    have hcongr : eLpNorm
          ((((hMem m).toLp fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2) : Ω × ℝ × E → ℝ)
            - (((hMem n).toLp fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2) : Ω × ℝ × E → ℝ))
          2 (markedEnergyMeasure P ν T)
        = eLpNorm (fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2 - φ n p.1 p.2.1 p.2.2) 2
          (markedEnergyMeasure P ν T) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hMem m).coeFn_toLp, (hMem n).coeFn_toLp] with p h1 h2
      simp only [Pi.sub_apply]
      rw [h1, h2]
    rw [hcongr]
    rcases lt_or_ge (eLpNorm (fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2 - φ n p.1 p.2.1 p.2.2)
      2 (markedEnergyMeasure P ν T)) ε with hlt' | hge
    · exact hlt'
    · exfalso
      have hsq : ε ^ 2 ≤ eLpNorm
          (fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2 - φ n p.1 p.2.1 p.2.2) 2
          (markedEnergyMeasure P ν T) ^ 2 := pow_le_pow_left' hge 2
      have hlt := hN m hm' n hn'
      rw [markedEnergy_eq_eLpNorm_sq ((hm m).sub (hm n)) T] at hlt
      exact absurd hlt (not_lt.mpr hsq)
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨(G : Ω × ℝ × E → ℝ), Lp.memLp G, ?_⟩
  have hlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ G).mp hG
  refine hlim.congr fun n => ?_
  refine eLpNorm_congr_ae ?_
  filter_upwards [(hMem n).coeFn_toLp] with p h1
  simp only [Pi.sub_apply]
  rw [h1]

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A pointwise `limsup` along `atTop` of countably many progressively measurable marked
processes is progressively measurable. -/
theorem markedProgressivelyMeasurable_limsup {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {φ : ℕ → Ω → ℝ → E → ℝ} (h : ∀ k, Probability.MarkedProgressivelyMeasurable ℱ (φ k)) :
    Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => limsup (fun k => φ k ω s e) atTop := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hind : (fun p : Ω × ℝ × E => (Set.Iic t).indicator
        (fun s => limsup (fun k => φ k p.1 s p.2.2) atTop) p.2.1)
      = fun p : Ω × ℝ × E =>
        limsup (fun k => (Set.Iic t).indicator (fun s => φ k p.1 s p.2.2) p.2.1) atTop := by
    funext p
    by_cases hp : p.2.1 ∈ Set.Iic t
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, limsup_const]
  rw [hind]
  refine stronglyMeasurable_iff_measurable.mpr (Measurable.limsup fun k => ?_)
  exact (h k t).measurable

/-- The pointwise `limsup` of a subsequence of marked integrands. -/
noncomputable def limsupMarkedIntegrand (φ : ℕ → Ω → ℝ → E → ℝ) (ns : ℕ → ℕ) :
    Ω → ℝ → E → ℝ := fun ω s e => limsup (fun i => φ (ns i) ω s e) atTop

omit [IsProbabilityMeasure P] in
/-- **Completeness of the admissible marked integrands.** An energy-Cauchy sequence of jointly and
progressively measurable marked integrands vanishing off the horizon has an admissible limit. -/
theorem exists_marked_progressive_energy_limit (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hm : ∀ n, Measurable fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2)
    (hp : ∀ n, Probability.MarkedProgressivelyMeasurable ℱ (φ n))
    (hz : ∀ n ω s e, s ∉ Set.Icc (0 : ℝ) T → φ n ω s e = 0)
    (hfin : ∀ n, markedEnergy P ν T (φ n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      markedEnergy P ν T (fun ω s e => φ m ω s e - φ n ω s e) < ε) :
    ∃ ψ : Ω → ℝ → E → ℝ, Measurable (fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
      ∧ Probability.MarkedProgressivelyMeasurable ℱ ψ
      ∧ (∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → ψ ω s e = 0)
      ∧ markedEnergy P ν T ψ ≠ ⊤
      ∧ Tendsto (fun n => markedEnergy P ν T (fun ω s e => φ n ω s e - ψ ω s e)) atTop (𝓝 0) := by
  obtain ⟨g, hgMem, hgt⟩ := exists_markedEnergy_limit hm hfin hcau
  have hMem : ∀ n, MemLp (fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2) 2
      (markedEnergyMeasure P ν T) := fun n => memLp_of_markedEnergy_ne_top (hm n) (hfin n)
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (μ := markedEnergyMeasure P ν T) (p := 2) (by norm_num)
    hgt).exists_seq_tendsto_ae
  have hKm : Measurable fun p : Ω × ℝ × E =>
      limsupMarkedIntegrand φ ns p.1 p.2.1 p.2.2 := Measurable.limsup fun i => hm (ns i)
  have hKp : Probability.MarkedProgressivelyMeasurable ℱ (limsupMarkedIntegrand φ ns) :=
    markedProgressivelyMeasurable_limsup fun i => hp (ns i)
  have hKz : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → limsupMarkedIntegrand φ ns ω s e = 0 := by
    intro ω s e hs
    have h0 : (fun i => φ (ns i) ω s e) = fun _ => (0 : ℝ) :=
      funext fun i => hz (ns i) ω s e hs
    rw [limsupMarkedIntegrand, h0]
    exact limsup_const 0
  have hKg : (fun p : Ω × ℝ × E => limsupMarkedIntegrand φ ns p.1 p.2.1 p.2.2)
      =ᵐ[markedEnergyMeasure P ν T] g := by
    filter_upwards [hae] with p hp'
    exact hp'.limsup_eq
  have hKfin : markedEnergy P ν T (limsupMarkedIntegrand φ ns) ≠ ⊤ := by
    rw [markedEnergy_eq_eLpNorm_sq hKm T, eLpNorm_congr_ae hKg]
    exact ENNReal.pow_ne_top hgMem.eLpNorm_lt_top.ne
  have hEq : ∀ n, markedEnergy P ν T
      (fun ω s e => φ n ω s e - limsupMarkedIntegrand φ ns ω s e)
      = eLpNorm ((fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2) - g) 2
        (markedEnergyMeasure P ν T) ^ 2 := by
    intro n
    rw [markedEnergy_eq_eLpNorm_sq ((hm n).sub hKm) T]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hKg] with p h1
    simp only [Pi.sub_apply]
    rw [h1]
  refine ⟨limsupMarkedIntegrand φ ns, hKm, hKp, hKz, hKfin, ?_⟩
  simp only [hEq]
  have hcont : Continuous fun x : ℝ≥0∞ => x ^ 2 := ENNReal.continuous_pow 2
  simpa [Function.comp_def] using (hcont.tendsto 0).comp hgt

end Complete

end LevyStochCalc.Poisson.Compensated
