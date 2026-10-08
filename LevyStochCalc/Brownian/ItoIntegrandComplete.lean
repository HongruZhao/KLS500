/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoLinear

/-!
# Completeness of the admissible integrands on a horizon

The energy of an integrand over `[0, T]` is the square of its `L²`-seminorm for the product of
the sample measure with Lebesgue measure on the horizon. A sequence of integrands that is Cauchy
for that energy therefore has an `L²`-limit, and the pointwise `limsup` of an almost everywhere
convergent subsequence is a representative of that limit which is again progressively measurable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The product of the sample measure with Lebesgue measure on the horizon `[0, T]`. -/
noncomputable def energyMeasure (P : Measure Ω) (T : ℝ) : Measure (Ω × ℝ) :=
  P.prod (volume.restrict (Set.Icc (0 : ℝ) T))

/-- The energy of an integrand over the horizon `[0, T]`. -/
noncomputable def energy (P : Measure Ω) (T : ℝ) (H : Ω → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P

/-- The square of the `L²`-seminorm as an extended integral of squares. -/
theorem eLpNorm_sq_eq_lintegral {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by simp
  rw [h2, ← ENNReal.rpow_natCast ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) 2,
    ← ENNReal.rpow_mul]
  norm_num
  rfl

omit [IsProbabilityMeasure P] in
/-- The energy is the square of the `L²`-seminorm on the product space. -/
theorem energy_eq_eLpNorm_sq {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H)) (T : ℝ) :
    energy P T H = eLpNorm (fun p : Ω × ℝ => H p.1 p.2) 2 (energyMeasure P T) ^ 2 := by
  have hme : AEMeasurable (fun p : Ω × ℝ => (‖H p.1 p.2‖₊ : ℝ≥0∞) ^ 2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    (((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2).aemeasurable
  rw [eLpNorm_sq_eq_lintegral _ (fun p : Ω × ℝ => H p.1 p.2) hm.aestronglyMeasurable, energyMeasure, energy,
    lintegral_prod (fun p : Ω × ℝ => (‖H p.1 p.2‖₊ : ℝ≥0∞) ^ 2) hme]

omit [IsProbabilityMeasure P] in
/-- An integrand of finite energy is square integrable on the product space. -/
theorem memLp_of_energy_ne_top {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H)) {T : ℝ}
    (hfin : energy P T H ≠ ⊤) :
    MemLp (fun p : Ω × ℝ => H p.1 p.2) 2 (energyMeasure P T) := by
  change eLpNorm (fun p : Ω × ℝ => H p.1 p.2) 2 (energyMeasure P T) < ⊤
  refine lt_top_iff_ne_top.mpr fun hcon => hfin ?_
  rw [energy_eq_eLpNorm_sq hm T, hcon]
  simp

/-- Truncating an integrand to the horizon preserves progressive measurability. -/
theorem progressivelyMeasurable_indicator_Icc {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {H : Ω → ℝ → ℝ} (hp : Probability.ProgressivelyMeasurable ℱ H) (T : ℝ) :
    Probability.ProgressivelyMeasurable ℱ
      fun ω s => Set.indicator (Set.Icc (0 : ℝ) T) (H ω) s := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator
        (fun s => Set.indicator (Set.Icc (0 : ℝ) T) (H p.1) s) p.2)
      = Set.indicator ((fun p : Ω × ℝ => p.2) ⁻¹' Set.Icc (0 : ℝ) T)
        (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2) := by
    funext p
    by_cases h2 : p.2 ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem (Set.mem_preimage.mpr h2)]
      by_cases h1 : p.2 ∈ Set.Iic t
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1]
    · rw [Set.indicator_of_notMem fun hc => h2 (Set.mem_preimage.mp hc)]
      by_cases h1 : p.2 ∈ Set.Iic t
      · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
      · rw [Set.indicator_of_notMem h1]
  rw [key]
  exact (hp t).indicator (measurable_snd measurableSet_Icc)

omit [IsProbabilityMeasure P] in
/-- An integrand vanishing off the horizon has no more energy on any other horizon. -/
theorem energy_le_of_vanishing {H : Ω → ℝ → ℝ} {T : ℝ}
    (hz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → H ω s = 0) (T' : ℝ) :
    energy P T' H ≤ energy P T H := by
  refine lintegral_mono fun ω => ?_
  have hind : (fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2)
      = Set.indicator (Set.Icc (0 : ℝ) T) (fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2) := by
    funext s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs, hz ω s hs]
      simp
  calc ∫⁻ s in Set.Icc (0 : ℝ) T', (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∫⁻ s in Set.Icc (0 : ℝ) T ∩ Set.Icc (0 : ℝ) T',
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
        conv_lhs => rw [hind]
        rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
        lintegral_mono' (Measure.restrict_mono Set.inter_subset_left le_rfl) le_rfl

section Complete

variable {T : ℝ} {H : ℕ → Ω → ℝ → ℝ}

omit [IsProbabilityMeasure P] in
/-- An energy-Cauchy sequence of integrands has an `L²`-limit on the product space. -/
theorem exists_energy_limit (hm : ∀ n, Measurable (Function.uncurry (H n)))
    (hfin : ∀ n, energy P T (H n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      energy P T (fun ω s => H m ω s - H n ω s) < ε) :
    ∃ g : Ω × ℝ → ℝ, MemLp g 2 (energyMeasure P T)
      ∧ Tendsto (fun n => eLpNorm ((fun p : Ω × ℝ => H n p.1 p.2) - g) 2 (energyMeasure P T))
          atTop (𝓝 0) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hMem : ∀ n, MemLp (fun p : Ω × ℝ => H n p.1 p.2) 2 (energyMeasure P T) :=
    fun n => memLp_of_energy_ne_top (hm n) (hfin n)
  have hcs : CauchySeq fun n => (hMem n).toLp (fun p : Ω × ℝ => H n p.1 p.2) := by
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm' n hn' => ?_⟩
    rw [Lp.edist_def]
    have hcongr : eLpNorm
          ((((hMem m).toLp (fun p : Ω × ℝ => H m p.1 p.2)) : Ω × ℝ → ℝ)
            - (((hMem n).toLp (fun p : Ω × ℝ => H n p.1 p.2)) : Ω × ℝ → ℝ))
          2 (energyMeasure P T)
        = eLpNorm (fun p : Ω × ℝ => H m p.1 p.2 - H n p.1 p.2) 2 (energyMeasure P T) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hMem m).coeFn_toLp, (hMem n).coeFn_toLp] with p h1 h2
      simp only [Pi.sub_apply]
      rw [h1, h2]
    rw [hcongr]
    rcases lt_or_ge (eLpNorm (fun p : Ω × ℝ => H m p.1 p.2 - H n p.1 p.2)
      2 (energyMeasure P T)) ε with hlt' | hge
    · exact hlt'
    · exfalso
      have hsq : ε ^ 2 ≤ eLpNorm (fun p : Ω × ℝ => H m p.1 p.2 - H n p.1 p.2)
          2 (energyMeasure P T) ^ 2 := pow_le_pow_left' hge 2
      have hlt := hN m hm' n hn'
      rw [energy_eq_eLpNorm_sq ((hm m).sub (hm n)) T] at hlt
      exact absurd hlt (not_lt.mpr hsq)
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨(G : Ω × ℝ → ℝ), Lp.memLp G, ?_⟩
  have hlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ G).mp hG
  refine hlim.congr fun n => ?_
  refine eLpNorm_congr_ae ?_
  filter_upwards [(hMem n).coeFn_toLp] with p h1
  simp only [Pi.sub_apply]
  rw [h1]

/-- The pointwise `limsup` of a subsequence of integrands. -/
noncomputable def limsupIntegrand (H : ℕ → Ω → ℝ → ℝ) (ns : ℕ → ℕ) : Ω → ℝ → ℝ :=
  fun ω s => limsup (fun i => H (ns i) ω s) atTop

omit [IsProbabilityMeasure P] in
/-- **Completeness of the admissible integrands.** An energy-Cauchy sequence of jointly and
progressively measurable integrands vanishing off the horizon has an admissible limit. -/
theorem exists_progressive_energy_limit (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hm : ∀ n, Measurable (Function.uncurry (H n)))
    (hp : ∀ n, Probability.ProgressivelyMeasurable ℱ (H n))
    (hz : ∀ n ω s, s ∉ Set.Icc (0 : ℝ) T → H n ω s = 0)
    (hfin : ∀ n, energy P T (H n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      energy P T (fun ω s => H m ω s - H n ω s) < ε) :
    ∃ K : Ω → ℝ → ℝ, Measurable (Function.uncurry K)
      ∧ Probability.ProgressivelyMeasurable ℱ K
      ∧ (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → K ω s = 0)
      ∧ energy P T K ≠ ⊤
      ∧ Tendsto (fun n => energy P T (fun ω s => H n ω s - K ω s)) atTop (𝓝 0) := by
  obtain ⟨g, hgMem, hgt⟩ := exists_energy_limit hm hfin hcau
  have hMem : ∀ n, MemLp (fun p : Ω × ℝ => H n p.1 p.2) 2 (energyMeasure P T) :=
    fun n => memLp_of_energy_ne_top (hm n) (hfin n)
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (μ := energyMeasure P T) (p := 2)
    (by norm_num) hgt).exists_seq_tendsto_ae
  have hKm : Measurable (Function.uncurry (limsupIntegrand H ns)) :=
    Measurable.limsup fun i => hm (ns i)
  have hKp : Probability.ProgressivelyMeasurable ℱ (limsupIntegrand H ns) :=
    Probability.ProgressivelyMeasurable.limsup fun i => hp (ns i)
  have hKz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → limsupIntegrand H ns ω s = 0 := by
    intro ω s hs
    have h0 : (fun i => H (ns i) ω s) = fun _ => (0 : ℝ) := funext fun i => hz (ns i) ω s hs
    rw [limsupIntegrand, h0]
    exact limsup_const 0
  have hKg : (fun p : Ω × ℝ => limsupIntegrand H ns p.1 p.2) =ᵐ[energyMeasure P T] g := by
    filter_upwards [hae] with p hp'
    exact hp'.limsup_eq
  have hKfin : energy P T (limsupIntegrand H ns) ≠ ⊤ := by
    rw [energy_eq_eLpNorm_sq hKm T, eLpNorm_congr_ae hKg]
    exact ENNReal.pow_ne_top hgMem.eLpNorm_lt_top.ne
  have hEq : ∀ n, energy P T (fun ω s => H n ω s - limsupIntegrand H ns ω s)
      = eLpNorm ((fun p : Ω × ℝ => H n p.1 p.2) - g) 2 (energyMeasure P T) ^ 2 := by
    intro n
    rw [energy_eq_eLpNorm_sq ((hm n).sub hKm) T]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hKg] with p h1
    simp only [Pi.sub_apply]
    rw [h1]
  refine ⟨limsupIntegrand H ns, hKm, hKp, hKz, hKfin, ?_⟩
  simp only [hEq]
  have hcont : Continuous fun x : ℝ≥0∞ => x ^ 2 := ENNReal.continuous_pow 2
  simpa [Function.comp_def] using (hcont.tendsto 0).comp hgt

end Complete

end LevyStochCalc.Brownian.Ito
