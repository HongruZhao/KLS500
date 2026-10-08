/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.Compensated
import LevyStochCalc.Poisson.CompensatedIntegrandComplete
import LevyStochCalc.Brownian.ItoLinear

/-!
# Linearity of the compensated Poisson integral

The compensated integral is built as an `L²` limit of elementary integrals, which is not itself a
linear construction, so linearity comes from the isometries instead: they fix every squared
`L²`-distance among the integrals of two integrands and of their sum, and the parallelogram law
for the marked energies then forces the sum relation. The same three-distance argument gives the
scalar rule.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The marked energy density of an integrand at a sample point. -/
noncomputable def markedDensity (ν : Measure E) (T : ℝ) (φ : Ω → ℝ → E → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume

omit [IsProbabilityMeasure P] in
theorem measurable_markedDensity {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (T : ℝ) :
    Measurable (markedDensity (Ω := Ω) ν T φ) := by
  have hsq : Measurable fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2
  have hmid : Measurable fun q : (Ω × ℝ) × E => (‖φ q.1.1 q.1.2 q.2‖₊ : ℝ≥0∞) ^ 2 :=
    hsq.comp (by fun_prop : Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))
  exact (hmid.lintegral_prod_right' (ν := ν)).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) T))

/-- The squared extended norm of the mark integral, at a fixed sample point and time. -/
theorem measurable_markSlice {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (ω : Ω) :
    Measurable fun s : ℝ => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  have hsq : Measurable fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2
  have hslice : Measurable fun q : ℝ × E => (‖φ ω q.1 q.2‖₊ : ℝ≥0∞) ^ 2 :=
    hsq.comp (measurable_prodMk_left (x := ω))
  exact hslice.lintegral_prod_right' (ν := ν)

section Parallelogram

variable {φ₁ φ₂ : Ω → ℝ → E → ℝ}

omit [IsProbabilityMeasure P] in
/-- **The parallelogram law for the marked energies.** -/
theorem lintegral_markedEnergy_parallelogram
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2) (T : ℝ) :
    markedEnergy P ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e)
        + markedEnergy P ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e)
      = 2 * markedEnergy P ν T φ₁ + 2 * markedEnergy P ν T φ₂ := by
  have hma : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 + φ₂ p.1 p.2.1 p.2.2 :=
    hm₁.add hm₂
  have hpt : ∀ a b : ℝ, (‖a + b‖₊ : ℝ≥0∞) ^ 2 + (‖a - b‖₊ : ℝ≥0∞) ^ 2
      = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
    intro a b
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
      sq_nnnorm_eq_ofReal_sq, h2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hmark : ∀ (ω : Ω) (s : ℝ),
      (∫⁻ e, (‖φ₁ ω s e + φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          + ∫⁻ e, (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν
        = 2 * (∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          + 2 * ∫⁻ e, (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    intro ω s
    have k1 : Measurable fun e => (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
      ((measurable_nnnorm.comp ((hm₁.comp (measurable_prodMk_left (x := ω))).comp
        (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal).pow_const 2
    have k2 : Measurable fun e => (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
      ((measurable_nnnorm.comp ((hm₂.comp (measurable_prodMk_left (x := ω))).comp
        (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal).pow_const 2
    have ka : Measurable fun e => (‖φ₁ ω s e + φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
      ((measurable_nnnorm.comp ((hma.comp (measurable_prodMk_left (x := ω))).comp
        (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal).pow_const 2
    rw [← lintegral_add_left ka, ← lintegral_const_mul 2 k1, ← lintegral_const_mul 2 k2,
      ← lintegral_add_left (k1.const_mul 2)]
    exact lintegral_congr fun e => hpt _ _
  have htime : ∀ ω : Ω,
      markedDensity ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e) ω
          + markedDensity ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e) ω
        = 2 * markedDensity ν T φ₁ ω + 2 * markedDensity ν T φ₂ ω := by
    intro ω
    have sa := measurable_markSlice (ν := ν)
      (φ := fun ω s e => φ₁ ω s e + φ₂ ω s e) hma ω
    have s1 := measurable_markSlice (ν := ν) (φ := φ₁) hm₁ ω
    have s2 := measurable_markSlice (ν := ν) (φ := φ₂) hm₂ ω
    rw [markedDensity, markedDensity, markedDensity, markedDensity,
      ← lintegral_add_left sa, ← lintegral_const_mul 2 s1, ← lintegral_const_mul 2 s2,
      ← lintegral_add_left (s1.const_mul 2)]
    exact lintegral_congr fun s => hmark ω s
  have e1 := measurable_markedDensity (ν := ν) (φ := φ₁) hm₁ T
  have e2 := measurable_markedDensity (ν := ν) (φ := φ₂) hm₂ T
  have ea := measurable_markedDensity (ν := ν)
    (φ := fun ω s e => φ₁ ω s e + φ₂ ω s e) hma T
  rw [markedEnergy, markedEnergy, markedEnergy, markedEnergy]
  rw [show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e + φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
        = markedDensity ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e) from rfl,
    show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
        = markedDensity ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e) from rfl,
    show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
        = markedDensity ν T φ₁ from rfl,
    show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
        = markedDensity ν T φ₂ from rfl,
    ← lintegral_add_left ea, ← lintegral_const_mul 2 e1, ← lintegral_const_mul 2 e2,
    ← lintegral_add_left (e1.const_mul 2)]
  exact lintegral_congr fun ω => htime ω

omit [IsProbabilityMeasure P] in
/-- A marked integrand dominated pointwise by twice the sum of two others has energy bounded by
twice the sum of theirs. -/
theorem markedEnergy_le_two_mul_add {ψ : Ω → ℝ → E → ℝ}
    (hbound : ∀ ω s e, (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2))
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2) (T : ℝ) :
    markedEnergy P ν T ψ ≤ 2 * markedEnergy P ν T φ₁ + 2 * markedEnergy P ν T φ₂ := by
  have e1 := measurable_markedDensity (ν := ν) (φ := φ₁) hm₁ T
  have e2 := measurable_markedDensity (ν := ν) (φ := φ₂) hm₂ T
  rw [markedEnergy, markedEnergy, markedEnergy,
    show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
      = markedDensity ν T φ₁ from rfl,
    show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
      = markedDensity ν T φ₂ from rfl,
    ← lintegral_const_mul 2 e1, ← lintegral_const_mul 2 e2,
    ← lintegral_add_left (e1.const_mul 2)]
  refine lintegral_mono fun ω => ?_
  have s1 := measurable_markSlice (ν := ν) (φ := φ₁) hm₁ ω
  have s2 := measurable_markSlice (ν := ν) (φ := φ₂) hm₂ ω
  rw [markedDensity, markedDensity, ← lintegral_const_mul 2 s1, ← lintegral_const_mul 2 s2,
    ← lintegral_add_left (s1.const_mul 2)]
  refine lintegral_mono fun s => ?_
  have k1 : Measurable fun e => (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp ((hm₁.comp (measurable_prodMk_left (x := ω))).comp
      (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal).pow_const 2
  have k2 : Measurable fun e => (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp ((hm₂.comp (measurable_prodMk_left (x := ω))).comp
      (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal).pow_const 2
  rw [← lintegral_const_mul 2 k1, ← lintegral_const_mul 2 k2,
    ← lintegral_add_left (k1.const_mul 2)]
  refine lintegral_mono fun e => ?_
  calc (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2) := hbound ω s e
    _ = 2 * (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 := by ring

omit [IsProbabilityMeasure P] in
/-- A marked integrand dominated by twice the sum of two square-integrable energies is itself
square integrable. -/
theorem markedEnergy_lt_top_of_bound {ψ : Ω → ℝ → E → ℝ}
    (hbound : ∀ ω s e, (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2))
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hq₁ : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ₁ < ⊤)
    (hq₂ : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ₂ < ⊤) :
    ∀ T : ℝ, 0 < T → markedEnergy P ν T ψ < ⊤ := fun T hT =>
  lt_of_le_of_lt (markedEnergy_le_two_mul_add hbound hm₁ hm₂ T) (ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (by simp) (hq₁ T hT), ENNReal.mul_lt_top (by simp) (hq₂ T hT)⟩)

omit [IsProbabilityMeasure P] in
/-- The same bound in the `≠ ⊤` form, at a single horizon. -/
theorem markedEnergy_ne_top_of_bound {ψ : Ω → ℝ → E → ℝ} {T : ℝ}
    (hbound : ∀ ω s e, (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2))
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (h1 : markedEnergy P ν T φ₁ ≠ ⊤) (h2 : markedEnergy P ν T φ₂ ≠ ⊤) :
    markedEnergy P ν T ψ ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (by simp) h1, ENNReal.mul_ne_top (by simp) h2⟩)
    (markedEnergy_le_two_mul_add hbound hm₁ hm₂ T)

omit [IsProbabilityMeasure P] in
/-- The energy of a sum is finite when both energies are. -/
theorem markedEnergy_add_ne_top {T : ℝ}
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (h1 : markedEnergy P ν T φ₁ ≠ ⊤) (h2 : markedEnergy P ν T φ₂ ≠ ⊤) :
    markedEnergy P ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e) ≠ ⊤ :=
  markedEnergy_ne_top_of_bound (fun _ _ _ => sq_nnnorm_add_le_two_mul _ _) hm₁ hm₂ h1 h2

end Parallelogram

section Linearity

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)

include hℱ in
/-- The compensated integral is square integrable. -/
theorem stochasticIntegral_memLp (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤) (T : ℝ) :
    MemLp (stochasticIntegral N ℱ hℱ φ hm hp hq T) 2 P :=
  MemLp.ae_eq (stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq T).symm
    (process_memLp N ℱ hℱ φ hm hp hq T)

include hℱ in
/-- **Additivity of the compensated integral.** -/
theorem stochasticIntegral_add {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hp₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hq₁ : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ₁ < ⊤)
    (hq₂ : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ₂ < ⊤)
    (hma : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 + φ₂ p.1 p.2.1 p.2.2)
    (hpa : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => φ₁ ω s e + φ₂ ω s e)
    (hqa : ∀ T : ℝ, 0 < T → markedEnergy P ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e) < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegral N ℱ hℱ (fun ω s e => φ₁ ω s e + φ₂ ω s e) hma hpa hqa T
      =ᵐ[P] fun ω => stochasticIntegral N ℱ hℱ φ₁ hm₁ hp₁ hq₁ T ω
        + stochasticIntegral N ℱ hℱ φ₂ hm₂ hp₂ hq₂ T ω := by
  have hqd : ∀ T : ℝ, 0 < T → markedEnergy P ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e) < ⊤ :=
    markedEnergy_lt_top_of_bound (fun ω s e => sq_nnnorm_sub_le_two_mul _ _) hm₁ hm₂ hq₁ hq₂
  refine ae_eq_add_of_sq_distances
    (stochasticIntegral_memLp N ℱ hℱ φ₁ hm₁ hp₁ hq₁ T)
    (stochasticIntegral_memLp N ℱ hℱ φ₂ hm₂ hp₂ hq₂ T)
    (stochasticIntegral_memLp N ℱ hℱ (fun ω s e => φ₁ ω s e + φ₂ ω s e) hma hpa hqa T)
    (hq₁ T hT).ne (hq₂ T hT).ne (hqa T hT).ne (hqd T hT).ne
    (isometry_stochasticIntegral N ℱ hℱ φ₁ hm₁ hp₁ hq₁ T hT)
    (isometry_stochasticIntegral N ℱ hℱ φ₂ hm₂ hp₂ hq₂ T hT)
    (isometry_stochasticIntegral N ℱ hℱ (fun ω s e => φ₁ ω s e + φ₂ ω s e) hma hpa hqa T hT)
    ?_ ?_
    (itoIsometry_diff_compensated N ℱ hℱ φ₁ φ₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ T hT)
    (lintegral_markedEnergy_parallelogram (P := P) (ν := ν) hm₁ hm₂ T)
  · refine Eq.trans (itoIsometry_diff_compensated N ℱ hℱ
      (fun ω s e => φ₁ ω s e + φ₂ ω s e) φ₁ hma hm₁ hpa hp₁ hqa hq₁ T hT) ?_
    exact lintegral_congr fun ω => lintegral_congr fun s => lintegral_congr fun e => by ring_nf
  · refine Eq.trans (itoIsometry_diff_compensated N ℱ hℱ
      (fun ω s e => φ₁ ω s e + φ₂ ω s e) φ₂ hma hm₂ hpa hp₂ hqa hq₂ T hT) ?_
    exact lintegral_congr fun ω => lintegral_congr fun s => lintegral_congr fun e => by ring_nf

omit [IsProbabilityMeasure P] in
/-- Scaling a marked integrand scales its energy by the square of the scalar. -/
theorem lintegral_markedEnergy_const_mul {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (c T : ℝ) :
    markedEnergy P ν T (fun ω s e => c * φ ω s e)
      = ENNReal.ofReal (c ^ 2) * markedEnergy P ν T φ := by
  have hpt : ∀ a : ℝ, (‖c * a‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (c ^ 2) * (‖a‖₊ : ℝ≥0∞) ^ 2 := by
    intro a
    rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
      ← ENNReal.ofReal_mul (sq_nonneg c)]
    congr 1
    ring
  have e := measurable_markedDensity (ν := ν) (φ := φ) hm T
  rw [markedEnergy, markedEnergy,
    show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
      = markedDensity ν T φ from rfl, ← lintegral_const_mul _ e]
  refine lintegral_congr fun ω => ?_
  have s1 := measurable_markSlice (ν := ν) (φ := φ) hm ω
  rw [markedDensity, ← lintegral_const_mul _ s1]
  refine lintegral_congr fun s => ?_
  have k1 : Measurable fun e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp ((hm.comp (measurable_prodMk_left (x := ω))).comp
      (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal).pow_const 2
  rw [← lintegral_const_mul _ k1]
  exact lintegral_congr fun e => hpt _

omit [IsProbabilityMeasure P] in
/-- The energy of a scalar multiple is finite when the energy is. -/
theorem markedEnergy_const_mul_ne_top {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) {T : ℝ}
    (h : markedEnergy P ν T φ ≠ ⊤) (c : ℝ) :
    markedEnergy P ν T (fun ω s e => c * φ ω s e) ≠ ⊤ := by
  rw [lintegral_markedEnergy_const_mul (P := P) (ν := ν) hm c T]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h

include hℱ in
/-- **Homogeneity of the compensated integral.** -/
theorem stochasticIntegral_const_mul {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤) (c : ℝ)
    (hmc : Measurable fun p : Ω × ℝ × E => c * φ p.1 p.2.1 p.2.2)
    (hpc : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => c * φ ω s e)
    (hqc : ∀ T : ℝ, 0 < T → markedEnergy P ν T (fun ω s e => c * φ ω s e) < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegral N ℱ hℱ (fun ω s e => c * φ ω s e) hmc hpc hqc T
      =ᵐ[P] fun ω => c * stochasticIntegral N ℱ hℱ φ hm hp hq T ω := by
  have hscale : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖c * φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      = ENNReal.ofReal (c ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
    lintegral_markedEnergy_const_mul (P := P) (ν := ν) (φ := φ) hm c T
  have hdiff : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖c * φ ω s e - φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      = ENNReal.ofReal ((c - 1) ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
    refine Eq.trans ?_
      (lintegral_markedEnergy_const_mul (P := P) (ν := ν) (φ := φ) hm (c - 1) T)
    exact lintegral_congr fun ω => lintegral_congr fun s => lintegral_congr fun e => by ring_nf
  refine ae_eq_const_mul_of_sq_distances
    (stochasticIntegral_memLp N ℱ hℱ (fun ω s e => c * φ ω s e) hmc hpc hqc T)
    (stochasticIntegral_memLp N ℱ hℱ φ hm hp hq T)
    (isometry_stochasticIntegral N ℱ hℱ (fun ω s e => c * φ ω s e) hmc hpc hqc T hT)
    (isometry_stochasticIntegral N ℱ hℱ φ hm hp hq T hT)
    (itoIsometry_diff_compensated N ℱ hℱ (fun ω s e => c * φ ω s e) φ hmc hm hpc hp
      hqc hq T hT) ?_ ?_
  · rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg c)]
  · rw [hdiff, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg (c - 1))]

end Linearity

end LevyStochCalc.Poisson.Compensated
