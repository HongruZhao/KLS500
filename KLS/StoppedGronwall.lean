import LevyStochCalc.Ito.PicardWindow

/-! Zero-initial-data integral Gronwall via the genuine Bielecki energy estimate. -/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
namespace KLS.LocalDiffusion
open LevyStochCalc.Ito.Picard
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}

/-- A finite-energy process satisfying the homogeneous integral second-moment
estimate vanishes at every fixed time. The concrete stopped estimates are
discharged in the local compatibility consumer. -/
theorem ae_zero_of_perTime_energy_bound
    {Z : ℝ → Ω → Fin n → ℝ}
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    (hS : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    {T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C)
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i, (Z t ω i) ^ 2) ∂P ≤ ENNReal.ofReal C *
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, Z t =ᵐ[P] 0 := by
  let β : ℝ := C + 1
  have hβ : 0 < β := by dsimp [β]; linarith
  have hc : C / (2 * β) < 1 := by
    apply (div_lt_one (by positivity : 0 < 2 * β)).mpr
    dsimp [β]
    linarith
  have hq : (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) < 1 :=
    ENNReal.rpow_lt_one (by
      have hd : 0 ≤ C / (2 * β) := div_nonneg hC (by positivity)
      simpa using (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hd).2 hc) (by norm_num)
  have hfin : bieleckiNorm (P := P) β T Z ≠ ⊤ :=
    (lt_of_le_of_lt (bieleckiNorm_le_bieleckiNorm_zero hβ.le T Z)
      (bieleckiNorm_lt_top_of_supL2 hT hS)).ne
  have hz : bieleckiNorm (P := P) β T Z = 0 :=
    eq_zero_of_le_mul_self hfin hq (bieleckiNorm_le_of_perTime hβ hC Z Z hZ hbd)
  intro t ht
  have hZm : Measurable (Function.uncurry Z) := hZ.comp measurable_swap
  have hm (u : ℝ) (i : Fin n) : Measurable (fun ω => Z u ω i) :=
    (measurable_pi_apply i).comp (Measurable.of_uncurry_left hZm)
  filter_upwards [ae_eq_zero_of_bieleckiNorm_eq_zero hm hz ht] with ω hω
  exact funext hω

end KLS.LocalDiffusion
#print axioms KLS.LocalDiffusion.ae_zero_of_perTime_energy_bound
