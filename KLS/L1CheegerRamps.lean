import KLS.DistanceRamp

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal

noncomputable section
namespace KLS

/-- Both half-mass inequalities defining a probability median. -/
def IsProbabilityMedian {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) (m : ℝ) : Prop :=
  (1 / 2 : ℝ≥0∞) ≤ μ {x | f x ≤ m} ∧ (1 / 2 : ℝ≥0∞) ≤ μ {x | m ≤ f x}

/-- Full locally Lipschitz L¹ median inequality, with extended gradient integral.
No finiteness of the gradient integral or regularity of the density is hidden. -/
def L1MedianCheeger {n : ℕ} (μ : Measure (Space n)) (K : ℝ) : Prop :=
  ∀ f : Space n → ℝ, LocallyLipschitz f → Integrable f μ →
    ∃ m : ℝ, IsProbabilityMedian μ f m ∧
      (∫⁻ x, ENNReal.ofReal |f x - m| ∂μ) ≤
        ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal ‖gradient f x‖ ∂μ

/-- Every scalar center of an indicator has deviation at least the smaller mass.
This estimate does not need the center to be a median. -/
theorem min_measure_le_indicator_deviation {n : ℕ} (μ : Measure (Space n))
    {A : Set (Space n)} (hA : MeasurableSet A) (m : ℝ) :
    min (μ A) (μ Aᶜ) ≤
      ∫⁻ x, ENNReal.ofReal |A.indicator (fun _ => (1 : ℝ)) x - m| ∂μ := by
  classical
  have hsplit : (∫⁻ x, ENNReal.ofReal |A.indicator (fun _ => (1 : ℝ)) x - m| ∂μ) =
      ENNReal.ofReal |1 - m| * μ A + ENNReal.ofReal |m| * μ Aᶜ := by
    calc
      _ = ∫⁻ x, A.indicator (fun _ => ENNReal.ofReal |1 - m|) x +
          Aᶜ.indicator (fun _ => ENNReal.ofReal |m|) x ∂μ := by
        apply lintegral_congr
        intro x
        by_cases hx : x ∈ A <;> simp [hx]
      _ = _ := by
        rw [lintegral_add_left (measurable_const.indicator hA),
          lintegral_indicator_const hA, lintegral_indicator_const hA.compl]
  rw [hsplit]
  have hab : (1 : ℝ≥0∞) ≤ ENNReal.ofReal |1 - m| + ENNReal.ofReal |m| := by
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    have : (1 : ℝ) ≤ |1 - m| + |m| := by
      simpa using (abs_add_le (1 - m) m)
    simpa using ENNReal.ofReal_le_ofReal this
  calc
    min (μ A) (μ Aᶜ) ≤ (ENNReal.ofReal |1 - m| + ENNReal.ofReal |m|) *
        min (μ A) (μ Aᶜ) := by simpa only [one_mul] using mul_le_mul_left hab (min (μ A) (μ Aᶜ))
    _ = ENNReal.ofReal |1 - m| * min (μ A) (μ Aᶜ) +
        ENNReal.ofReal |m| * min (μ A) (μ Aᶜ) := add_mul _ _ _
    _ ≤ _ := add_le_add (mul_le_mul_right (min_le_left _ _) _)
      (mul_le_mul_right (min_le_right _ _) _)

theorem distanceRamp_lintegral_gradient_le {n : ℕ} (μ : Measure (Space n))
    {A : Set (Space n)} (hA : MeasurableSet A) (hne : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ x, ENNReal.ofReal ‖gradient (distanceRamp A ε) x‖ ∂μ) ≤
      ENNReal.ofReal ε⁻¹ * μ (thickening ε A \ A) := by
  classical
  calc
    _ ≤ ∫⁻ x, (thickening ε A \ A).indicator (fun _ => ENNReal.ofReal ε⁻¹) x ∂μ := by
      apply lintegral_mono
      intro x
      have h := ENNReal.ofReal_le_ofReal (distanceRamp_gradient_bound hne hε x)
      by_cases hx : x ∈ thickening ε A \ A <;> simpa [hx] using h
    _ = _ := lintegral_indicator_const (isOpen_thickening.measurableSet.diff hA) _

theorem distanceRamp_lintegral_error_le {n : ℕ} (μ : Measure (Space n))
    {A : Set (Space n)} (hA : MeasurableSet A) (hne : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ x, ENNReal.ofReal |A.indicator (fun _ => (1 : ℝ)) x - distanceRamp A ε x| ∂μ) ≤
      μ (thickening ε A \ A) := by
  classical
  calc
    _ ≤ ∫⁻ x, (thickening ε A \ A).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
      apply lintegral_mono
      intro x
      have h := ENNReal.ofReal_le_ofReal (distanceRamp_indicator_error hne hε x)
      by_cases hx : x ∈ thickening ε A \ A <;> simpa [hx] using h
    _ = _ := lintegral_indicator_const (isOpen_thickening.measurableSet.diff hA) 1 |>.trans (one_mul _)

/-- The enlargement error is retained. Consequently arbitrary nonclosed sets
are allowed, including sets whose closures have strictly larger measure. -/
theorem L1MedianCheeger.min_measure_le_ramp_shell {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {K : ℝ} (hC : L1MedianCheeger μ K)
    {A : Set (Space n)} (hA : MeasurableSet A) (hne : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    min (μ A) (1 - μ A) ≤
      ENNReal.ofReal K * (ENNReal.ofReal ε⁻¹ * μ (thickening ε A \ A)) +
        μ (thickening ε A \ A) := by
  classical
  obtain ⟨m, _, hm⟩ := hC (distanceRamp A ε) (distanceRamp_lipschitz A hε).locallyLipschitz
    (distanceRamp_integrable μ A hε)
  have hmin := min_measure_le_indicator_deviation μ hA m
  rw [measure_compl hA (measure_ne_top μ A), measure_univ] at hmin
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal |A.indicator (fun _ => (1 : ℝ)) x - m| ∂μ := hmin
    _ ≤ ∫⁻ x, ENNReal.ofReal |distanceRamp A ε x - m| +
        ENNReal.ofReal |A.indicator (fun _ => (1 : ℝ)) x - distanceRamp A ε x| ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have h := abs_add_le (distanceRamp A ε x - m)
        (A.indicator (fun _ => (1 : ℝ)) x - distanceRamp A ε x)
      convert h using 1
      congr 1
      ring
    _ = (∫⁻ x, ENNReal.ofReal |distanceRamp A ε x - m| ∂μ) +
        ∫⁻ x, ENNReal.ofReal |A.indicator (fun _ => (1 : ℝ)) x - distanceRamp A ε x| ∂μ :=
      lintegral_add_left (((distanceRamp_lipschitz A hε).continuous.measurable.sub_const m).abs.ennreal_ofReal) _
    _ ≤ _ := add_le_add (hm.trans (mul_le_mul_right
      (distanceRamp_lintegral_gradient_le μ hA hne hε) _))
        (distanceRamp_lintegral_error_le μ hA hne hε)

end KLS
end
