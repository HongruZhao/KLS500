import LevyStochCalc.Poisson.Filtered

/- A concrete zero-intensity Poisson random measure, on any probability space. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace KLSLevyProbe
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {E : Type v} [MeasurableSpace E]
open LevyStochCalc.Poisson

lemma poissonMeasure_zero_eq_dirac : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro n
  cases n with
  | zero => simp [poissonMeasure_singleton]
  | succ n => simp [poissonMeasure_singleton]

lemma poissonMeasureENN_zero_eq_dirac : poissonMeasureENN 0 = Measure.dirac (0 : ℝ≥0∞) := by
  rw [poissonMeasureENN, poissonMeasure_zero_eq_dirac]
  simp

lemma iIndepFun_const_zero {ι : Type*} :
    iIndepFun (fun (_ : ι) (_ : Ω) => (0 : ℝ≥0∞)) P := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    by_cases hzero : (0 : ℝ≥0∞) ∈ sets i
    · simpa [hi, Set.preimage_const_of_mem hzero] using ih (fun j hj => hsets j (Finset.mem_insert_of_mem hj))
    · simp [hi, Set.preimage_const_of_notMem hzero]

noncomputable def zeroPoisson : PoissonRandomMeasure P (0 : Measure E) where
  N := fun _ => 0
  measurable_eval := fun _ => measurable_const
  integer_valued := by intro B _ _; exact Filter.Eventually.of_forall fun _ => ⟨0, by simp⟩
  infinite_at_infinite_intensity := by
    intro B _ h
    simp [referenceIntensity] at h
  poisson_law := by
    intro B _ _
    simp [referenceIntensity, poissonMeasureENN_zero_eq_dirac, Measure.map_const]
  independent_disjoint := by
    intro ι _ B _ _
    exact iIndepFun_const_zero P
  joint_past_future_independent := by
    intro s t _ _ A _ _
    simpa only [Measure.coe_zero, Pi.zero_apply, MeasurableSpace.comap_const]
      using (indep_bot_right (μ := P) (⨆ B ∈
        {C : Set (ℝ × E) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C},
          MeasurableSpace.comap (fun (_ : Ω) => (0 : ℝ≥0∞)) inferInstance))

theorem zeroPoisson_isPoissonFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    IsPoissonFiltration (zeroPoisson (E := E) P) ℱ where
  measurable := by intro t B _ _; exact measurable_const
  indep_future := by
    intro s _
    simpa only [zeroPoisson, Measure.coe_zero, Pi.zero_apply,
      MeasurableSpace.comap_const, iSup_bot] using (indep_bot_right (μ := P) (ℱ s))

#print axioms zeroPoisson
#print axioms zeroPoisson_isPoissonFiltration
end KLSLevyProbe
