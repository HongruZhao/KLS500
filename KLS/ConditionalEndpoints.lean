import KLS.IsotropicLowerBound
import KLS.Targets
import KLS.TruncationEnergy

/-!
# Explicitly conditional consequences of finiteness

The major analytic obligation is to prove `universalPoincareConstant < ⊤`.
This module does not prove that obligation. It shows that, if finiteness is
eventually established, the actual imported optimal constants attain the
L² inequality. The finite-energy extension is a separate analytic bridge.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

noncomputable section
namespace KLS

/-- At any admissible measure, a finite optimal constant is attained. Its
positivity is proved from isotropy rather than postulated. -/
theorem admissibleMeasure.optimal_attained
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (hn : 1 ≤ n)
    (hfinite : poincareConstant μ < ⊤) :
    (poincareConstant μ).toNNReal ∈ poincareConstants μ :=
  optimal_toNNReal_mem (poincareConstants_nonempty_iff.mpr hfinite)
    (hμ.poincareConstant_pos hn)

/-- The optimal universal constant satisfies the full L² inequality if it is
finite. This statement names the unresolved assumption in its type. -/
theorem fullL2Poincare_of_universal_finite
    (hfinite : universalPoincareConstant < ⊤) :
    FullL2Poincare universalPoincareConstant := by
  intro n hn μ hμ f hf
  have hle := poincareConstant_le_universal hn hμ
  have hμfinite : poincareConstant μ < ⊤ := hle.trans_lt hfinite
  have hne := poincareConstants_nonempty_iff.mpr hμfinite
  exact (variance_le_optimal_mul_energy hne (hμ.poincareConstant_pos hn) hf).trans
    (mul_le_mul_left hle _)

/-- The compact-set class still needs its absolute-continuity theorem. This
definition isolates that obligation without adding it to the admissible class. -/
def FullClassAbsolutelyContinuous : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ μ : Measure (Space n), admissibleMeasure μ →
    μ ≪ (volume : Measure (Space n))

/-- Once the two displayed unresolved obligations are proved, the finite-energy
endpoint at the optimal universal constant follows with no conversion loss. -/
theorem fullFiniteEnergyPoincare_of_finite_and_absolutelyContinuous
    (hfinite : universalPoincareConstant < ⊤)
    (habs : FullClassAbsolutelyContinuous) :
    FullFiniteEnergyPoincare universalPoincareConstant := by
  intro n hn μ hμ f hf he
  let : IsProbabilityMeasure μ := hμ.isProb
  have hne : universalPoincareConstant ≠ ⊤ := ne_of_lt hfinite
  have hC : universalPoincareConstant.toNNReal ∈ poincareConstants μ := by
    intro g hg
    rw [ENNReal.coe_toNNReal hne]
    exact fullL2Poincare_of_universal_finite hfinite n hn μ hμ g hg
  simpa only [ENNReal.coe_toNNReal hne] using
    finiteEnergy_poincare_of_mem_constants (habs n hn μ hμ) hC hf he

/-- Existence of one fully admissible positive-dimensional example forces the
universal constant to be positive, even before its finiteness is known. -/
theorem one_le_universal_of_example
    {n : ℕ} {μ : Measure (Space n)} (hn : 1 ≤ n) (hμ : admissibleMeasure μ) :
    1 ≤ universalPoincareConstant :=
  (hμ.one_le_poincareConstant hn).trans (poincareConstant_le_universal hn hμ)

/-- Finite positive numerical upper bounds for all the optimal constants. -/
def positiveUniversalBounds : Set ℝ≥0 :=
  {C | 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ μ : Measure (Space n),
    admissibleMeasure μ → poincareConstant μ ≤ (C : ℝ≥0∞)}

/-- A conditional, attained infimum characterization. This does not determine
the numerical sharp constant and does not prove the finiteness hypothesis. -/
theorem universal_eq_inf_positive_bounds
    (hpos : 0 < universalPoincareConstant)
    (hfinite : universalPoincareConstant < ⊤) :
    universalPoincareConstant =
      sInf ((fun C : ℝ≥0 => (C : ℝ≥0∞)) '' positiveUniversalBounds) := by
  have hne : universalPoincareConstant ≠ ⊤ := ne_of_lt hfinite
  have hmem : universalPoincareConstant.toNNReal ∈ positiveUniversalBounds := by
    constructor
    · exact ENNReal.toNNReal_pos (ne_of_gt hpos) hne
    · intro n hn μ hμ
      rw [ENNReal.coe_toNNReal hne]
      exact poincareConstant_le_universal hn hμ
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨C, hC, rfl⟩
    exact universal_le_iff.mpr hC.2
  · have hs := sInf_le (Set.mem_image_of_mem (fun C : ℝ≥0 => (C : ℝ≥0∞)) hmem)
    simpa only [ENNReal.coe_toNNReal hne] using hs

end KLS
end

#print axioms KLS.admissibleMeasure.optimal_attained
#print axioms KLS.fullL2Poincare_of_universal_finite
#print axioms KLS.fullFiniteEnergyPoincare_of_finite_and_absolutelyContinuous
#print axioms KLS.one_le_universal_of_example
#print axioms KLS.universal_eq_inf_positive_bounds
