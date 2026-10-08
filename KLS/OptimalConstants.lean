import KLS.Definitions

/-!
# Order properties of the actual Poincaré constants

These are unconditional consequences of the definitions, with the hypotheses
printed explicitly. In particular, existence of a finite constant and the
positive lower bound are NOT proved here for the KLS measure class. No theorem
in this module asserts the KLS conjecture.

The infinite-energy case is separated because multiplication by `⊤` does not
preserve infima at zero (`0 * ⊤ = 0`).
-/

open scoped ENNReal NNReal
open MeasureTheory Set

noncomputable section
namespace KLS

variable {n : ℕ} {μ : Measure (Space n)}

theorem poincareConstant_le_of_mem {C : ℝ≥0}
    (hC : C ∈ poincareConstants μ) : poincareConstant μ ≤ (C : ℝ≥0∞) :=
  sInf_le ⟨C, hC, rfl⟩

theorem le_poincareConstant_of_forall {a : ℝ≥0∞}
    (ha : ∀ C ∈ poincareConstants μ, a ≤ (C : ℝ≥0∞)) :
    a ≤ poincareConstant μ := by
  apply le_sInf
  rintro _ ⟨C, hC, rfl⟩
  exact ha C hC

theorem poincareConstant_eq_top_of_empty (h : poincareConstants μ = ∅) :
    poincareConstant μ = ⊤ := by
  simp [poincareConstant, h]

theorem poincareConstants_mono {C D : ℝ≥0}
    (hC : C ∈ poincareConstants μ) (hCD : C ≤ D) :
    D ∈ poincareConstants μ := by
  intro f hf
  exact (hC f hf).trans (mul_le_mul_left (by exact_mod_cast hCD) _)

theorem poincareConstant_lt_top_of_mem {C : ℝ≥0}
    (hC : C ∈ poincareConstants μ) : poincareConstant μ < ⊤ :=
  (poincareConstant_le_of_mem hC).trans_lt ENNReal.coe_lt_top

theorem poincareConstants_nonempty_iff :
    (poincareConstants μ).Nonempty ↔ poincareConstant μ < ⊤ := by
  constructor
  · rintro ⟨C, hC⟩
    exact poincareConstant_lt_top_of_mem hC
  · intro hfin
    by_contra hne
    have hempty : poincareConstants μ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [poincareConstant_eq_top_of_empty hempty] at hfin
    exact (lt_irrefl _) hfin

/-- Infimum admissibility for finite energy only needs a nonempty set of
finite admissible constants, and does not require positivity of the infimum. -/
theorem variance_le_optimal_mul_energy_of_finite
    (hne : (poincareConstants μ).Nonempty) {f : Space n → ℝ}
    (hf : LocallyLipschitzTests μ f) (he : energy μ f ≠ ⊤) :
    variance μ f ≤ poincareConstant μ * energy μ f := by
  by_cases he0 : energy μ f = 0
  · obtain ⟨C, hC⟩ := hne
    simpa [he0] using hC f hf
  · apply (ENNReal.div_le_iff he0 he).mp
    apply le_poincareConstant_of_forall
    intro C hC
    exact (ENNReal.div_le_iff he0 he).mpr (hC f hf)

/-- With a positive optimal constant, infinite energy is harmless. The
positivity assumption must later be established from isotropy. -/
theorem variance_le_optimal_mul_energy
    (hne : (poincareConstants μ).Nonempty) (hpos : 0 < poincareConstant μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ poincareConstant μ * energy μ f := by
  by_cases he : energy μ f = ⊤
  · simp [he, ENNReal.mul_top (ne_of_gt hpos)]
  · exact variance_le_optimal_mul_energy_of_finite hne hf he

/-- Real conversion occurs only after finiteness has been proved from an
actual finite admissible constant. -/
theorem optimal_toNNReal_mem
    (hne : (poincareConstants μ).Nonempty) (hpos : 0 < poincareConstant μ) :
    (poincareConstant μ).toNNReal ∈ poincareConstants μ := by
  obtain ⟨C, hC⟩ := hne
  have hfin : poincareConstant μ ≠ ⊤ :=
    ne_of_lt (poincareConstant_lt_top_of_mem hC)
  intro f hf
  rw [ENNReal.coe_toNNReal hfin]
  exact variance_le_optimal_mul_energy ⟨C, hC⟩ hpos hf

theorem poincareConstants_iff_optimal_le
    (hne : (poincareConstants μ).Nonempty) (hpos : 0 < poincareConstant μ)
    {C : ℝ≥0} : C ∈ poincareConstants μ ↔ poincareConstant μ ≤ (C : ℝ≥0∞) := by
  constructor
  · exact poincareConstant_le_of_mem
  · intro hC f hf
    exact (variance_le_optimal_mul_energy hne hpos hf).trans (mul_le_mul_left hC _)

theorem exists_test_of_lt_poincareConstant {C : ℝ≥0}
    (hC : (C : ℝ≥0∞) < poincareConstant μ) :
    ∃ f : Space n → ℝ, LocallyLipschitzTests μ f ∧
      (C : ℝ≥0∞) * energy μ f < variance μ f := by
  have hnot : C ∉ poincareConstants μ := fun h =>
    (not_le_of_gt hC) (poincareConstant_le_of_mem h)
  simpa only [poincareConstants, mem_ofPred_eq, not_forall, not_imp, not_le,
    exists_prop] using hnot

theorem poincareConstant_le_universal (hn : 1 ≤ n) (hμ : admissibleMeasure μ) :
    poincareConstant μ ≤ universalPoincareConstant := by
  exact le_iSup_of_le n (le_iSup_of_le hn (le_iSup_of_le μ (le_iSup_of_le hμ le_rfl)))

theorem universal_le_iff {C : ℝ≥0∞} :
    universalPoincareConstant ≤ C ↔
      ∀ (n : ℕ), 1 ≤ n → ∀ μ : Measure (Space n),
        admissibleMeasure μ → poincareConstant μ ≤ C := by
  simp only [universalPoincareConstant, iSup_le_iff]

theorem universal_lt_top_of_uniform_bound {C : ℝ≥0}
    (hC : ∀ (n : ℕ), 1 ≤ n → ∀ μ : Measure (Space n),
      admissibleMeasure μ → C ∈ poincareConstants μ) :
    universalPoincareConstant < ⊤ := by
  have hbound : universalPoincareConstant ≤ (C : ℝ≥0∞) := by
    apply universal_le_iff.mpr
    intro n hn μ hμ
    exact poincareConstant_le_of_mem (hC n hn μ hμ)
  exact hbound.trans_lt ENNReal.coe_lt_top

/-- Every proposed finite constant below the universal supremum fails for
an actual test in some measure in the full class. This does not show the class
is inhabited or that its supremum is finite; those remain separate obligations. -/
theorem exists_counterexample_of_lt_universal {C : ℝ≥0}
    (hC : (C : ℝ≥0∞) < universalPoincareConstant) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (μ : Measure (Space n)), admissibleMeasure μ ∧
      ∃ f : Space n → ℝ, LocallyLipschitzTests μ f ∧
        (C : ℝ≥0∞) * energy μ f < variance μ f := by
  have hex : ∃ (n : ℕ) (_ : 1 ≤ n) (μ : Measure (Space n)) (_ : admissibleMeasure μ),
      (C : ℝ≥0∞) < poincareConstant μ := by
    simpa only [universalPoincareConstant, lt_iSup_iff] using hC
  obtain ⟨n, hn, μ, hμ, hlt⟩ := hex
  exact ⟨n, hn, μ, hμ, exists_test_of_lt_poincareConstant hlt⟩

end KLS
end

#print axioms KLS.variance_le_optimal_mul_energy
#print axioms KLS.optimal_toNNReal_mem
#print axioms KLS.exists_counterexample_of_lt_universal
