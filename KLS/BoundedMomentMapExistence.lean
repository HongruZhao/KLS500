import KLS.MomentPartitionDerivative
import KLS.WeightedIntegrationByParts

/-!
# Actual bounded-target moment-map existence

The variationally constructed potential is normalized by its proved positive
finite partition function. The first-variation identities then identify its
actual gradient pushforward with the given isotropic target measure.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

def normalizedMomentPotential {n : ℕ} (φ : Space n → ℝ) (x : Space n) : ℝ :=
  φ x + Real.log (momentPartitionFunction φ)

theorem gradient_normalizedMomentPotential {n : ℕ} (φ : Space n → ℝ) :
    gradient (normalizedMomentPotential φ) = gradient φ := by
  funext x
  change gradient (fun y => φ y + Real.log (momentPartitionFunction φ)) x = gradient φ x
  simp only [gradient, fderiv_add_const]

theorem exp_neg_normalizedMomentPotential {n : ℕ} {φ : Space n → ℝ}
    (hpos : 0 < momentPartitionFunction φ) (x : Space n) :
    Real.exp (-normalizedMomentPotential φ x) = Real.exp (-φ x) / momentPartitionFunction φ := by
  rw [normalizedMomentPotential, neg_add, Real.exp_add, Real.exp_neg (Real.log (momentPartitionFunction φ)),
    Real.exp_log hpos, div_eq_mul_inv]

theorem isProbabilityMeasure_normalizedMomentPotential {n : ℕ} {φ : Space n → ℝ}
    (hZ : Integrable (fun x => Real.exp (-φ x)) volume) :
    IsProbabilityMeasure (potentialMeasure (normalizedMomentPotential φ)) := by
  have hpos : 0 < momentPartitionFunction φ := integral_exp_pos hZ
  have hnormalized : Integrable (fun x => Real.exp (-normalizedMomentPotential φ x)) volume := by
    simpa only [exp_neg_normalizedMomentPotential hpos] using hZ.div_const (momentPartitionFunction φ)
  have hint : (∫ x, Real.exp (-normalizedMomentPotential φ x)) = 1 := by
    simp_rw [exp_neg_normalizedMomentPotential hpos]
    rw [integral_div]
    exact div_self hpos.ne'
  constructor
  change (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-normalizedMomentPotential φ x)))) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hnormalized (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    hint, ENNReal.ofReal_one]

/-- Identifying a normalized gradient pushforward from all bounded continuous
test identities. Both probability normalization and equality of measures are
proved, not supplied as moment-map certificates. -/
theorem gradient_map_eq_of_moment_integral_identity {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {φ : Space n → ℝ} (hcont : Continuous φ)
    (hZ : Integrable (fun x => Real.exp (-φ x)) volume)
    (hidentity : ∀ (v : Space n → ℝ) (B : ℝ), (∀ y, |v y| ≤ B) → Continuous v →
      (∫ x, Real.exp (-φ x) * v (gradient φ x)) / momentPartitionFunction φ = ∫ y, v y ∂μ) :
    (potentialMeasure (normalizedMomentPotential φ)).map (gradient (normalizedMomentPotential φ)) = μ := by
  let := isProbabilityMeasure_normalizedMomentPotential hZ
  have hpos : 0 < momentPartitionFunction φ := integral_exp_pos hZ
  have hψmeas : Measurable (normalizedMomentPotential φ) := hcont.measurable.add_const _
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro v
  rw [integral_map (measurable_gradient _).aemeasurable v.continuous.aestronglyMeasurable,
    integral_potentialMeasure hψmeas]
  calc
    (∫ x, v (gradient (normalizedMomentPotential φ) x) * Real.exp (-normalizedMomentPotential φ x)) =
        (∫ x, Real.exp (-φ x) * v (gradient φ x)) / momentPartitionFunction φ := by
      simp_rw [gradient_normalizedMomentPotential, exp_neg_normalizedMomentPotential hpos,
        ← mul_div_assoc]
      rw [integral_div]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => mul_comm _ _
    _ = ∫ y, v y ∂μ := hidentity v ‖v‖
      (fun y => by simpa [Real.norm_eq_abs] using v.norm_coe_le_norm y) v.continuous

/-- Every bounded isotropic probability measure is the actual moment measure
of a finite convex Lipschitz potential with normalized exponential density.
This is the weak moment-map existence theorem; no smoothness or Hessian bound
is asserted by this result. -/
theorem IsIsotropic.exists_bounded_momentMap
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (L : ℝ≥0) (hbound : ∀ᵐ y ∂μ, ‖y‖ ≤ L) :
    ∃ ψ : C(Space n, ℝ), LipschitzWith L ψ ∧ ConvexOn ℝ Set.univ ψ ∧
      IsProbabilityMeasure (potentialMeasure ψ) ∧
      (potentialMeasure ψ).map (gradient ψ) = μ := by
  obtain ⟨φ, hφ, hnonneg, hfinite, hZ, hidentity⟩ :=
    hμ.exists_moment_potential_integral_identity L hbound
  let ψ : C(Space n, ℝ) := ⟨normalizedMomentPotential φ, φ.continuous.add_const _⟩
  refine ⟨ψ, ?_, ?_, isProbabilityMeasure_normalizedMomentPotential hZ,
    gradient_map_eq_of_moment_integral_identity φ.continuous hZ hidentity⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (φ x + Real.log (momentPartitionFunction φ)) (φ y + Real.log (momentPartitionFunction φ)) ≤ _
    simpa [Real.dist_eq] using hφ.1.dist_le_mul x y
  · exact hφ.2.2.add_const _

end KLS
end

#print axioms KLS.isProbabilityMeasure_normalizedMomentPotential
#print axioms KLS.gradient_map_eq_of_moment_integral_identity
#print axioms KLS.IsIsotropic.exists_bounded_momentMap
