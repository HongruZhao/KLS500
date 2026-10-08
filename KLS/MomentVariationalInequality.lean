import KLS.MomentPerturbationNormalization

/-!
# Variational inequality for actual bounded conjugate perturbations

Every bounded conjugate perturbation is translated to an attained minimum
and normalized. Its actual energy and partition function are compared with
those of the constructed maximizer. This gives a two-sided-in-parameter
variational inequality, before differentiating it.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

theorem momentLegendrePerturbation_zero {n : ℕ} {φ : Space n → ℝ}
    (hcont : Continuous φ) (hconvex : ConvexOn ℝ Set.univ φ) (hzero : φ 0 = 0)
    (hnonneg : ∀ x, 0 ≤ φ x) (v : Space n → ℝ) (x : Space n) :
    momentLegendrePerturbation φ v 0 x = φ x := by
  simpa only [momentLegendrePerturbation, zero_mul, sub_zero] using
    normalizedLegendre_biconjugate_eq hcont hconvex hzero hnonneg x

theorem IsIsotropic.integrable_exp_neg_momentLegendrePerturbation
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hconvex : ConvexOn ℝ Set.univ φ) (hzero : φ 0 = 0) (hnonneg : ∀ x, 0 ≤ φ x)
    (hfinite : momentDualEnergy μ φ ≠ ∞) {v : Space n → ℝ} {B : ℝ}
    (hv : ∀ y, |v y| ≤ B) (t : ℝ) :
    Integrable (fun x : Space n => Real.exp (-momentLegendrePerturbation φ v t x)) := by
  obtain ⟨a, ha, hcone⟩ := hμ.exists_dualEnergy_linear_coercivity
  apply integrable_exp_neg_of_linear_coercivity
    (lipschitzWith_momentLegendrePerturbation hLip hzero hnonneg hv t).continuous.aestronglyMeasurable
    ha (A := (momentDualEnergy μ φ).toReal + |t| * B)
  intro x
  have hc := hcone φ hnonneg hfinite x
  have hd := (abs_le.mp (abs_momentLegendrePerturbation_sub_le
    hLip.continuous hconvex hzero hnonneg hv t x)).1
  linarith

/-- The actual maximizer satisfies the variational inequality for every real
parameter and every bounded integrable perturbation of its conjugate. The
normalization and admissibility of each competitor are proved internally. -/
theorem IsIsotropic.momentVariational_logPartition_inequality
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    {L : ℝ≥0} (φ : C(Space n, ℝ))
    (hφ : φ ∈ normalizedConvexLipschitzPotentials n L)
    (hnonneg : ∀ x, 0 ≤ φ x) (hfinite : momentDualEnergy μ φ ≠ ∞)
    (hmax : ∀ η : C(Space n, ℝ), η ∈ normalizedConvexLipschitzPotentials n L →
      (∀ x, 0 ≤ η x) → momentDualEnergy μ η ≠ ∞ →
      momentVariationalFunctional μ η ≤ momentVariationalFunctional μ φ)
    {v : Space n → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B) (hvi : Integrable v μ) (t : ℝ) :
    Real.log (momentPartitionFunction (momentLegendrePerturbation φ v t)) -
      Real.log (momentPartitionFunction φ) ≤ t * (∫ y, v y ∂μ) := by
  obtain ⟨x₀, hmin⟩ := hμ.exists_minimizer_momentLegendrePerturbation
    hφ.1 hφ.2.2 hφ.2.1 hnonneg hfinite hv t
  let ψ : Space n → ℝ := momentLegendrePerturbation φ v t
  have hψLip : LipschitzWith L ψ :=
    lipschitzWith_momentLegendrePerturbation hφ.1 hφ.2.1 hnonneg hv t
  let η : C(Space n, ℝ) := ⟨normalizeMomentPotentialAt ψ x₀,
    (lipschitzWith_normalizeMomentPotentialAt hψLip x₀).continuous⟩
  have hη : η ∈ normalizedConvexLipschitzPotentials n L :=
    ⟨lipschitzWith_normalizeMomentPotentialAt hψLip x₀,
      normalizeMomentPotentialAt_zero ψ x₀,
      convexOn_normalizeMomentPotentialAt (convexOn_momentLegendrePerturbation hnonneg hv t) x₀⟩
  have hηnonneg : ∀ x, 0 ≤ η x := normalizeMomentPotentialAt_nonneg hmin
  obtain ⟨hηfinite, hηenergy⟩ := hμ.momentDualEnergy_normalizedPerturbation_toReal_le
    hfinite hv hvi t x₀
  have hcomparison := hmax η hη hηnonneg hηfinite
  have hψpos : 0 < momentPartitionFunction ψ :=
    integral_exp_pos (hμ.integrable_exp_neg_momentLegendrePerturbation
      hφ.1 hφ.2.2 hφ.2.1 hnonneg hfinite hv t)
  have hlog : Real.log (momentPartitionFunction η) = ψ x₀ + Real.log (momentPartitionFunction ψ) := by
    change Real.log (momentPartitionFunction (normalizeMomentPotentialAt ψ x₀)) = _
    rw [momentPartitionFunction_normalizeAt, Real.log_mul (Real.exp_pos _).ne' hψpos.ne', Real.log_exp]
  change Real.log (momentPartitionFunction η) - (momentDualEnergy μ η).toReal ≤
    Real.log (momentPartitionFunction φ) - (momentDualEnergy μ φ).toReal at hcomparison
  rw [hlog] at hcomparison
  change (momentDualEnergy μ η).toReal ≤ (momentDualEnergy μ φ).toReal +
    t * (∫ y, v y ∂μ) + ψ x₀ at hηenergy
  change Real.log (momentPartitionFunction ψ) - Real.log (momentPartitionFunction φ) ≤ _
  linarith

/-- A bounded isotropic law produces an actual normalized finite-energy
potential satisfying the variational inequality for all bounded integrable
conjugate perturbations. Differentiating this inequality is the remaining
Euler--Lagrange step, not an assumption of the theorem. -/
theorem IsIsotropic.exists_momentVariational_potential_with_inequality
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (L : ℝ≥0) (hbound : ∀ᵐ y ∂μ, ‖y‖ ≤ L) :
    ∃ φ : C(Space n, ℝ),
      φ ∈ normalizedConvexLipschitzPotentials n L ∧ (∀ x, 0 ≤ φ x) ∧
      momentDualEnergy μ φ ≠ ∞ ∧
      ∀ (v : Space n → ℝ) (B : ℝ), (∀ y, |v y| ≤ B) → Integrable v μ → ∀ t : ℝ,
        Real.log (momentPartitionFunction (momentLegendrePerturbation φ v t)) -
          Real.log (momentPartitionFunction φ) ≤ t * (∫ y, v y ∂μ) := by
  obtain ⟨φ, hφ, hnonneg, hfinite, hmax⟩ := hμ.exists_momentVariational_maximizer_of_bounded L hbound
  refine ⟨φ, hφ, hnonneg, hfinite, fun v B hv hvi t => ?_⟩
  exact hμ.momentVariational_logPartition_inequality φ hφ hnonneg hfinite hmax hv hvi t

end KLS
end

#print axioms KLS.IsIsotropic.momentVariational_logPartition_inequality
#print axioms KLS.IsIsotropic.exists_momentVariational_potential_with_inequality
