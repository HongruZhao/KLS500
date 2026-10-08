import OptScalarStandardization
import OptScalarTiltVariance
import KLS.ConcaveExponentialTilt
import KLS.ClassToDensity
import KLS.TiltCumulantLowOrders

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem tiltVariance_inner_pos (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) {q : Space n → ℝ} (hq : Continuous q)
    {u : Space n} (hu : u ≠ 0) :
    0 < ProbabilityTheory.variance (fun x => inner ℝ u x) (μ.tilted q) := by
  have := tilted_isProbability_of_compact_support hμ hq
  have hs : (μ.tilted q).support = μ.support := tilted_support_eq hμ hq
  apply lt_of_le_of_ne' (variance_nonneg _ _)
  intro hz
  have hae := ae_eq_integral_of_variance_eq_zero
    (memLp_two_continuous_tilted hμ hq (show Continuous (fun x => inner ℝ u x) by fun_prop)) hz
  exact hu (eq_zero_of_affineSpan_support_eq_top_ae_inner_eq_const (by rwa [hs]) hae)

theorem admissible_cumulantTensor_three_diagonal_sq_le
    (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) (u : Space n) :
    (cumulantTensor μ 3 (fun _ => u))^2 ≤ 4 * ‖u‖^6 := by
  by_cases hu : u = 0
  · subst u
    rw [cumulantTensor_three_apply hμ]
    simp [tiltThirdCumulant, tiltAverage]
  let f : Space n →L[ℝ] ℝ := innerSL ℝ u
  have hf : Continuous (fun x => f x) := f.continuous
  have hpos (t : ℝ) : 0 < ProbabilityTheory.variance f (μ.tilted (fun x => 0 + t * f x)) :=
    tiltVariance_inner_pos hμ hadm.isotropic.affineSpan_support_eq_top (by fun_prop) hu
  have hQ (t : ℝ) :
      ProbabilityTheory.variance (fun x => (f x - tiltAverage μ (fun x => 0 + t * f x) f)^2)
        (μ.tilted (fun x => 0 + t * f x)) ≤
        8 * (ProbabilityTheory.variance f (μ.tilted (fun x => 0 + t * f x)))^2 := by
    have hcont : Continuous (fun x => 0 + t * f x) := by fun_prop
    have := tilted_isProbability_of_compact_support hμ hcont
    have hcompact : IsCompact (μ.tilted (fun x => 0 + t * f x)).support := by
      rwa [tilted_support_eq hμ hcont]
    have hconc : ConcaveOn ℝ univ (fun x => 0 + t * f x) := by
      refine ⟨convex_univ, ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [zero_add, map_add, map_smul, smul_eq_mul]
      ring_nf
      exact le_refl _
    exact centered_square_variance_le_eight hcompact
      (hadm.hasLogConcaveDensity.measureLogConcave_tilted hcont hconc) f (hpos t)
  have hh := tiltThirdCumulant_same_sq_le_of_centered_square_variance hμ
    (q := fun _ => 0) continuous_const hf hpos hQ 0
  have hvu : ProbabilityTheory.variance (fun x => inner ℝ u x) μ = ‖u‖^2 := by
    simpa only [real_inner_comm] using hadm.isotropic.real_variance_inner u
  rw [cumulantTensor_three_apply hμ]
  simpa only [zero_mul, add_zero, tilted_const, f,
    innerSL_apply_apply, hvu, ← pow_mul] using hh

theorem admissible_cumulantTensor_three_diagonal_abs_le
    (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) (u : Space n) :
    |cumulantTensor μ 3 (fun _ => u)| ≤ 2 * ‖u‖^3 := by
  have h := admissible_cumulantTensor_three_diagonal_sq_le hμ hadm u
  have hp : 0 ≤ 2 * ‖u‖^3 := by positivity
  nlinarith [sq_abs (cumulantTensor μ 3 (fun _ => u))]

end KLS.ConstantReduction
end
