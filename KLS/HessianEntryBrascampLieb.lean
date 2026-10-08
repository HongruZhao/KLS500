import KLS.HessianCongruenceEnergy
import KLS.BrascampLiebFiniteEnergy
import KLS.PositiveMatrixSquareRoot

/-!
# Summed entrywise Brascamp–Lieb for an actual Hessian congruence

The source Hessian mean comes from the actual isotropic gradient pushforward.
The entry variances and inverse-Hessian energies are computed explicitly.
Diffusion-range density and integrability of the actual trace energy remain
honest analytic premises; the latter is supplied by the trace evolution module.
-/

open Matrix InnerProductSpace MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

theorem integral_hessianCongruence_entry {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 4 φ)
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (R : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    (∫ x, hessianCongruence φ R x a b ∂potentialMeasure φ) = (R * R.transpose) a b := by
  change (∫ x, (R * coordinateHessian φ x * R.transpose) a b ∂potentialMeasure φ) = _
  rw [integral_matrix_congruence_entry
    (fun i j => (memLp_coordinateHessian_entry_of_bounded hφ hH i j).integrable (by norm_num))]
  have heq : Matrix.of (fun i j => ∫ x, coordinateHessian φ x i j ∂potentialMeasure φ) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    exact integral_coordinateHessian_entry_eq_one_of_isotropic hφ hH hiso i j
  rw [heq, Matrix.mul_one]

/-- The true scalar variances of every entry sum to the centered trace moment. -/
theorem sum_variance_hessianCongruence {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 4 φ)
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (R : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a, ∑ b, ProbabilityTheory.variance (fun x => hessianCongruence φ R x a b) (potentialMeasure φ)) =
      (∫ x, hessianTraceSquare φ (R.transpose * R) x ∂potentialMeasure φ) -
        ((R.transpose * R) * (R.transpose * R)).trace := by
  have hf2 (a b : Fin n) := memLp_hessianCongruence_entry hφ hH R a b
  have hvar (a b : Fin n) : ProbabilityTheory.variance (fun x => hessianCongruence φ R x a b) (potentialMeasure φ) =
      (∫ x, hessianCongruence φ R x a b ^ 2 ∂potentialMeasure φ) - (R * R.transpose) a b ^ 2 := by
    rw [variance_eq_sub (hf2 a b), integral_hessianCongruence_entry hφ hH hiso]
    rfl
  simp_rw [hvar, Finset.sum_sub_distrib]
  have hmean : (∑ a, ∑ b, (R * R.transpose) a b ^ 2) =
      ((R.transpose * R) * (R.transpose * R)).trace := by
    have h1 : (1 : Matrix (Fin n) (Fin n) ℝ).IsSymm := by
      exact Matrix.isSymm_one
    simpa only [Matrix.mul_one, matrixFrobeniusSq] using matrixFrobeniusSq_affine_congruence R 1 h1
  rw [hmean]
  congr 1
  calc
    (∑ a, ∑ b, ∫ x, hessianCongruence φ R x a b ^ 2 ∂potentialMeasure φ) =
        ∑ a, ∫ x, ∑ b, hessianCongruence φ R x a b ^ 2 ∂potentialMeasure φ := by
      apply Finset.sum_congr rfl
      intro a _
      exact (integral_finsetSum Finset.univ (fun b _ => (hf2 a b).integrable_sq)).symm
    _ = ∫ x, ∑ a, ∑ b, hessianCongruence φ R x a b ^ 2 ∂potentialMeasure φ :=
      (integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ
        (fun b _ => (hf2 a b).integrable_sq))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact matrixFrobeniusSq_affine_congruence R (coordinateHessian φ x)
        (coordinateHessian_symmetric (hφ.of_le (by norm_num)) x)

theorem sum_integral_energy_hessianCongruence {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (R : Matrix (Fin n) (Fin n) ℝ)
    (hA : Integrable (hessianTraceGradientTerm φ (R.transpose * R)) (potentialMeasure φ)) :
    (∑ a, ∑ b, ∫ x, inverseHessianGradientForm φ (fun y => hessianCongruence φ R y a b) x
      ∂potentialMeasure φ) = ∫ x, hessianTraceGradientTerm φ (R.transpose * R) x ∂potentialMeasure φ := by
  have he (a b : Fin n) := integrable_hessianCongruence_entry_energy hφ hpos R hA a b
  calc
    _ = ∑ a, ∫ x, ∑ b, inverseHessianGradientForm φ (fun y => hessianCongruence φ R y a b) x
        ∂potentialMeasure φ := by
      apply Finset.sum_congr rfl
      intro a _
      exact (integral_finsetSum Finset.univ (fun b _ => he a b)).symm
    _ = ∫ x, ∑ a, ∑ b, inverseHessianGradientForm φ (fun y => hessianCongruence φ R y a b) x
        ∂potentialMeasure φ := (integral_finsetSum Finset.univ
          (fun a _ => integrable_finsetSum Finset.univ (fun b _ => he a b))).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (sum_inverseHessianGradientForm_hessianCongruence hφ R)

/-- Summing genuine scalar Brascamp–Lieb bounds gives the required trace
variance estimate for B=RᵀR, with no matrix inequality premise. -/
theorem hessianTrace_variance_control_of_factor {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 4 φ)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (R : Matrix (Fin n) (Fin n) ℝ)
    (hA : Integrable (hessianTraceGradientTerm φ (R.transpose * R)) (potentialMeasure φ))
    (hdense : DiffusionRangeDense φ) :
    (∫ x, hessianTraceSquare φ (R.transpose * R) x ∂potentialMeasure φ) -
        ((R.transpose * R) * (R.transpose * R)).trace ≤
      ∫ x, hessianTraceGradientTerm φ (R.transpose * R) x ∂potentialMeasure φ := by
  rw [← sum_variance_hessianCongruence hφ hH hiso R,
    ← sum_integral_energy_hessianCongruence hφ hpos R hA]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  exact brascampLieb_variance_of_integrable_energy (hφ.of_le (by norm_num))
    ((contDiff_matrix_entry (contDiff_hessianCongruence hφ R) a b).of_le (by norm_num)) hpos
    (memLp_hessianCongruence_entry hφ hH R a b)
    (integrable_hessianCongruence_entry_energy hφ hpos R hA a b) hdense

/-- The actual spectral square root covers every PSD B. -/
theorem hessianTrace_variance_control {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 4 φ)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef)
    (hA : Integrable (hessianTraceGradientTerm φ B) (potentialMeasure φ))
    (hdense : DiffusionRangeDense φ) :
    (∫ x, hessianTraceSquare φ B x ∂potentialMeasure φ) - (B * B).trace ≤
      ∫ x, hessianTraceGradientTerm φ B x ∂potentialMeasure φ := by
  obtain ⟨R, _, hR⟩ := exists_symmetric_matrix_square_root hB
  have hAR : Integrable (hessianTraceGradientTerm φ (R.transpose * R)) (potentialMeasure φ) := by
    simpa only [hR] using hA
  simpa only [hR] using hessianTrace_variance_control_of_factor hφ hpos hH hiso R hAR hdense

end KLS
end

#print axioms KLS.sum_variance_hessianCongruence
#print axioms KLS.sum_integral_energy_hessianCongruence
#print axioms KLS.hessianTrace_variance_control
