import KLS.TensorEntryBounds

/-! The true Brownian diffusion derivative of the cumulant energy is uniformly
bounded along log-concave current laws of a compact original measure. -/
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def energyNoiseCoefficient (μ : Measure (Space n)) (r : ℕ) (u : Space n)
    (k : Fin n) (z : Fin (n+n*n) → ℝ) : ℝ :=
  fderiv ℝ (cumulantEnergy μ r u) z (coordinateDiffusion μ k z)

theorem energyNoiseCoefficient_eq_whitened (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (u : Space n) (k : Fin n)
    (z : Fin (n+n*n) → ℝ) :
    energyNoiseCoefficient μ r u k z =
      2*(whitenedCumulantTensor μ r u z ⬝ᵥ whitenedNextCumulantTensor μ r u k z) -
      whitenedCumulantTensor μ r u z ⬝ᵥ
        (tensorSlotSum (whitenedCovarianceNoiseMatrix μ k z) *ᵥ whitenedCumulantTensor μ r u z) := by
  let P := inverseSqrtCovariance μ (decodeState z)
  have hPs : P.transpose = P := (inverseSqrtCovariance_isSymm _).eq
  have hwhite : P*coordinateCovarianceMatrix μ z*P = 1 := by
    simpa only [P, coordinateCovarianceMatrix,
      (inverseSqrtCovariance_isSymm (μ := μ) (decodeState z)).eq] using
      inverseSqrtCovariance_whitens hμ hfull (decodeState z)
  have hh := fderiv_tensorMetric_whitened (contDiff_coordinateCovarianceMatrix hμ)
    (fun y => (coordinateCovarianceMatrix_posDef hμ hfull y).det_pos.ne')
    (contDiff_coordinateCumulantTensor (r := r) hμ u) z (coordinateDiffusion μ k z)
    P hPs (inverseSqrtCovariance_det_ne_zero hμ hfull _) hwhite
  rw [fderiv_coordinateCovarianceMatrix_diffusion hμ,
    fderiv_coordinateCumulantTensor_diffusion hμ] at hh
  exact hh

theorem abs_energyNoiseCoefficient_le_energies (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (u : Space n) (k : Fin n)
    (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) :
    |energyNoiseCoefficient μ r u k z| ≤
      ((1/2 : ℝ)+(r : ℝ)*normalizedThirdMomentBound n*(n : ℝ)^r)*cumulantEnergy μ r u z +
      2*cumulantEnergy μ (r+1) u z := by
  let T := whitenedCumulantTensor μ r u z
  let W := whitenedNextCumulantTensor μ r u k z
  let H := whitenedCovarianceNoiseMatrix μ k z
  have hb := abs_two_dotProduct_le T W
  have hq := abs_dotProduct_tensorSlotSum_le T H (normalizedThirdMomentBound n)
    (normalizedThirdMomentBound_pos n).le (fun i j => abs_whitenedCovarianceNoiseMatrix_le hμ hfull z hlc i j k)
  have hW : W ⬝ᵥ W ≤ cumulantEnergy μ (r+1) u z := by
    rw [← sum_whitenedNextCumulantTensor_square hμ hfull]
    exact Finset.single_le_sum (f := fun j : Fin n =>
      whitenedNextCumulantTensor μ r u j z ⬝ᵥ whitenedNextCumulantTensor μ r u j z)
      (fun j _ => dotProduct_self_nonnegative _) (Finset.mem_univ k)
  have hE : T ⬝ᵥ T = cumulantEnergy μ r u z := (cumulantEnergy_eq_whitened hμ hfull u z).symm
  rw [energyNoiseCoefficient_eq_whitened hμ hfull]
  have ha := abs_sub (2*(T ⬝ᵥ W)) (T ⬝ᵥ (tensorSlotSum H *ᵥ T))
  change |2*(T ⬝ᵥ W) - T ⬝ᵥ (tensorSlotSum H *ᵥ T)| ≤ _
  rw [hE] at hb hq
  nlinarith

def energyNoiseAprioriConstant (n r : ℕ) : ℝ :=
  ((1/2 : ℝ)+(r : ℝ)*normalizedThirdMomentBound n*(n : ℝ)^r)*energyAprioriConstant n r +
    2*energyAprioriConstant n (r+1)

theorem energyNoiseAprioriConstant_nonnegative (n r : ℕ) : 0 ≤ energyNoiseAprioriConstant n r := by
  have hB := (normalizedThirdMomentBound_pos n).le
  have hE := energyAprioriConstant_nonnegative n r
  have hE' := energyAprioriConstant_nonnegative n (r+1)
  unfold energyNoiseAprioriConstant
  positivity

theorem abs_energyNoiseCoefficient_le_covariance (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 1 ≤ r) (u : Space n) (k : Fin n)
    (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) :
    |energyNoiseCoefficient μ r u k z| ≤ energyNoiseAprioriConstant n r *
      inner ℝ u (matrixAction (coordinateCovarianceMatrix μ z) u) := by
  have hB := (normalizedThirdMomentBound_pos n).le
  have hE := cumulantEnergy_le_apriori_covariance hμ hfull hr u z hlc
  have hE' := cumulantEnergy_le_apriori_covariance hμ hfull (r := r+1) (by omega) u z hlc
  calc
    _ ≤ ((1/2 : ℝ)+(r : ℝ)*normalizedThirdMomentBound n*(n : ℝ)^r)*cumulantEnergy μ r u z +
        2*cumulantEnergy μ (r+1) u z := abs_energyNoiseCoefficient_le_energies hμ hfull u k z hlc
    _ ≤ ((1/2 : ℝ)+(r : ℝ)*normalizedThirdMomentBound n*(n : ℝ)^r)*
        (energyAprioriConstant n r * inner ℝ u (matrixAction (coordinateCovarianceMatrix μ z) u)) +
        2*(energyAprioriConstant n (r+1) * inner ℝ u (matrixAction (coordinateCovarianceMatrix μ z) u)) := by
      gcongr
    _ = _ := by unfold energyNoiseAprioriConstant; ring

def energyUniformNoiseBound (hμ : IsCompact μ.support) (r : ℕ) (u : Space n) : ℝ :=
  energyNoiseAprioriConstant n r * ‖directionalCovarianceCLM u‖ * (2*(supportNormBound hμ)^2)

theorem energyUniformNoiseBound_nonnegative (hμ : IsCompact μ.support) (r : ℕ) (u : Space n) :
    0 ≤ energyUniformNoiseBound hμ r u := by
  have h := energyNoiseAprioriConstant_nonnegative n r
  unfold energyUniformNoiseBound
  positivity

theorem abs_energyNoiseCoefficient_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 1 ≤ r) (u : Space n) (k : Fin n)
    (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) :
    |energyNoiseCoefficient μ r u k z| ≤ energyUniformNoiseBound hμ r u := by
  have hc : inner ℝ u (matrixAction (coordinateCovarianceMatrix μ z) u) ≤
      ‖directionalCovarianceCLM u‖*(2*(supportNormBound hμ)^2) := by
    rw [← directionalCovarianceCLM_apply]
    calc
      _ ≤ ‖directionalCovarianceCLM u (coordinateCovarianceMatrix μ z)‖ := le_abs_self _
      _ ≤ ‖directionalCovarianceCLM u‖*‖coordinateCovarianceMatrix μ z‖ :=
        (directionalCovarianceCLM u).le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (norm_covariance_le_of_support hμ (supportNormBound_pos hμ).le (norm_le_supportNormBound hμ) _)
        (norm_nonneg _)
  exact (abs_energyNoiseCoefficient_le_covariance hμ hfull hr u k z hlc).trans
    ((mul_le_mul_of_nonneg_left hc (energyNoiseAprioriConstant_nonnegative n r)).trans_eq (by
      unfold energyUniformNoiseBound
      ring))

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.abs_energyNoiseCoefficient_le
