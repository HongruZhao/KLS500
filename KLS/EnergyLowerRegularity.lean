import KLS.DifferentialGeneratorContinuous

/-! The actual lower-cumulant tensor, its scalar energy and its cross term.
Their regularity follows from the proved cumulant generator identity. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def lowerCumulantEnergy (μ : Measure (Space n)) (r : ℕ) (u : Space n)
    (z : Fin (n+n*n) → ℝ) : ℝ :=
  whitenedLowerCumulantTensor μ r u z ⬝ᵥ whitenedLowerCumulantTensor μ r u z

def cumulantEnergyCross (μ : Measure (Space n)) (r : ℕ) (u : Space n)
    (z : Fin (n+n*n) → ℝ) : ℝ :=
  whitenedCumulantTensor μ r u z ⬝ᵥ whitenedLowerCumulantTensor μ r u z

theorem lowerCumulantEnergy_nonnegative (u : Space n) (z : Fin (n+n*n) → ℝ) :
    0 ≤ lowerCumulantEnergy μ r u z := dotProduct_self_nonnegative _

theorem continuous_lowerCumulantTensor (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r) (u : Space n) :
    Continuous (lowerCumulantTensor μ r u) := by
  have hG := continuous_differentialGenerator (contDiff_coordinateCumulantTensor (r := r) hμ u)
    (locallyLipschitz_coordinateDrift hμ hfull).continuous
    (fun k => (locallyLipschitz_coordinateDiffusion hμ hfull k).continuous)
  have he : lowerCumulantTensor μ r u = fun z =>
      -(differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
        (coordinateCumulantTensor μ r u) z) - ((r+1 : ℕ) : ℝ) • coordinateCumulantTensor μ r u z := by
    funext z
    rw [coordinateCumulantTensor_generator hμ hfull hr u z, neg_neg]
    abel
  rw [he]
  exact hG.neg.sub ((contDiff_coordinateCumulantTensor (r := r) hμ u).continuous.const_smul (((r+1 : ℕ) : ℝ)))

theorem continuous_whitened_tensor {T : (Fin (n+n*n) → ℝ) → (Fin r → Fin n) → ℝ}
    (hμ : IsCompact μ.support) (hfull : affineSpan ℝ μ.support = ⊤) (hT : Continuous T) :
    Continuous (fun z => tensorMatrix (inverseSqrtCovariance μ (decodeState z)) *ᵥ T z) := by
  have hP := (locallyLipschitz_inverseSqrtCovariance hμ hfull).continuous.comp
    contDiff_decodeState.continuous
  apply continuous_pi
  intro a
  unfold Matrix.mulVec dotProduct tensorMatrix tensorMatrixFamily
  apply continuous_finsetSum
  intro b _
  exact (continuous_finsetProd _ fun s _ =>
    (continuous_apply (b s)).comp ((continuous_apply (a s)).comp hP)).mul
      ((continuous_apply b).comp hT)

theorem continuous_cumulantEnergyCross (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r) (u : Space n) :
    Continuous (cumulantEnergyCross μ r u) := by
  apply continuous_finsetSum
  intro a _
  exact ((continuous_apply a).comp (continuous_whitened_tensor hμ hfull
    (contDiff_coordinateCumulantTensor hμ u).continuous)).mul
      ((continuous_apply a).comp (continuous_whitened_tensor hμ hfull
        (continuous_lowerCumulantTensor hμ hfull hr u)))

theorem continuous_lowerCumulantEnergy (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r) (u : Space n) :
    Continuous (lowerCumulantEnergy μ r u) := by
  apply continuous_finsetSum
  intro a _
  exact ((continuous_apply a).comp (continuous_whitened_tensor hμ hfull
    (continuous_lowerCumulantTensor hμ hfull hr u))).mul
      ((continuous_apply a).comp (continuous_whitened_tensor hμ hfull
        (continuous_lowerCumulantTensor hμ hfull hr u)))

theorem continuous_cumulantEnergyDrift (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r) (u : Space n) :
    Continuous (cumulantEnergyDrift μ r u) := by
  have he : cumulantEnergyDrift μ r u = fun z =>
      differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
        (cumulantEnergy μ r u) z := by
    funext z
    exact (cumulantEnergy_generator_exact hμ hfull hr u z).symm
  rw [he]
  exact continuous_differentialGenerator (contDiff_cumulantEnergy hμ hfull u)
    (locallyLipschitz_coordinateDrift hμ hfull).continuous
    (fun k => (locallyLipschitz_coordinateDiffusion hμ hfull k).continuous)

end KLS.AdaptiveLocalization
end
