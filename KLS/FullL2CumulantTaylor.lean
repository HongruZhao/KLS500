import KLS.OrthogonalTaylorLimit
import KLS.LinearCumulantTaylor

/-! Conditional full L2 transfer from the actual universal directional
cumulant estimate. The affine component and its orthogonal remainder are
handled separately, and their squared norms add exactly. -/

open MeasureTheory Matrix
open scoped ContDiff BigOperators ENNReal
noncomputable section
namespace KLS
set_option maxHeartbeats 1000000

lemma Taylor_sum_le_of_universalCumulant_L2 {n d : ℕ} {V : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) (f : Lp ℝ 2 (potentialMeasure V))
    {κ b : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 0 < d) (hb : 0 ≤ b) (hglobal : UniversalDirectionalCumulantBound d b) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
      (2 * b / (d.factorial : ℝ) ^ 2) * ‖f‖ ^ 2 := by
  let v := isotropicAffineCoordinate hμ
  let P := finiteOrthonormalProjection v
  let R := finiteOrthonormalRemainder v
  let B := b / (d.factorial : ℝ) ^ 2
  have hB : 0 ≤ B := div_nonneg hb (sq_nonneg _)
  have hR := Taylor_sum_le_of_universalCumulant_orthogonal hV hμ (R f)
    (inner_finiteOrthonormalRemainder (orthonormal_isotropicAffineCoordinate hμ) f)
    hκ hlower hd hb hglobal
  have hP : (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V (P f) d a ^ 2) ≤
      B * ‖P f‖ ^ 2 := by
    have he (a : Fin d → Fin n) : exponentialTiltCoordinateTaylor V (P f) d a =
        exponentialTiltCoordinateTaylor V (fun x => inner ℝ x (affineProjectionVector hμ f)) d a := by
      rw [exponentialTiltCoordinateTaylor_congr_ae (finiteOrthonormalProjection_affine_coe hμ f)]
      have heq : (fun x => inner ℝ (isotropicAffineCoordinate hμ none) f +
          inner ℝ x (affineProjectionVector hμ f)) =
          (fun x => inner ℝ x (affineProjectionVector hμ f) -
            (-inner ℝ (isotropicAffineCoordinate hμ none) f)) := by funext x; ring
      rw [heq]
      exact exponentialTiltCoordinateTaylor_sub_const hV hκ hlower
        (hμ.memLp_inner _) _ hd.ne' a
    simp_rw [he]
    exact (Taylor_sum_le_of_universalCumulant_linear hV hμ hκ hlower hglobal _).trans
      (mul_le_mul_of_nonneg_left (affineProjectionVector_norm_sq_le hμ f) hB)
  have he (a : Fin d → Fin n) : exponentialTiltCoordinateTaylor V f d a =
      exponentialTiltCoordinateTaylor V (R f) d a + exponentialTiltCoordinateTaylor V (P f) d a := by
    have hsub : R f = f - P f := rfl
    have ht := exponentialTiltCoordinateTaylor_sub hV hκ hlower (Lp.memLp f) (Lp.memLp (P f)) d a
    have ht' := (exponentialTiltCoordinateTaylor_congr_ae
      (φ := V) (Lp.coeFn_sub f (P f)) d a).trans ht
    rw [← hsub] at ht'
    linarith
  have hsum : (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
      2 * (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V (R f) d a ^ 2) +
      2 * (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V (P f) d a ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    rw [he]
    nlinarith [sq_nonneg (exponentialTiltCoordinateTaylor V (R f) d a -
      exponentialTiltCoordinateTaylor V (P f) d a)]
  have hn := finiteOrthonormalProjection_remainder_norm_sq
    (orthonormal_isotropicAffineCoordinate hμ) f
  change ‖P f‖ ^ 2 + ‖R f‖ ^ 2 = ‖f‖ ^ 2 at hn
  calc
    _ ≤ 2 * B * ‖R f‖ ^ 2 + 2 * B * ‖P f‖ ^ 2 := by nlinarith
    _ = (2 * b / (d.factorial : ℝ) ^ 2) * ‖f‖ ^ 2 := by rw [← hn]; dsimp [B]; ring

lemma Taylor_sum_le_of_universalCumulant_memLp {n d : ℕ} {V f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) (hf : MemLp f 2 (potentialMeasure V))
    {κ b : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 0 < d) (hb : 0 ≤ b) (hglobal : UniversalDirectionalCumulantBound d b) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
      (2 * b / (d.factorial : ℝ) ^ 2) * ∫ x, (f x) ^ 2 ∂potentialMeasure V := by
  have hh := Taylor_sum_le_of_universalCumulant_L2 hV hμ (hf.toLp f) hκ hlower hd hb hglobal
  simp_rw [exponentialTiltCoordinateTaylor_congr_ae hf.coeFn_toLp] at hh
  rwa [norm_toLp_sq_eq_integral_sq] at hh

theorem weightedCoordinateTaylorBound_of_universalCumulant {n : ℕ} {V : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) {κ R : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (b : ℕ → ℝ) (hb : ∀ d, 1 ≤ d → 0 ≤ b d)
    (hsize : ∀ d, 1 ≤ d → 2 * b d / (d.factorial : ℝ) ^ 2 ≤ R ^ (2 * d))
    (hglobal : ∀ d, 1 ≤ d → UniversalDirectionalCumulantBound d (b d)) :
    WeightedCoordinateTaylorBound V R := by
  intro d hd f
  exact (Taylor_sum_le_of_universalCumulant_L2 hV hμ f hκ hlower hd (hb d hd)
    (hglobal d hd)).trans (mul_le_mul_of_nonneg_right (hsize d hd) (sq_nonneg _))

end KLS
end
#print axioms KLS.Taylor_sum_le_of_universalCumulant_L2
#print axioms KLS.Taylor_sum_le_of_universalCumulant_memLp
#print axioms KLS.weightedCoordinateTaylorBound_of_universalCumulant
