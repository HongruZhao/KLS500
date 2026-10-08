import KLS.SuspensionTaylorNormalization
import KLS.WeightedSmoothL2Density

/-! The actual Taylor bound extends from smooth affine remainders to the
entire closed affine-orthogonal L2 subspace by the independently proved
continuity of its actual Taylor coefficients. -/

open MeasureTheory Matrix Filter
open scoped ContDiff BigOperators ENNReal Topology
noncomputable section
namespace KLS
set_option maxHeartbeats 1000000

lemma Taylor_sum_le_of_universalCumulant_orthogonal {n d : ℕ} {V : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) (f : Lp ℝ 2 (potentialMeasure V))
    (horth : ∀ a : Option (Fin n), inner ℝ (isotropicAffineCoordinate hμ a) f = 0)
    {κ b : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 0 < d) (hb : 0 ≤ b) (hglobal : UniversalDirectionalCumulantBound d b) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
      (b / (d.factorial : ℝ) ^ 2) * ‖f‖ ^ 2 := by
  obtain ⟨g, hgc, hg, ht⟩ := exists_smoothCompactL2_sequence hV.continuous f
  let u (k : ℕ) := (hg k).toLp (g k)
  let R := finiteOrthonormalRemainder (isotropicAffineCoordinate hμ)
  have hRf : R f = f := finiteOrthonormalRemainder_eq_self horth
  have hRt : Tendsto (fun k => R (u k)) atTop (𝓝 f) := by
    simpa only [hRf, Function.comp_def, u] using R.continuous.continuousAt.tendsto.comp ht
  have hh (k : ℕ) :
      (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V (R (u k)) d a ^ 2) ≤
        (b / (d.factorial : ℝ) ^ 2) * ‖R (u k)‖ ^ 2 := by
    let F := affineRemoval hμ (u k) (g k)
    have hF := memLp_affineRemoval hμ (u k) (hg k)
    have he := (hg k).coeFn_toLp
    have hFe : hF.toLp F = R (u k) := toLp_affineRemoval hμ (u k) (hg k) he
    have hm : (∫ x, F x ∂potentialMeasure V) = 0 := by
      simpa only [affineCoordinateFunction, Option.elim_none, one_mul] using
        affineRemoval_orthogonal hμ (u k) he none
    have ho (j : Fin n) : (∫ x, x j * F x ∂potentialMeasure V) = 0 :=
      affineRemoval_orthogonal hμ (u k) he (some j)
    have hs := Taylor_sum_le_of_universalCumulant_smoothAffine hV hμ
      (smoothAffineFunction_affineRemoval hμ (u k) (hgc k).1 (hgc k).2)
      hF hm ho hκ hlower hd hb hglobal
    rw [hFe] at hs
    convert hs using 1
    apply Finset.sum_congr rfl
    intro a _
    rw [exponentialTiltCoordinateTaylor_congr_ae (finiteOrthonormalRemainder_affine_coe hμ (u k) he)]
  exact le_of_tendsto_of_tendsto
    ((continuous_exponentialTiltTaylor_square_sum_L2 hV hκ hlower d).continuousAt.tendsto.comp hRt)
    (((continuous_norm.pow 2).const_mul (b / (d.factorial : ℝ) ^ 2)).continuousAt.tendsto.comp hRt)
    (Eventually.of_forall hh)

end KLS
end
#print axioms KLS.Taylor_sum_le_of_universalCumulant_orthogonal
