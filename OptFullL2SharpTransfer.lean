import OptCombinedSmoothTaylor
import KLS.WeightedSmoothL2Density

/-! A universal directional cumulant bound transfers to the actual Taylor
coefficients of every L2 observable without splitting the Taylor vector. -/
open MeasureTheory Matrix Filter
open scoped ContDiff BigOperators ENNReal Topology
noncomputable section
namespace KLS
set_option maxHeartbeats 1000000

lemma affineRemoval_add_inner_projection {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (f : Lp ℝ 2 μ)
    (g : Space n → ℝ) (x : Space n) :
    affineRemoval hμ f g x + inner ℝ x (affineProjectionVector hμ f) =
      g x - inner ℝ (isotropicAffineCoordinate hμ none) f := by
  simp only [affineRemoval, Fintype.sum_option, affineCoordinateFunction,
    Option.elim_none, Option.elim_some, mul_one, inner_eq_coordinate_sum]
  change g x - (inner ℝ (isotropicAffineCoordinate hμ none) f +
    ∑ j : Fin n, inner ℝ (isotropicAffineCoordinate hμ (some j)) f * x j) +
    (∑ j : Fin n, inner ℝ (isotropicAffineCoordinate hμ (some j)) f * x j) =
    g x - inner ℝ (isotropicAffineCoordinate hμ none) f
  ring

lemma Taylor_sum_le_of_universalCumulant_smoothCompact_sharp {n d : ℕ} {V g : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V))
    (hgc : ContDiff ℝ (⊤ : ℕ∞) g) (hgs : HasCompactSupport g)
    (hg : MemLp g 2 (potentialMeasure V)) {κ b : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 0 < d) (hb : 0 ≤ b) (hglobal : UniversalDirectionalCumulantBound d b) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V g d a ^ 2) ≤
      (b / (d.factorial : ℝ)^2) * ‖hg.toLp g‖^2 := by
  let f := hg.toLp g
  let R := finiteOrthonormalRemainder (isotropicAffineCoordinate hμ)
  let P := finiteOrthonormalProjection (isotropicAffineCoordinate hμ)
  let F := affineRemoval hμ f g
  let u := affineProjectionVector hμ f
  have hF := memLp_affineRemoval hμ f hg
  have hFe : hF.toLp F = R f := toLp_affineRemoval hμ f hg hg.coeFn_toLp
  have hm : (∫ x, F x ∂potentialMeasure V) = 0 := by
    simpa only [affineCoordinateFunction, Option.elim_none, one_mul] using
      affineRemoval_orthogonal hμ f hg.coeFn_toLp none
  have ho (j : Fin n) : (∫ x, x j * F x ∂potentialMeasure V) = 0 :=
    affineRemoval_orthogonal hμ f hg.coeFn_toLp (some j)
  have hs := Taylor_sum_le_of_universalCumulant_smoothAffine_combined hV hμ
    (smoothAffineFunction_affineRemoval hμ f hgc hgs) hF hm ho hκ hlower hd hb hglobal u
  rw [hFe] at hs
  have he : (fun x => F x + inner ℝ x u) =
      (fun x => g x - inner ℝ (isotropicAffineCoordinate hμ none) f) := by
    funext x
    exact affineRemoval_add_inner_projection hμ f g x
  rw [he] at hs
  simp_rw [exponentialTiltCoordinateTaylor_sub_const hV hκ hlower hg _ hd.ne'] at hs
  have hn := finiteOrthonormalProjection_remainder_norm_sq
    (orthonormal_isotropicAffineCoordinate hμ) f
  change ‖P f‖^2 + ‖R f‖^2 = ‖f‖^2 at hn
  have hu : ‖u‖^2 ≤ ‖P f‖^2 := affineProjectionVector_norm_sq_le hμ f
  have hsum : ‖R f‖^2 + ‖u‖^2 ≤ ‖f‖^2 := by linarith
  exact hs.trans (mul_le_mul_of_nonneg_left hsum (div_nonneg hb (sq_nonneg _)))

theorem Taylor_sum_le_of_universalCumulant_L2_sharp {n d : ℕ} {V : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) (f : Lp ℝ 2 (potentialMeasure V))
    {κ b : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 0 < d) (hb : 0 ≤ b) (hglobal : UniversalDirectionalCumulantBound d b) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
      (b / (d.factorial : ℝ)^2) * ‖f‖^2 := by
  obtain ⟨g, hgc, hg, ht⟩ := exists_smoothCompactL2_sequence hV.continuous f
  have hh (k : ℕ) :
      (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V ((hg k).toLp (g k)) d a ^ 2) ≤
        (b / (d.factorial : ℝ)^2) * ‖(hg k).toLp (g k)‖^2 := by
    simp_rw [exponentialTiltCoordinateTaylor_congr_ae (hg k).coeFn_toLp]
    exact Taylor_sum_le_of_universalCumulant_smoothCompact_sharp hV hμ
      (hgc k).1 (hgc k).2 (hg k) hκ hlower hd hb hglobal
  exact le_of_tendsto_of_tendsto
    ((continuous_exponentialTiltTaylor_square_sum_L2 hV hκ hlower d).continuousAt.tendsto.comp ht)
    (((continuous_norm.pow 2).const_mul (b / (d.factorial : ℝ)^2)).continuousAt.tendsto.comp ht)
    (Eventually.of_forall hh)

theorem Taylor_sum_le_of_universalCumulant_memLp_sharp {n d : ℕ} {V f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) (hf : MemLp f 2 (potentialMeasure V))
    {κ b : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 0 < d) (hb : 0 ≤ b) (hglobal : UniversalDirectionalCumulantBound d b) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
      (b / (d.factorial : ℝ)^2) * ∫ x, (f x)^2 ∂potentialMeasure V := by
  have hh := Taylor_sum_le_of_universalCumulant_L2_sharp hV hμ (hf.toLp f)
    hκ hlower hd hb hglobal
  simp_rw [exponentialTiltCoordinateTaylor_congr_ae hf.coeFn_toLp] at hh
  rwa [norm_toLp_sq_eq_integral_sq] at hh

theorem weightedCoordinateTaylorBound_of_universalCumulant_sharp {n : ℕ} {V : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) {κ R : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (b : ℕ → ℝ) (hb : ∀ d, 1 ≤ d → 0 ≤ b d)
    (hsize : ∀ d, 1 ≤ d → b d / (d.factorial : ℝ)^2 ≤ R^(2*d))
    (hglobal : ∀ d, 1 ≤ d → UniversalDirectionalCumulantBound d (b d)) :
    WeightedCoordinateTaylorBound V R := by
  intro d hd f
  exact (Taylor_sum_le_of_universalCumulant_L2_sharp hV hμ f hκ hlower hd (hb d hd)
    (hglobal d hd)).trans (mul_le_mul_of_nonneg_right (hsize d hd) (sq_nonneg _))

end KLS
end
