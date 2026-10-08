import KLS.ContactCapLocalization
import KLS.SubgradientAffineCovariance

/-!
# A retained contact segment and normalized caps

A second contact point supplies one fixed, nonzero amount of directional
width in every positive tilted section. Under any affine normalization into
a fixed ball, that width bounds the transformed normal from below. Therefore
the upper cap thickness still tends to zero after normalization.
-/

open MeasureTheory InnerProductSpace Set Metric
open scoped Topology ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

/-- A short part of a nontrivial contact segment belongs to every tilted
section, with a fixed positive separation in the exposing functional. -/
theorem exists_retained_contact_segment
    {u : Space n → ℝ} (hc : ConvexOn ℝ univ u)
    {x p z v w : Space n} {R c : ℝ} (hp : p ∈ convexSubgradient u x)
    (hz : z ∈ supportContactSet u x p) (hzu : u z ≤ R)
    (hw : w ∈ supportContactSet u x p) (hwu : u w ≤ R)
    (hwneg : inner ℝ v (w - z) < 0) (hcpos : 0 < c) :
    ∃ y : Space n, ∃ d : ℝ, 0 < d ∧ d < c ∧
      inner ℝ v (y - z) = -d ∧
      ∀ t : ℝ, 0 ≤ t → y ∈ contactTiltSection u x p z v R c t := by
  let D : ℝ := -inner ℝ v (w - z)
  have hD : 0 < D := neg_pos.mpr hwneg
  let s : ℝ := c / (2 * (c + D))
  have hs : 0 < s := div_pos hcpos (by positivity)
  have hden : 0 < 2 * (c + D) := by positivity
  have hseq : s * (2 * (c + D)) = c := div_mul_cancel₀ _ hden.ne'
  have hsone : s < 1 := (div_lt_one hden).mpr (by linarith)
  have hsd : s * D < c := by nlinarith [mul_pos hs hcpos]
  let y : Space n := (1 - s) • z + s • w
  have hycontact : y ∈ supportContactSet u x p :=
    convex_supportContactSet hc hp hz hw (by linarith) hs.le (by ring)
  have hyu : u y ≤ R := by
    have h := hc.2 (mem_univ z) (mem_univ w) (by linarith : 0 ≤ 1 - s)
      hs.le (by ring : 1 - s + s = 1)
    change u y ≤ (1 - s) * u z + s * u w at h
    have h₁ := mul_le_mul_of_nonneg_left hzu (by linarith : 0 ≤ 1 - s)
    have h₂ := mul_le_mul_of_nonneg_left hwu hs.le
    nlinarith
  have hyinner : inner ℝ v (y - z) = -(s * D) := by
    dsimp [y, D]
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
    ring
  refine ⟨y, s * D, mul_pos hs hD, hsd, hyinner, ?_⟩
  intro t ht
  refine ⟨hyu, ?_⟩
  rw [contactTilt, supportGap_eq_zero_iff.mpr hycontact, hyinner]
  have hm := mul_nonneg ht (show 0 ≤ -(s * D) + c by linarith)
  linarith

/-- The adjoint of the inverse affine linear part is the exact normal
transform for directional differences. -/
theorem inner_inverse_affine_adjoint
    (e : Space n ≃ᴬ[ℝ] Space n) (v y z : Space n) :
    inner ℝ (e.symm.linear.toLinearMap.adjoint v) (e y - e z) =
      inner ℝ v (y - z) := by
  rw [LinearMap.adjoint_inner_left]
  congr 1
  change e.symm.linear (e y - e z) = y - z
  simpa only [vsub_eq_sub, AffineEquiv.linear_toAffineMap, AffineEquiv.coe_toAffineMap, ContinuousAffineEquiv.coe_coe,
    LinearEquiv.coe_coe, e.symm_apply_apply] using
    e.symm.toAffineEquiv.toAffineMap.linear_apply_vsub (e y) (e z)

/-- Fixed retained width bounds the norm of the transformed normal away
from zero whenever the normalized set lies in a fixed ball. -/
theorem retained_width_le_transformed_normal
    (e : Space n ≃ᴬ[ℝ] Space n) {v y z : Space n} {d R : ℝ}
    (hsep : inner ℝ v (y - z) = -d)
    (hy : e y ∈ closedBall (0 : Space n) R)
    (hz : e z ∈ closedBall (0 : Space n) R) :
    d ≤ ‖e.symm.linear.toLinearMap.adjoint v‖ * (2 * R) := by
  have hyR : ‖e y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hzR : ‖e z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hdist : ‖e y - e z‖ ≤ 2 * R :=
    (norm_sub_le _ _).trans (by linarith)
  have hinner := inner_inverse_affine_adjoint e v y z
  have hcauchy := abs_real_inner_le_norm (e.symm.linear.toLinearMap.adjoint v) (e y - e z)
  rw [hinner, hsep, abs_neg] at hcauchy
  exact (le_abs_self d).trans (hcauchy.trans
    (mul_le_mul_of_nonneg_left hdist (norm_nonneg _)))

/-- An affine-normalized cap has a unit normal and a thickness bounded by
the original thickness times a fixed retained-width constant. -/
theorem exists_normalized_cap_from_retained_width
    (e : Space n ≃ᴬ[ℝ] Space n) {K : Set (Space n)}
    {v y z : Space n} {d R δ : ℝ}
    (hy : y ∈ K) (hz : z ∈ K) (hd : 0 < d) (hδ : 0 < δ)
    (hsep : inner ℝ v (y - z) = -d)
    (houter : e '' K ⊆ closedBall 0 R)
    (hcap : ∀ w ∈ K, inner ℝ v (w - z) ≤ δ) :
    ∃ v' : Space n, ‖v'‖ = 1 ∧
      ∀ w ∈ e '' K, inner ℝ v' (w - e z) ≤ (2 * R / d) * δ := by
  let a : Space n := e.symm.linear.toLinearMap.adjoint v
  have haR : d ≤ ‖a‖ * (2 * R) := retained_width_le_transformed_normal e hsep
    (houter ⟨y, hy, rfl⟩) (houter ⟨z, hz, rfl⟩)
  have ha : 0 < ‖a‖ := by
    by_contra hn
    have heq : ‖a‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    rw [heq, zero_mul] at haR
    exact (not_le_of_gt hd) haR
  refine ⟨‖a‖⁻¹ • a, ?_, ?_⟩
  · simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), inv_mul_cancel₀ ha.ne']
  · rintro w ⟨w, hw, rfl⟩
    rw [real_inner_smul_left]
    change ‖a‖⁻¹ * inner ℝ (e.symm.linear.toLinearMap.adjoint v) (e w - e z) ≤ _
    rw [inner_inverse_affine_adjoint]
    have hscaled := mul_le_mul_of_nonneg_left (hcap w hw) (inv_nonneg.mpr ha.le)
    have hrecip : ‖a‖⁻¹ ≤ 2 * R / d := by
      apply (le_div_iff₀ hd).mpr
      exact (inv_mul_le_iff₀ ha).mpr (by simpa only [mul_comm, mul_left_comm] using haR)
    exact hscaled.trans (mul_le_mul_of_nonneg_right hrecip hδ.le)

end KLS
end

#print axioms KLS.exists_retained_contact_segment
#print axioms KLS.inner_inverse_affine_adjoint
#print axioms KLS.retained_width_le_transformed_normal
#print axioms KLS.exists_normalized_cap_from_retained_width
