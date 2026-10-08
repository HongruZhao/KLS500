import KLS.MomentLegendreDuality
import KLS.ConvexSubgradient

/-!
# Convexity and inverse support for the finite Legendre transform

These statements concern the actual finite domain of the extended conjugate.
They provide the geometric input for differentiability of the conjugate and
uniqueness of inverse subgradients almost everywhere.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

theorem normalizedLegendreTransform_combo_le {n : ℕ} (φ : Space n → ℝ)
    {p q : Space n} (hp : p ∈ momentLegendreDomain φ) (hq : q ∈ momentLegendreDomain φ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    normalizedLegendreTransform φ (a • p + b • q) ≤
      ENNReal.ofReal (a * (normalizedLegendreTransform φ p).toReal +
        b * (normalizedLegendreTransform φ q).toReal) := by
  apply (normalizedLegendreTransform_le_ofReal_iff φ _ (by positivity)).mpr
  intro x
  have hp' := mul_le_mul_of_nonneg_left (normalizedLegendreTransform_young φ hp x) ha
  have hq' := mul_le_mul_of_nonneg_left (normalizedLegendreTransform_young φ hq x) hb
  have hφ : a * φ x + b * φ x = φ x := by rw [← add_mul, hab, one_mul]
  simp only [inner_add_left, real_inner_smul_left]
  nlinarith only [hp', hq', hφ]

theorem convex_momentLegendreDomain {n : ℕ} (φ : Space n → ℝ) :
    Convex ℝ (momentLegendreDomain φ) := by
  intro p hp q hq a b ha hb hab
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (normalizedLegendreTransform_combo_le φ hp hq ha hb hab)

theorem convexOn_normalizedLegendreTransform_toReal {n : ℕ} (φ : Space n → ℝ) :
    ConvexOn ℝ (momentLegendreDomain φ) (fun p => (normalizedLegendreTransform φ p).toReal) := by
  refine ⟨convex_momentLegendreDomain φ, ?_⟩
  intro p hp q hq a b ha hb hab
  change (normalizedLegendreTransform φ (a • p + b • q)).toReal ≤
    a * (normalizedLegendreTransform φ p).toReal + b * (normalizedLegendreTransform φ q).toReal
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (normalizedLegendreTransform_combo_le φ hp hq ha hb hab)

/-- Every ordinary supporting slope is an actual finite contact point of the
extended conjugate. No differentiability or strict convexity is required. -/
theorem normalizedLegendreTransform_eq_of_mem_convexSubgradient
    {n : ℕ} {φ : Space n → ℝ} (hzero : φ 0 = 0) {x p : Space n}
    (hp : p ∈ convexSubgradient φ x) :
    normalizedLegendreTransform φ p = ENNReal.ofReal (inner ℝ p x - φ x) := by
  have hnonneg : 0 ≤ inner ℝ p x - φ x := by
    have h := hp 0
    simp only [zero_sub, inner_neg_right, hzero] at h
    linarith
  apply le_antisymm _ (ofReal_affine_le_normalizedLegendreTransform φ x p)
  apply (normalizedLegendreTransform_le_ofReal_iff φ p hnonneg).mpr
  intro z
  have h := hp z
  rw [inner_sub_right] at h
  linarith

theorem mem_momentLegendreDomain_of_mem_convexSubgradient
    {n : ℕ} {φ : Space n → ℝ} (hzero : φ 0 = 0) {x p : Space n}
    (hp : p ∈ convexSubgradient φ x) : p ∈ momentLegendreDomain φ := by
  change normalizedLegendreTransform φ p ≠ ∞
  rw [normalizedLegendreTransform_eq_of_mem_convexSubgradient hzero hp]
  exact ENNReal.ofReal_ne_top

theorem normalizedLegendreTransform_toReal_eq_of_mem_convexSubgradient
    {n : ℕ} {φ : Space n → ℝ} (hzero : φ 0 = 0) {x p : Space n}
    (hp : p ∈ convexSubgradient φ x) :
    (normalizedLegendreTransform φ p).toReal = inner ℝ p x - φ x := by
  rw [normalizedLegendreTransform_eq_of_mem_convexSubgradient hzero hp, ENNReal.toReal_ofReal]
  have h := hp 0
  simp only [zero_sub, inner_neg_right, hzero] at h
  linarith

/-- Fenchel contact reverses the support relation on the genuine finite
conjugate domain. This is the inverse graph identity needed for weak transport. -/
theorem finiteLegendre_support_of_mem_convexSubgradient
    {n : ℕ} {φ : Space n → ℝ} (hzero : φ 0 = 0) {x p : Space n}
    (hp : p ∈ convexSubgradient φ x) {q : Space n} (hq : q ∈ momentLegendreDomain φ) :
    (normalizedLegendreTransform φ p).toReal + inner ℝ x (q - p) ≤
      (normalizedLegendreTransform φ q).toReal := by
  rw [normalizedLegendreTransform_toReal_eq_of_mem_convexSubgradient hzero hp,
    inner_sub_right, real_inner_comm q x, real_inner_comm p x]
  have h := normalizedLegendreTransform_young φ hq x
  linarith

end KLS
end

#print axioms KLS.convex_momentLegendreDomain
#print axioms KLS.convexOn_normalizedLegendreTransform_toReal
#print axioms KLS.finiteLegendre_support_of_mem_convexSubgradient
