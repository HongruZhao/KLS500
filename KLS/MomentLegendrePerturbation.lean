import KLS.MomentLegendreDuality

/-!
# Actual bounded perturbations on the Legendre side

Perturb the finite conjugate values by `t v`, then take their affine supremum.
The resulting potential is constructed explicitly. Its uniform distance to
the original potential, convexity, and Lipschitz bound are proved here.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

def momentLegendrePerturbation {n : ℕ} (φ v : Space n → ℝ) (t : ℝ) (x : Space n) : ℝ :=
  sSup (Set.range (fun y : momentLegendreDomain φ =>
    inner ℝ y.1 x - (normalizedLegendreTransform φ y.1).toReal - t * v y.1))

theorem momentLegendrePerturbation_range_nonempty {n : ℕ} {φ : Space n → ℝ}
    (hnonneg : ∀ x, 0 ≤ φ x) (v : Space n → ℝ) (t : ℝ) (x : Space n) :
    (Set.range (fun y : momentLegendreDomain φ =>
      inner ℝ y.1 x - (normalizedLegendreTransform φ y.1).toReal - t * v y.1)).Nonempty := by
  obtain ⟨y, hy⟩ := momentLegendreDomain_nonempty hnonneg
  exact ⟨_, Set.mem_range_self (⟨y, hy⟩ : momentLegendreDomain φ)⟩

theorem momentLegendrePerturbation_range_bddAbove {n : ℕ} (φ : Space n → ℝ)
    {v : Space n → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B) (t : ℝ) (x : Space n) :
    BddAbove (Set.range (fun y : momentLegendreDomain φ =>
      inner ℝ y.1 x - (normalizedLegendreTransform φ y.1).toReal - t * v y.1)) := by
  refine ⟨φ x + |t| * B, ?_⟩
  rintro a ⟨y, rfl⟩
  have hfenchel := normalizedLegendreTransform_young φ y.2 x
  have hb : |t * v y.1| ≤ |t| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hv y.1) (abs_nonneg _)
  have hneg := neg_le_abs (t * v y.1)
  linarith

theorem affine_le_momentLegendrePerturbation {n : ℕ} (φ : Space n → ℝ)
    {v : Space n → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B) (t : ℝ) (x : Space n)
    (y : momentLegendreDomain φ) :
    inner ℝ y.1 x - (normalizedLegendreTransform φ y.1).toReal - t * v y.1 ≤
      momentLegendrePerturbation φ v t x :=
  le_csSup (momentLegendrePerturbation_range_bddAbove φ hv t x) (Set.mem_range_self y)

theorem momentLegendrePerturbation_le {n : ℕ} {φ : Space n → ℝ}
    (hnonneg : ∀ x, 0 ≤ φ x) {v : Space n → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B)
    (t : ℝ) (x : Space n) :
    momentLegendrePerturbation φ v t x ≤ φ x + |t| * B := by
  apply csSup_le (momentLegendrePerturbation_range_nonempty hnonneg v t x)
  rintro a ⟨y, rfl⟩
  have hfenchel := normalizedLegendreTransform_young φ y.2 x
  have hb : |t * v y.1| ≤ |t| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hv y.1) (abs_nonneg _)
  have hneg := neg_le_abs (t * v y.1)
  linarith

/-- Uniform control of the actual conjugate perturbation on all source space. -/
theorem abs_momentLegendrePerturbation_sub_le {n : ℕ} {φ : Space n → ℝ}
    (hcont : Continuous φ) (hconvex : ConvexOn ℝ Set.univ φ) (hzero : φ 0 = 0)
    (hnonneg : ∀ x, 0 ≤ φ x) {v : Space n → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B)
    (t : ℝ) (x : Space n) :
    |momentLegendrePerturbation φ v t x - φ x| ≤ |t| * B := by
  have hu := momentLegendrePerturbation_le hnonneg hv t x
  have hl : φ x ≤ momentLegendrePerturbation φ v t x + |t| * B := by
    apply (normalizedLegendre_biconjugate_isLUB hcont hconvex hzero x).2
    rintro a ⟨y, rfl⟩
    have hy := affine_le_momentLegendrePerturbation φ hv t x y
    have hb : t * v y.1 ≤ |t| * B := by
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv y.1) (abs_nonneg _)
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem convexOn_momentLegendrePerturbation {n : ℕ} {φ : Space n → ℝ}
    (hnonneg : ∀ x, 0 ≤ φ x) {v : Space n → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B)
    (t : ℝ) : ConvexOn ℝ Set.univ (momentLegendrePerturbation φ v t) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  apply csSup_le (momentLegendrePerturbation_range_nonempty hnonneg v t (a • x + b • z))
  rintro c ⟨y, rfl⟩
  have hx := affine_le_momentLegendrePerturbation φ hv t x y
  have hz := affine_le_momentLegendrePerturbation φ hv t z y
  have hax := mul_le_mul_of_nonneg_left hx ha
  have hbz := mul_le_mul_of_nonneg_left hz hb
  have hconst : a * ((normalizedLegendreTransform φ y.1).toReal + t * v y.1) +
      b * ((normalizedLegendreTransform φ y.1).toReal + t * v y.1) =
      (normalizedLegendreTransform φ y.1).toReal + t * v y.1 := by
    rw [← add_mul, hab, one_mul]
  simp only [inner_add_right, inner_smul_right, smul_eq_mul]
  nlinarith only [hax, hbz, hconst]

theorem lipschitzWith_momentLegendrePerturbation {n : ℕ} {φ : Space n → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L φ) (hzero : φ 0 = 0) (hnonneg : ∀ x, 0 ≤ φ x)
    {v : Space n → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B) (t : ℝ) :
    LipschitzWith L (momentLegendrePerturbation φ v t) := by
  have hle (x z : Space n) :
      momentLegendrePerturbation φ v t x ≤ momentLegendrePerturbation φ v t z + L * ‖x - z‖ := by
    apply csSup_le (momentLegendrePerturbation_range_nonempty hnonneg v t x)
    rintro a ⟨y, rfl⟩
    have hz := affine_le_momentLegendrePerturbation φ hv t z y
    have hy := norm_le_of_mem_momentLegendreDomain hLip hzero y.2
    have hi : inner ℝ y.1 x - inner ℝ y.1 z ≤ L * ‖x - z‖ := by
      rw [← inner_sub_right]
      exact (real_inner_le_norm y.1 (x - z)).trans
        (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq, dist_eq_norm]
  have hxz := hle x z
  have hzx := hle z x
  rw [norm_sub_rev] at hzx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end KLS
end

#print axioms KLS.abs_momentLegendrePerturbation_sub_le
#print axioms KLS.convexOn_momentLegendrePerturbation
#print axioms KLS.lipschitzWith_momentLegendrePerturbation
