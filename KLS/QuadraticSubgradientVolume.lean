import KLS.SubgradientComparison
import KLS.MatrixActionMeasure
import Mathlib.Analysis.Matrix.PosDef

/-! Centered positive quadratic tests and their exact subgradient image volumes. -/

open MeasureTheory InnerProductSpace Matrix Set Filter
open scoped Topology ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

def centeredQuadratic (A : Matrix (Fin n) (Fin n) ℝ) (x₀ p : Space n)
    (c : ℝ) (x : Space n) : ℝ :=
  c + inner ℝ p (x - x₀) + (1 / 2 : ℝ) * inner ℝ (x - x₀) (matrixAction A (x - x₀))

lemma continuous_centeredQuadratic (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ p : Space n) (c : ℝ) : Continuous (centeredQuadratic A x₀ p c) := by
  unfold centeredQuadratic
  fun_prop

lemma differentiable_centeredQuadratic (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ p : Space n) (c : ℝ) : Differentiable ℝ (centeredQuadratic A x₀ p c) := by
  have hd : Differentiable ℝ (fun x : Space n => x - x₀) := differentiable_id.sub_const _
  exact ((differentiable_const c).add ((differentiable_const p).inner ℝ hd)).add
    ((differentiable_const (1 / 2 : ℝ)).mul (hd.inner ℝ ((matrixAction A).differentiable.comp hd)))

@[simp] lemma centeredQuadratic_center (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ p : Space n) (c : ℝ) : centeredQuadratic A x₀ p c x₀ = c := by
  simp [centeredQuadratic]

lemma inner_matrixAction_nonneg {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x : Space n) : 0 ≤ inner ℝ x (matrixAction A x) := by
  have h := hA.dotProduct_mulVec_nonneg (fun i => x i)
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    dotProduct, Matrix.mulVec, matrixAction_apply, star_trivial, mul_comm] using h

lemma inner_matrixAction_pos {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {x : Space n} (hx : x ≠ 0) :
    0 < inner ℝ x (matrixAction A x) := by
  have hx' : (fun i => x i) ≠ 0 := by
    intro h
    apply hx
    ext i
    exact congrFun h i
  have h := hA.dotProduct_mulVec_pos hx'
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    dotProduct, Matrix.mulVec, matrixAction_apply, star_trivial, mul_comm] using h

lemma centeredQuadratic_support_identity {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) (x₀ p : Space n) (c : ℝ) (x y : Space n) :
    centeredQuadratic A x₀ p c y - centeredQuadratic A x₀ p c x -
      inner ℝ (p + matrixAction A (x - x₀)) (y - x) =
      (1 / 2 : ℝ) * inner ℝ (y - x) (matrixAction A (y - x)) := by
  have hsym : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hA)
  rw [show y - x = (y - x₀) - (x - x₀) by abel]
  set X := x - x₀
  set Y := y - x₀
  change c + inner ℝ p Y + (1 / 2 : ℝ) * inner ℝ Y (matrixAction A Y) -
    (c + inner ℝ p X + (1 / 2 : ℝ) * inner ℝ X (matrixAction A X)) -
    inner ℝ (p + matrixAction A X) (Y - X) =
    (1 / 2 : ℝ) * inner ℝ (Y - X) (matrixAction A (Y - X))
  have hs : inner ℝ (matrixAction A X) Y = inner ℝ X (matrixAction A Y) := hsym _ _
  simp only [map_sub, inner_sub_left, inner_sub_right, inner_add_left]
  rw [← hs, real_inner_comm Y (matrixAction A X), real_inner_comm X (matrixAction A X)]
  ring

lemma centeredQuadratic_slope_mem_subgradient {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ p : Space n) (c : ℝ) (x : Space n) :
    p + matrixAction A (x - x₀) ∈ convexSubgradient (centeredQuadratic A x₀ p c) x := by
  intro y
  have h := centeredQuadratic_support_identity hA.isHermitian.isSymm x₀ p c x y
  have hn := inner_matrixAction_nonneg hA (y - x)
  linarith

lemma convexOn_of_global_subgradients {u : Space n → ℝ}
    (hs : ∀ x, (convexSubgradient u x).Nonempty) : ConvexOn ℝ univ u := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  obtain ⟨p, hp⟩ := hs (a • x + b • y)
  have hx := mul_le_mul_of_nonneg_left (hp x) ha
  have hy := mul_le_mul_of_nonneg_left (hp y) hb
  have hi : a * inner ℝ p (x - (a • x + b • y)) +
      b * inner ℝ p (y - (a • x + b • y)) = 0 := by
    simp only [inner_sub_right, inner_add_right, inner_smul_right]
    calc
      _ = (a * inner ℝ p x + b * inner ℝ p y) -
          (a + b) * (a * inner ℝ p x + b * inner ℝ p y) := by ring
      _ = 0 := by rw [hab]; ring
  have hval : a * u (a • x + b • y) + b * u (a • x + b • y) =
      u (a • x + b • y) := by rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul]
  nlinarith only [hx, hy, hi, hval]

lemma convex_centeredQuadratic {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ p : Space n) (c : ℝ) :
    ConvexOn ℝ univ (centeredQuadratic A x₀ p c) :=
  convexOn_of_global_subgradients (fun x => ⟨_, centeredQuadratic_slope_mem_subgradient hA x₀ p c x⟩)

lemma convexSubgradient_centeredQuadratic {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ p : Space n) (c : ℝ) (x : Space n) :
    convexSubgradient (centeredQuadratic A x₀ p c) x = {p + matrixAction A (x - x₀)} := by
  have hs := centeredQuadratic_slope_mem_subgradient hA x₀ p c x
  rw [convexSubgradient_eq_singleton_of_differentiableAt
    (convex_centeredQuadratic hA x₀ p c) ((differentiable_centeredQuadratic A x₀ p c) x),
    ← eq_gradient_of_mem_convexSubgradient ((differentiable_centeredQuadratic A x₀ p c) x) hs]

lemma volume_image_add_const (S : Set (Space n)) (p : Space n) :
    volume ((fun y => p + y) '' S) = volume S := by
  have heq : (fun y => p + y) '' S = (fun y => -p + y) ⁻¹' S := by
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨-p + y, hy, by simp⟩
  rw [heq, measure_preimage_add]

/-- This identity uses ordinary Euclidean volume and the matrix determinant;
there is no abstract Monge--Ampere operator or Jacobian premise. -/
theorem volume_convexSubgradientImage_centeredQuadratic
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (x₀ p : Space n) (c : ℝ) (S : Set (Space n)) :
    volume (convexSubgradientImage (centeredQuadratic A x₀ p c) S) =
      ENNReal.ofReal A.det * volume S := by
  have heq : convexSubgradientImage (centeredQuadratic A x₀ p c) S =
      (fun y => p + y) '' ((matrixAction A) '' ((fun x => -x₀ + x) '' S)) := by
    ext q
    simp only [convexSubgradientImage, mem_ofPred_eq, convexSubgradient_centeredQuadratic hA,
      mem_singleton_iff, mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, by simp [sub_eq_add_neg, add_comm]⟩
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp [sub_eq_add_neg, add_comm]⟩
  rw [heq, volume_image_add_const, Measure.addHaar_image_continuousLinearMap]
  change ENNReal.ofReal |(matrixAction A).det| * volume ((fun x => -x₀ + x) '' S) = _
  rw [det_matrixAction, abs_of_nonneg hA.det_nonneg, volume_image_add_const]

end KLS
end

#print axioms KLS.centeredQuadratic_support_identity
#print axioms KLS.volume_convexSubgradientImage_centeredQuadratic
