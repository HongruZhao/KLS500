import KLS.WeightedIntegrationByParts
import KLS.DefinitionBridges
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Hessian mean from an actual isotropic gradient pushforward

The source measure is `potentialMeasure φ`, with its actual density `exp (-φ)`.
The target is its actual pushforward by `gradient φ`. Weighted integration by
parts yields the Hessian integral identity from differentiability and stated
L¹ conditions. Under isotropy, the first and product gradient integrability
conditions follow from the target moments; Hessian-entry integrability remains
explicit.

No Hessian mean identity is assumed, and no moment-map existence, convexity,
Brascamp--Lieb inequality, or universal KLS bound is proved here.
-/

open MeasureTheory InnerProductSpace Set
open scoped Matrix.Norms.Elementwise

noncomputable section
namespace KLS.MomentMap

local instance matrixContinuousENorm (n : ℕ) : ContinuousENorm (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (ContinuousENorm (Fin n → Fin n → ℝ))

/-- The Euclidean coordinate vector used to differentiate a scalar coordinate. -/
def coordinateVector {n : ℕ} (j : Fin n) : Space n := PiLp.single 2 j (1 : ℝ)

/-- The actual image measure, rather than a separate measure with an assumed moment identity. -/
def gradientPushforward {n : ℕ} (φ : Space n → ℝ) : Measure (Space n) :=
  (potentialMeasure φ).map (gradient φ)

/-- The coordinate Hessian, with row `i` and differentiation direction `j`. -/
def hessianMatrix {n : ℕ} (φ : Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fun y => gradient φ y i) x (coordinateVector j)

/-- The library gradient is identified with coordinate directional derivatives. -/
theorem gradient_coordinate_eq_fderiv {n : ℕ} (φ : Space n → ℝ)
    (x : Space n) (j : Fin n) :
    gradient φ x j = fderiv ℝ φ x (coordinateVector j) := by
  rw [← inner_gradient_left]
  simp only [coordinateVector, EuclideanSpace.inner_single_right]
  simp

/-- Under differentiability of the gradient, the coordinate Hessian is the matrix of its derivative. -/
theorem hessianMatrix_apply_eq {n : ℕ} {φ : Space n → ℝ}
    (hgrad : Differentiable ℝ (gradient φ)) (x : Space n) (i j : Fin n) :
    hessianMatrix φ x i j = (fderiv ℝ (gradient φ) x (coordinateVector j)) i := by
  have hd := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x (hgrad x).hasFDerivAt
  simp only [EuclideanSpace.coe_proj, Function.comp_def] at hd
  rw [hessianMatrix, hd.fderiv]
  rfl

/-- The raw integration-by-parts identity. Its three nontrivial L¹ conditions are explicit;
the fourth condition from weighted integration by parts is the integrability of zero because `g=1`. -/
theorem integral_hessian_entry_eq_gradient_product {n : ℕ} {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hgrad : Differentiable ℝ (gradient φ))
    (i j : Fin n)
    (hfirst : Integrable (fun x => gradient φ x i) (potentialMeasure φ))
    (hhessian : Integrable (fun x => hessianMatrix φ x i j) (potentialMeasure φ))
    (hproduct : Integrable (fun x => gradient φ x i * gradient φ x j) (potentialMeasure φ)) :
    (∫ x, hessianMatrix φ x i j ∂potentialMeasure φ) =
      ∫ x, gradient φ x i * gradient φ x j ∂potentialMeasure φ := by
  have hi : Differentiable ℝ (fun x => gradient φ x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiable.comp hgrad
  have h1 : Integrable (fun x => gradient φ x i * (1 : ℝ)) (potentialMeasure φ) := by
    simpa only [mul_one] using hfirst
  have h2 : Integrable (fun x =>
      fderiv ℝ (fun y => gradient φ y i) x (coordinateVector j) * (1 : ℝ))
      (potentialMeasure φ) := by
    simpa only [hessianMatrix, mul_one] using hhessian
  have h3 : Integrable (fun x => gradient φ x i *
      fderiv ℝ (fun _ : Space n => (1 : ℝ)) x (coordinateVector j)) (potentialMeasure φ) := by
    simp
  have h4 : Integrable (fun x => gradient φ x i * (1 : ℝ) *
      fderiv ℝ φ x (coordinateVector j)) (potentialMeasure φ) := by
    simpa only [mul_one, ← gradient_coordinate_eq_fderiv φ] using hproduct
  have h := integral_mul_fderiv_potentialMeasure hφ hi (differentiable_const (1 : ℝ))
    (coordinateVector j) h1 h2 h3 h4
  simp only [fderiv_const_apply, zero_apply, mul_zero, integral_zero, mul_one] at h
  simp_rw [← gradient_coordinate_eq_fderiv φ] at h
  change (∫ x, fderiv ℝ (fun y => gradient φ y i) x (coordinateVector j)
    ∂potentialMeasure φ) = _
  linarith

/-- First gradient integrability follows from isotropy of the actual pushforward. -/
theorem integrable_gradient_coordinate {n : ℕ} {φ : Space n → ℝ}
    (hgrad : AEMeasurable (gradient φ) (potentialMeasure φ))
    (hiso : IsIsotropic (gradientPushforward φ)) (i : Fin n) :
    Integrable (fun x => gradient φ x i) (potentialMeasure φ) :=
  (hiso.integrable_coordinate i).comp_aemeasurable hgrad

/-- Product gradient integrability also follows from the pushforward's stated isotropic moments. -/
theorem integrable_gradient_coordinate_mul {n : ℕ} {φ : Space n → ℝ}
    (hgrad : AEMeasurable (gradient φ) (potentialMeasure φ))
    (hiso : IsIsotropic (gradientPushforward φ)) (i j : Fin n) :
    Integrable (fun x => gradient φ x i * gradient φ x j) (potentialMeasure φ) :=
  (hiso.2.2.1 i j).comp_aemeasurable hgrad

/-- Isotropic second moments are transferred through the actual gradient map. -/
theorem integral_gradient_coordinate_mul {n : ℕ} {φ : Space n → ℝ}
    (hgrad : AEMeasurable (gradient φ) (potentialMeasure φ))
    (hiso : IsIsotropic (gradientPushforward φ)) (i j : Fin n) :
    (∫ x, gradient φ x i * gradient φ x j ∂potentialMeasure φ) =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  calc
    _ = ∫ x : Space n, x i * x j ∂gradientPushforward φ :=
      (integral_map hgrad (by fun_prop)).symm
    _ = _ := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hiso.2.2.2

/-- Letwin's Hessian mean identity, entry by entry, with Hessian-entry L¹ explicit. -/
theorem integral_hessian_entry_eq_one {n : ℕ} {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hgrad : Differentiable ℝ (gradient φ))
    (hiso : IsIsotropic (gradientPushforward φ)) (i j : Fin n)
    (hhessian : Integrable (fun x => hessianMatrix φ x i j) (potentialMeasure φ)) :
    (∫ x, hessianMatrix φ x i j ∂potentialMeasure φ) =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  have hgm : AEMeasurable (gradient φ) (potentialMeasure φ) :=
    hgrad.continuous.measurable.aemeasurable
  rw [integral_hessian_entry_eq_gradient_product hφ hgrad i j
    (integrable_gradient_coordinate hgm hiso i) hhessian
    (integrable_gradient_coordinate_mul hgm hiso i j)]
  exact integral_gradient_coordinate_mul hgm hiso i j

/-- The Hessian matrix is Bochner integrable when all of its finitely many entries are integrable. -/
theorem integrable_hessianMatrix {n : ℕ} {φ : Space n → ℝ}
    (hhessian : ∀ i j, Integrable (fun x => hessianMatrix φ x i j) (potentialMeasure φ)) :
    Integrable (hessianMatrix φ) (potentialMeasure φ) :=
  Integrable.of_eval (fun i => Integrable.of_eval (hhessian i))

/-- The actual matrix integral is the identity, rather than a postulated Hessian normalization. -/
theorem integral_hessianMatrix_eq_one {n : ℕ} {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hgrad : Differentiable ℝ (gradient φ))
    (hiso : IsIsotropic (gradientPushforward φ))
    (hhessian : ∀ i j, Integrable (fun x => hessianMatrix φ x i j) (potentialMeasure φ)) :
    (∫ x, hessianMatrix φ x ∂potentialMeasure φ) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hi : ∀ i, Integrable (fun x => hessianMatrix φ x i) (potentialMeasure φ) :=
    fun i => Integrable.of_eval (hhessian i)
  change (∫ x, (fun i j => hessianMatrix φ x i j) ∂potentialMeasure φ) =
    (fun i j => (1 : Matrix (Fin n) (Fin n) ℝ) i j)
  ext i j
  rw [eval_integral hi i, eval_integral (hhessian i) j]
  exact integral_hessian_entry_eq_one hφ hgrad hiso i j (hhessian i j)

end KLS.MomentMap
end

#print axioms KLS.MomentMap.hessianMatrix_apply_eq
#print axioms KLS.MomentMap.integral_hessian_entry_eq_gradient_product
#print axioms KLS.MomentMap.integrable_gradient_coordinate_mul
#print axioms KLS.MomentMap.integrable_hessianMatrix
#print axioms KLS.MomentMap.integral_hessianMatrix_eq_one
