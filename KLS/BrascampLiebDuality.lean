import KLS.ConvexHessian

/-!
# Inverse-Hessian dual estimate on the actual diffusion range

For a C² potential with positive-definite Hessian, matrix Young's inequality,
weighted integration by parts and integrated Bochner give the Brascamp--Lieb
dual estimate against actual diffusion images of compact smooth tests.
The inverse is mathlib's actual matrix inverse; compact support discharges
all integrability conditions. Density of this range in zero-mean L², needed
to identify the supremum with full variance, is not assumed or established.
-/

open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped BigOperators ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

/-- The actual inverse-Hessian quadratic form on the actual test gradient. -/
def inverseHessianGradientForm (φ f : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (coordinateHessian φ x)⁻¹ i j * coordinateDerivative f i x * coordinateDerivative f j x

lemma matrix_quadratic_sum_eq_dotProduct (M : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, M i j * a i * a j) = a ⬝ᵥ (M *ᵥ a) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Finite-dimensional Young inequality for a genuine positive-definite matrix and its inverse. -/
theorem matrix_inverse_young {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (a b : Fin n → ℝ) :
    2 * (a ⬝ᵥ b) ≤ a ⬝ᵥ (M⁻¹ *ᵥ a) + b ⬝ᵥ (M *ᵥ b) := by
  let _ := hM.isUnit.invertible
  have hMa : M *ᵥ (M⁻¹ *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hcross : (M⁻¹ *ᵥ a) ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ a := by
    rw [hM.isHermitian.isSymm.dotProduct_mulVec_comm, hMa]
  have h := hM.posSemidef.dotProduct_mulVec_nonneg (M⁻¹ *ᵥ a - b)
  simp only [star_trivial, Matrix.mulVec_sub, hMa, sub_dotProduct, dotProduct_sub] at h
  rw [hcross, dotProduct_comm (M⁻¹ *ᵥ a) a, dotProduct_comm b a] at h
  linarith

lemma inverseHessianGradientForm_nonneg {φ : Space n → ℝ}
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (f : Space n → ℝ) (x : Space n) :
    0 ≤ inverseHessianGradientForm φ f x := by
  rw [inverseHessianGradientForm, matrix_quadratic_sum_eq_dotProduct]
  simpa only [star_trivial] using (hpos x).inv.posSemidef.dotProduct_mulVec_nonneg
    (fun i => coordinateDerivative f i x)

/-- The actual Hessian and its actual inverse depend continuously on position. -/
lemma continuous_inverse_coordinateHessian {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef) :
    Continuous (fun x => (coordinateHessian φ x)⁻¹) := by
  have hh : Continuous (coordinateHessian φ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (continuousAt_matrix_inv (coordinateHessian φ x) ?_).comp hh.continuousAt
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (hpos x).det_pos.ne'

lemma continuous_inverseHessianGradientForm {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) :
    Continuous (inverseHessianGradientForm φ f) := by
  have hinv := continuous_inverse_coordinateHessian hφ hpos
  unfold inverseHessianGradientForm
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (((continuous_apply j).comp ((continuous_apply i).comp hinv)).mul
    (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous).mul
      (contDiff_coordinateDerivative hf (m := 0) (by norm_num) j).continuous

lemma hasCompactSupport_inverseHessianGradientForm {φ f : Space n → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (inverseHessianGradientForm φ f) := by
  have hij (i j : Fin n) : HasCompactSupport (fun x =>
      (coordinateHessian φ x)⁻¹ i j * coordinateDerivative f i x * coordinateDerivative f j x) :=
    (hasCompactSupport_coordinateDerivative hf i).mul_left.mul_right
  have hi (i : Fin n) : HasCompactSupport (fun x => ∑ j : Fin n,
      (coordinateHessian φ x)⁻¹ i j * coordinateDerivative f i x * coordinateDerivative f j x) := by
    convert! HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun j x => (coordinateHessian φ x)⁻¹ i j * coordinateDerivative f i x *
        coordinateDerivative f j x) (fun j _ => hij i j) using 1
    funext x
    simp only [Finset.sum_apply]
  convert! HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun i x => ∑ j : Fin n, (coordinateHessian φ x)⁻¹ i j *
        coordinateDerivative f i x * coordinateDerivative f j x) (fun i _ => hi i) using 1
  funext x
  simp only [inverseHessianGradientForm, Finset.sum_apply]

/-- No additional inverse-energy integrability assumption is needed for compact tests. -/
lemma integrable_inverseHessianGradientForm {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (hc : HasCompactSupport f) :
    Integrable (inverseHessianGradientForm φ f) (potentialMeasure φ) :=
  integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
    (continuous_inverseHessianGradientForm hφ hf hpos)
    (hasCompactSupport_inverseHessianGradientForm hc)

lemma inverse_hessian_gradient_young {φ : Space n → ℝ}
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (f g : Space n → ℝ) (x : Space n) :
    2 * inner ℝ (gradient f x) (gradient g x) ≤
      inverseHessianGradientForm φ f x + hessianGradientForm φ g x := by
  rw [inverseHessianGradientForm, hessianGradientForm,
    matrix_quadratic_sum_eq_dotProduct, matrix_quadratic_sum_eq_dotProduct,
    ← sum_coordinateDerivative_mul]
  exact matrix_inverse_young (hpos x) _ _

/-- Compact smooth diffusion images have zero weighted mean. -/
theorem integral_weightedDiffusion_eq_zero_of_hasCompactSupport {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) :
    (∫ x, weightedDiffusion φ g x ∂potentialMeasure φ) = 0 := by
  have h := integral_mul_weightedDiffusion_of_hasCompactSupport hφ
    (contDiff_const (c := (1 : ℝ))) hg hc
  simpa using h

/-- Compact smooth diffusion images are genuinely L² for the actual density measure. -/
theorem memLp_weightedDiffusion_of_hasCompactSupport {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    MemLp (weightedDiffusion φ g) 2 (potentialMeasure φ) := by
  apply (memLp_two_iff_integrable_sq (contDiff_weightedDiffusion hφ hg).continuous.aestronglyMeasurable).mpr
  exact (bochnerIntegrability_of_hasCompactSupport hφ hg hc).integrable_diffusion_sq

/-- The inverse-Hessian dual estimate on the concrete diffusion range.
Extending this to full variance requires a separate density theorem for that range. -/
theorem brascampLieb_dual_diffusion {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 3 g)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    2 * (∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ) -
      (∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ) ≤
      ∫ x, inverseHessianGradientForm φ f x ∂potentialMeasure φ := by
  have hid := diffusionIntegrability_of_hasCompactSupport (hφ.of_le (by norm_num)) hf
    (hg.of_le (by norm_num)) hgc
  have hbd := bochnerIntegrability_of_hasCompactSupport hφ hg hgc
  have hinv := integrable_inverseHessianGradientForm hφ hf hpos hfc
  have hy := integral_mono (hid.integrable_inner_gradient.const_mul 2)
    (hinv.add hbd.integrable_hessianGradientForm) (fun x => inverse_hessian_gradient_young hpos f g x)
  simp only [Pi.add_apply] at hy
  rw [integral_const_mul, integral_add hinv hbd.integrable_hessianGradientForm] at hy
  have hb := integral_hessianGradientForm_le_diffusion_sq hφ hg hgc
  have hi : (∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ) =
      ∫ x, inner ℝ (gradient f x) (gradient g x) ∂potentialMeasure φ := by
    calc
      _ = -(∫ x, f x * weightedDiffusion φ g x ∂potentialMeasure φ) := by
        rw [← integral_neg]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := by
        rw [integral_mul_weightedDiffusion_of_hasCompactSupport
          (hφ.of_le (by norm_num)) hf (hg.of_le (by norm_num)) hgc]
        ring
  rw [hi]
  linarith

end KLS
end

#print axioms KLS.matrix_inverse_young
#print axioms KLS.continuous_inverse_coordinateHessian
#print axioms KLS.integrable_inverseHessianGradientForm
#print axioms KLS.integral_weightedDiffusion_eq_zero_of_hasCompactSupport
#print axioms KLS.memLp_weightedDiffusion_of_hasCompactSupport
#print axioms KLS.brascampLieb_dual_diffusion
