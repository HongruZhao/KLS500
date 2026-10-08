import KLS.WeightedIntegrationByParts

/-!
# Concrete weighted diffusion and its energy identity

Coordinate derivatives are actual Fréchet derivatives in the Euclidean unit
coordinate directions. The diffusion is the coordinate Hessian trace minus
`⟨∇φ, ∇g⟩`, for the actual density measure `exp(-φ) dx`. The integration
identity is derived by summing the proved weighted integration by parts.
All regularity and boundary/integrability hypotheses are explicit.
-/

open MeasureTheory InnerProductSpace Filter
open scoped BigOperators

noncomputable section
namespace KLS

variable {n : ℕ}

/-- The actual derivative in the ith Euclidean unit direction. -/
def coordinateDerivative (f : Space n → ℝ) (i : Fin n) (x : Space n) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The actual iterated coordinate derivative, with outer index i and inner index j. -/
def coordinateHessian (f : Space n → ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => coordinateDerivative (coordinateDerivative f j) i x

/-- The trace of the coordinate Hessian. -/
def coordinateLaplacian (f : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, coordinateHessian f x i i

/-- The concrete weighted diffusion `Δg - ⟨∇φ, ∇g⟩`. -/
def weightedDiffusion (φ g : Space n → ℝ) (x : Space n) : ℝ :=
  coordinateLaplacian g x - inner ℝ (gradient φ x) (gradient g x)

/-- Four L¹ requirements for each coordinate's weighted integration by parts.
These are integrability hypotheses, not an assumed integration identity. -/
structure DiffusionIntegrability (φ f g : Space n → ℝ) : Prop where
  mul_deriv : ∀ i, Integrable (fun x => f x * coordinateDerivative g i x)
    (potentialMeasure φ)
  deriv_mul_deriv : ∀ i, Integrable
    (fun x => coordinateDerivative f i x * coordinateDerivative g i x) (potentialMeasure φ)
  mul_diagonal : ∀ i, Integrable (fun x => f x * coordinateHessian g x i i)
    (potentialMeasure φ)
  mul_deriv_drift : ∀ i, Integrable
    (fun x => f x * coordinateDerivative g i x * coordinateDerivative φ i x)
    (potentialMeasure φ)

lemma coordinateDerivative_eq_gradient (f : Space n → ℝ) (i : Fin n) (x : Space n) :
    coordinateDerivative f i x = gradient f x i := by
  rw [coordinateDerivative, ← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp

lemma sum_coordinateDerivative_mul (f g : Space n → ℝ) (x : Space n) :
    (∑ i, coordinateDerivative f i x * coordinateDerivative g i x) =
      inner ℝ (gradient f x) (gradient g x) := by
  simp only [coordinateDerivative_eq_gradient, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma weightedDiffusion_eq_sum (φ g : Space n → ℝ) (x : Space n) :
    weightedDiffusion φ g x = ∑ i,
      (coordinateHessian g x i i - coordinateDerivative g i x * coordinateDerivative φ i x) := by
  rw [weightedDiffusion, coordinateLaplacian, ← sum_coordinateDerivative_mul,
    Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma DiffusionIntegrability.integrable_inner_gradient {φ f g : Space n → ℝ}
    (h : DiffusionIntegrability φ f g) :
    Integrable (fun x => inner ℝ (gradient f x) (gradient g x)) (potentialMeasure φ) := by
  simp_rw [← sum_coordinateDerivative_mul]
  exact integrable_finsetSum Finset.univ (fun i _ => h.deriv_mul_deriv i)

lemma DiffusionIntegrability.integrable_mul_diffusion {φ f g : Space n → ℝ}
    (h : DiffusionIntegrability φ f g) :
    Integrable (fun x => f x * weightedDiffusion φ g x) (potentialMeasure φ) := by
  have hi : Integrable (fun x => ∑ i : Fin n,
      (f x * coordinateHessian g x i i -
        f x * coordinateDerivative g i x * coordinateDerivative φ i x)) (potentialMeasure φ) :=
    integrable_finsetSum Finset.univ (fun i _ => (h.mul_diagonal i).sub (h.mul_deriv_drift i))
  convert hi using 1
  funext x
  rw [weightedDiffusion_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Coordinate integration by parts for the weighted diffusion. -/
theorem integral_mul_coordinate_diffusion {φ f g : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hf : Differentiable ℝ f)
    (hg : ∀ i, Differentiable ℝ (coordinateDerivative g i))
    (h : DiffusionIntegrability φ f g) (i : Fin n) :
    (∫ x, f x * (coordinateHessian g x i i -
      coordinateDerivative g i x * coordinateDerivative φ i x) ∂potentialMeasure φ) =
      -(∫ x, coordinateDerivative f i x * coordinateDerivative g i x ∂potentialMeasure φ) := by
  have hibp := integral_mul_fderiv_potentialMeasure hφ hf (hg i)
    (EuclideanSpace.single i 1) (h.mul_deriv i) (h.deriv_mul_deriv i)
    (h.mul_diagonal i) (h.mul_deriv_drift i)
  change (∫ x, f x * coordinateHessian g x i i ∂potentialMeasure φ) =
    (∫ x, f x * coordinateDerivative g i x * coordinateDerivative φ i x ∂potentialMeasure φ) -
      ∫ x, coordinateDerivative f i x * coordinateDerivative g i x ∂potentialMeasure φ at hibp
  have heq : (fun x => f x * (coordinateHessian g x i i -
      coordinateDerivative g i x * coordinateDerivative φ i x)) =
      (fun x => f x * coordinateHessian g x i i -
        f x * coordinateDerivative g i x * coordinateDerivative φ i x) := by
    funext x
    ring
  rw [heq, integral_sub (h.mul_diagonal i) (h.mul_deriv_drift i), hibp]
  ring

/-- The actual diffusion satisfies the weighted gradient integration identity. -/
theorem integral_mul_weightedDiffusion {φ f g : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hf : Differentiable ℝ f)
    (hg : ∀ i, Differentiable ℝ (coordinateDerivative g i))
    (h : DiffusionIntegrability φ f g) :
    (∫ x, f x * weightedDiffusion φ g x ∂potentialMeasure φ) =
      -(∫ x, inner ℝ (gradient f x) (gradient g x) ∂potentialMeasure φ) := by
  have hi (i : Fin n) : Integrable (fun x => f x * (coordinateHessian g x i i -
      coordinateDerivative g i x * coordinateDerivative φ i x)) (potentialMeasure φ) := by
    convert (h.mul_diagonal i).sub (h.mul_deriv_drift i) using 1
    funext x
    dsimp
    ring
  simp_rw [weightedDiffusion_eq_sum, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp_rw [integral_mul_coordinate_diffusion hφ hf hg h]
  rw [Finset.sum_neg_distrib]
  rw [← integral_finsetSum Finset.univ (fun i _ => h.deriv_mul_deriv i)]
  simp_rw [sum_coordinateDerivative_mul]

/-- Symmetry holds on the explicitly specified common integration domain. -/
theorem integral_mul_weightedDiffusion_symmetric {φ f g : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hdf : ∀ i, Differentiable ℝ (coordinateDerivative f i))
    (hdg : ∀ i, Differentiable ℝ (coordinateDerivative g i))
    (hfg : DiffusionIntegrability φ f g) (hgf : DiffusionIntegrability φ g f) :
    (∫ x, f x * weightedDiffusion φ g x ∂potentialMeasure φ) =
      ∫ x, g x * weightedDiffusion φ f x ∂potentialMeasure φ := by
  rw [integral_mul_weightedDiffusion hφ hf hdg hfg,
    integral_mul_weightedDiffusion hφ hg hdf hgf]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => real_inner_comm _ _

/-- The diffusion quadratic form is the negative Dirichlet energy. -/
theorem integral_mul_weightedDiffusion_self {φ g : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hg : Differentiable ℝ g)
    (hdg : ∀ i, Differentiable ℝ (coordinateDerivative g i))
    (h : DiffusionIntegrability φ g g) :
    (∫ x, g x * weightedDiffusion φ g x ∂potentialMeasure φ) =
      -(∫ x, ‖gradient g x‖ ^ 2 ∂potentialMeasure φ) := by
  simpa only [real_inner_self_eq_norm_sq] using integral_mul_weightedDiffusion hφ hg hdg h

/-- In particular, the diffusion is nonpositive on its concrete integration domain. -/
theorem integral_mul_weightedDiffusion_self_nonpos {φ g : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hg : Differentiable ℝ g)
    (hdg : ∀ i, Differentiable ℝ (coordinateDerivative g i))
    (h : DiffusionIntegrability φ g g) :
    (∫ x, g x * weightedDiffusion φ g x ∂potentialMeasure φ) ≤ 0 := by
  rw [integral_mul_weightedDiffusion_self hφ hg hdg h]
  exact neg_nonpos.mpr (integral_nonneg fun x => sq_nonneg _)

end KLS
end

#print axioms KLS.coordinateDerivative_eq_gradient
#print axioms KLS.integral_mul_coordinate_diffusion
#print axioms KLS.integral_mul_weightedDiffusion
#print axioms KLS.integral_mul_weightedDiffusion_symmetric
#print axioms KLS.integral_mul_weightedDiffusion_self
#print axioms KLS.integral_mul_weightedDiffusion_self_nonpos
