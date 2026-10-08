import KLS.WeakEllipticGreenAlgebra

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- A genuine compact C2 right test supplies integrability for the actual
 second-order expression with locally L2 coefficients. -/
theorem integrable_mul_weakEllipticExpression_compact_right
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Fin n → Space n → ℝ}
    (hA : ∀ i j, ∀ S : Set (Space n), IsCompact S → MemLp (fun x => A x i j) 2 (volume.restrict S))
    (hb : ∀ j, ∀ S : Set (Space n), IsCompact S → MemLp (b j) 2 (volume.restrict S))
    {f η : Space n → ℝ} (hf : Continuous f) (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η) :
    Integrable (fun x => f x*weakEllipticExpression A b η x) := by
  have hH (i j : Fin n) : Integrable (fun x => A x i j*(f x*coordinateHessian η x i j)) :=
    integrable_mul_continuous_compact_of_localL2
      (hf.mul (contDiff_coordinateHessian hη (m := 0) (by norm_num) i j).continuous)
      ((hasCompactSupport_coordinateDerivative (hasCompactSupport_coordinateDerivative hc j) i).mul_left)
      (hA i j)
  have hD (j : Fin n) : Integrable (fun x => b j x*(f x*coordinateDerivative η j x)) :=
    integrable_mul_continuous_compact_of_localL2
      (hf.mul (contDiff_coordinateDerivative hη (m := 1) (by norm_num) j).continuous)
      ((hasCompactSupport_coordinateDerivative hc j).mul_left) (hb j)
  have ht := (integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hH i j))).sub
      (integrable_finsetSum Finset.univ (fun j _ => hD j))
  change Integrable (fun x => (∑ i, ∑ j, A x i j*(f x*coordinateHessian η x i j)) -
    ∑ j, b j x*(f x*coordinateDerivative η j x)) at ht
  simpa only [weakEllipticExpression,Pi.sub_apply,mul_sub,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc] using ht

/-- Compact self-adjoint transfer follows directly from the genuine weak
 column divergence and symmetry. The left test has a Lipschitz gradient;
 no derivative of the coefficient matrix is used. -/
theorem integral_weakEllipticExpression_compact_transfer
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Fin n → Space n → ℝ}
    (hA : ∀ i j, ∀ S : Set (Space n), IsCompact S → MemLp (fun x => A x i j) 2 (volume.restrict S))
    (hb : ∀ j, ∀ S : Set (Space n), IsCompact S → MemLp (b j) 2 (volume.restrict S))
    (hsymm : ∀ᵐ x ∂(volume : Measure (Space n)), (A x).IsSymm)
    (hdiv : ∀ j, ∀ ψ : Space n → ℝ, LocallyLipschitz ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A x i j*coordinateDerivative ψ i x) = ∫ x, b j x*ψ x)
    {f η : Space n → ℝ} {G : ℝ≥0} (hf : ContDiff ℝ 1 f)
    (hG : LipschitzWith G (gradient f)) (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η) :
    Integrable (fun x => η x*weakEllipticExpression A b f x) ∧
    Integrable (fun x => f x*weakEllipticExpression A b η x) ∧
    (∫ x, η x*weakEllipticExpression A b f x) = ∫ x, f x*weakEllipticExpression A b η x := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hDη (j : Fin n) : ContDiff ℝ 1 (coordinateDerivative η j) :=
    contDiff_coordinateDerivative hη (by norm_num) j
  have hDf (j : Fin n) := lipschitz_coordinateDerivative_of_gradient_lipschitz hG j
  let ψ : Fin n → Space n → ℝ := fun j x =>
    η x*coordinateDerivative f j x-f x*coordinateDerivative η j x
  have hψ (j : Fin n) : LocallyLipschitz (ψ j) :=
    locallyLipschitz_sub_real
      (locallyLipschitz_mul_real hη1.locallyLipschitz (hDf j).locallyLipschitz)
      (locallyLipschitz_mul_real hf.locallyLipschitz (hDη j).locallyLipschitz)
  have hψc (j : Fin n) : HasCompactSupport (ψ j) :=
    hc.mul_right.sub (hasCompactSupport_coordinateDerivative hc j).mul_left
  have hψint (i j : Fin n) : Integrable (fun x => A x i j*coordinateDerivative (ψ j) i x) :=
    integrable_mul_coordinateDerivative_of_localL2 (hψ j) (hψc j) (hA i j) i
  have hbψ (j : Fin n) : Integrable (fun x => b j x*ψ j x) :=
    integrable_mul_continuous_compact_of_localL2 (hψ j).continuous (hψc j) (hb j)
  let W : Space n → ℝ := fun x =>
    (∑ j, ∑ i, A x i j*coordinateDerivative (ψ j) i x) - ∑ j, b j x*ψ j x
  have hW1 : Integrable (fun x => ∑ j, ∑ i, A x i j*coordinateDerivative (ψ j) i x) :=
    integrable_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun i _ => hψint i j))
  have hW2 : Integrable (fun x => ∑ j, b j x*ψ j x) :=
    integrable_finsetSum Finset.univ (fun j _ => hbψ j)
  have hW : Integrable W := hW1.sub hW2
  have hWzero : (∫ x, W x) = 0 := by
    change (∫ x, (∑ j, ∑ i, A x i j*coordinateDerivative (ψ j) i x) - ∑ j, b j x*ψ j x) = 0
    rw [integral_sub hW1 hW2,integral_finsetSum _ (fun j _ =>
      integrable_finsetSum Finset.univ (fun i _ => hψint i j)),integral_finsetSum _ (fun j _ => hbψ j)]
    simp_rw [integral_finsetSum _ (fun i _ => hψint i _),hdiv _ _ (hψ _) (hψc _)]
    exact sub_self _
  have hpoint : W =ᵐ[volume] (fun x =>
      η x*weakEllipticExpression A b f x-f x*weakEllipticExpression A b η x) := by
    have hdfAe : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ j, DifferentiableAt ℝ (coordinateDerivative f j) x :=
      ae_all_iff.mpr (fun j => (hDf j).ae_differentiableAt (μ := volume))
    filter_upwards [hsymm,hdfAe] with x hx hdf
    have hψder (j i : Fin n) : coordinateDerivative (ψ j) i x =
        (coordinateDerivative η i x*coordinateDerivative f j x+η x*coordinateHessian f x i j) -
          (coordinateDerivative f i x*coordinateDerivative η j x+f x*coordinateHessian η x i j) := by
      dsimp only [ψ]
      have hp : DifferentiableAt ℝ (fun y => η y*coordinateDerivative f j y) x :=
        ((hη1.differentiable (by norm_num)) x).mul (hdf j)
      have hq : DifferentiableAt ℝ (fun y => f y*coordinateDerivative η j y) x :=
        ((hf.differentiable (by norm_num)) x).mul (((hDη j).differentiable (by norm_num)) x)
      rw [coordinateDerivative_sub hp hq,
        coordinateDerivative_mul ((hη1.differentiable (by norm_num)) x) (hdf j),
        coordinateDerivative_mul ((hf.differentiable (by norm_num)) x)
          (((hDη j).differentiable (by norm_num)) x)]
      rfl
    dsimp only [W]
    simp_rw [hψder]
    exact weak_elliptic_green_algebra (A x) (coordinateHessian f x) (coordinateHessian η x) hx
      (fun j => b j x) (fun j => coordinateDerivative f j x) (fun j => coordinateDerivative η j x) (f x) (η x)
  have hR := integrable_mul_weakEllipticExpression_compact_right hA hb hf.continuous hη hc
  have heq : (fun x => W x+f x*weakEllipticExpression A b η x) =ᵐ[volume]
      (fun x => η x*weakEllipticExpression A b f x) := by
    filter_upwards [hpoint] with x hx
    linarith
  refine ⟨(hW.add hR).congr heq,hR,?_⟩
  rw [← integral_congr_ae heq,integral_add hW hR,hWzero,zero_add]

end KLS
end
