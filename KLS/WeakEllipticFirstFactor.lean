import KLS.WeakEllipticCompactTransfer

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The pointwise product-rule algebra for a compact first test needs no
 derivative or symmetry of the elliptic coefficients. -/
theorem weak_elliptic_first_factor_algebra
    (A H : Matrix (Fin n) (Fin n) ℝ) (b df de : Fin n → ℝ) (e : ℝ) :
    (∑ j, ∑ i, A i j*(de i*df j+e*H i j)) - (∑ j, b j*(e*df j)) =
      e*((∑ i, ∑ j, A i j*H i j)-(∑ j, b j*df j)) +
        ∑ i, ∑ j, A i j*de i*df j := by
  have hH : (∑ j, ∑ i, A i j*(e*H i j)) = e*(∑ i, ∑ j, A i j*H i j) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hb : (∑ j, b j*(e*df j)) = e*(∑ j, b j*df j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hJ : (∑ j, ∑ i, A i j*(de i*df j)) = ∑ i, ∑ j, A i j*de i*df j := by
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [hH,hb,hJ]
  ring

/-- Genuine weak column divergence gives the compact first-factor
 integration identity with only C1 regularity of that first factor and
 a Lipschitz gradient of the second. Both integral products are derived. -/
theorem integral_weakEllipticExpression_compact_first_factor
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Fin n → Space n → ℝ}
    (hA : ∀ i j, ∀ S : Set (Space n), IsCompact S → MemLp (fun x => A x i j) 2 (volume.restrict S))
    (hb : ∀ j, ∀ S : Set (Space n), IsCompact S → MemLp (b j) 2 (volume.restrict S))
    (hdiv : ∀ j, ∀ ψ : Space n → ℝ, LocallyLipschitz ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A x i j*coordinateDerivative ψ i x) = ∫ x, b j x*ψ x)
    {f η : Space n → ℝ} {G : ℝ≥0}
    (hG : LipschitzWith G (gradient f)) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    Integrable (fun x => η x*weakEllipticExpression A b f x) ∧
    Integrable (fun x => ∑ i, ∑ j, A x i j*coordinateDerivative η i x*coordinateDerivative f j x) ∧
    (∫ x, η x*weakEllipticExpression A b f x) =
      -(∫ x, ∑ i, ∑ j, A x i j*coordinateDerivative η i x*coordinateDerivative f j x) := by
  have hDf (j : Fin n) := lipschitz_coordinateDerivative_of_gradient_lipschitz hG j
  let ψ : Fin n → Space n → ℝ := fun j x => η x*coordinateDerivative f j x
  have hψ (j : Fin n) : LocallyLipschitz (ψ j) :=
    locallyLipschitz_mul_real hη.locallyLipschitz (hDf j).locallyLipschitz
  have hψc (j : Fin n) : HasCompactSupport (ψ j) := hc.mul_right
  have hψint (i j : Fin n) : Integrable (fun x => A x i j*coordinateDerivative (ψ j) i x) :=
    integrable_mul_coordinateDerivative_of_localL2 (hψ j) (hψc j) (hA i j) i
  have hbψ (j : Fin n) : Integrable (fun x => b j x*ψ j x) :=
    integrable_mul_continuous_compact_of_localL2 (hψ j).continuous (hψc j) (hb j)
  let W : Space n → ℝ := fun x =>
    (∑ j, ∑ i, A x i j*coordinateDerivative (ψ j) i x) - ∑ j, b j x*ψ j x
  let J : Space n → ℝ := fun x =>
    ∑ i, ∑ j, A x i j*coordinateDerivative η i x*coordinateDerivative f j x
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
  have hJ : Integrable J := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    have ht := integrable_mul_continuous_compact_of_localL2
      (((contDiff_coordinateDerivative hη (m := 0) (by norm_num) i).continuous).mul (hDf j).continuous)
      ((hasCompactSupport_coordinateDerivative hc i).mul_right) (hA i j)
    change Integrable (fun x => A x i j*(coordinateDerivative η i x*coordinateDerivative f j x)) at ht
    simpa only [mul_assoc] using ht
  have hpoint : W =ᵐ[volume] (fun x => η x*weakEllipticExpression A b f x+J x) := by
    have hd : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ j, DifferentiableAt ℝ (coordinateDerivative f j) x :=
      ae_all_iff.mpr (fun j => (hDf j).ae_differentiableAt (μ := volume))
    filter_upwards [hd] with x hx
    have hψder (j i : Fin n) : coordinateDerivative (ψ j) i x =
        coordinateDerivative η i x*coordinateDerivative f j x+η x*coordinateHessian f x i j := by
      exact coordinateDerivative_mul (hη.differentiable (by norm_num) x) (hx j) i
    dsimp only [W,J,weakEllipticExpression]
    simp_rw [hψder]
    dsimp only [ψ]
    exact weak_elliptic_first_factor_algebra (A x) (coordinateHessian f x)
      (fun j => b j x) (fun j => coordinateDerivative f j x) (fun j => coordinateDerivative η j x) (η x)
  have heq : (fun x => W x-J x) =ᵐ[volume] (fun x => η x*weakEllipticExpression A b f x) := by
    filter_upwards [hpoint] with x hx
    linarith
  refine ⟨(hW.sub hJ).congr heq,hJ,?_⟩
  rw [← integral_congr_ae heq,integral_sub hW hJ,hWzero,zero_sub]

end KLS
end
