import KLS.WeakEllipticFirstFactor
import KLS.BoundedCompactH1Tests
import KLS.LocalLipschitzWeakDerivative

open MeasureTheory Set Filter Matrix Metric
open scoped ContDiff Topology NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Rademacher on a countable exhaustion gives actual differentiability
 almost everywhere for each locally Lipschitz scalar. -/
theorem ae_differentiableAt_of_locallyLipschitz
    {f : Space n → ℝ} (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂(volume : Measure (Space n)), DifferentiableAt ℝ f x := by
  have hball (k : ℕ) : ∀ᵐ x ∂(volume : Measure (Space n)),
      x ∈ closedBall (0 : Space n) (k : ℝ) →
        DifferentiableWithinAt ℝ f (closedBall (0 : Space n) (k : ℝ)) x := by
    obtain ⟨L,hL⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : Space n) (k : ℝ))
    exact hL.ae_differentiableWithinAt_of_mem
  filter_upwards [ae_all_iff.mpr hball] with x hx
  obtain ⟨k,hk⟩ := exists_nat_gt ‖x‖
  have hxb : x ∈ ball (0 : Space n) (k : ℝ) := by simpa using hk
  exact (hx k (ball_subset_closedBall hxb)).differentiableAt
    (mem_of_superset (isOpen_ball.mem_nhds hxb) ball_subset_closedBall)

/-- Genuine weak column divergence gives the compact first-factor
 integration identity with only C1 regularity of that first factor and
 locally Lipschitz actual coordinate derivatives of the second. Both integral products are derived. -/
theorem integral_weakEllipticExpression_localC11_compact_first_factor
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Fin n → Space n → ℝ}
    (hA : ∀ i j, ∀ S : Set (Space n), IsCompact S → MemLp (fun x => A x i j) 2 (volume.restrict S))
    (hb : ∀ j, ∀ S : Set (Space n), IsCompact S → MemLp (b j) 2 (volume.restrict S))
    (hdiv : ∀ j, ∀ ψ : Space n → ℝ, LocallyLipschitz ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A x i j*coordinateDerivative ψ i x) = ∫ x, b j x*ψ x)
    {f η : Space n → ℝ}
    (hDf : ∀ j, LocallyLipschitz (coordinateDerivative f j)) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    Integrable (fun x => η x*weakEllipticExpression A b f x) ∧
    Integrable (fun x => ∑ i, ∑ j, A x i j*coordinateDerivative η i x*coordinateDerivative f j x) ∧
    (∫ x, η x*weakEllipticExpression A b f x) =
      -(∫ x, ∑ i, ∑ j, A x i j*coordinateDerivative η i x*coordinateDerivative f j x) := by
  let ψ : Fin n → Space n → ℝ := fun j x => η x*coordinateDerivative f j x
  have hψ (j : Fin n) : LocallyLipschitz (ψ j) :=
    locallyLipschitz_mul_real hη.locallyLipschitz (hDf j)
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
      ae_all_iff.mpr (fun j => ae_differentiableAt_of_locallyLipschitz (hDf j))
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
