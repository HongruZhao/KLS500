import KLS.WeightedTiltMixedTaylor
import KLS.SmoothPermutationTaylor

/-! Exact fully symmetrized Taylor identity for actual normalized tilted
expectations. The first-slot form distinguishes the original gradient index;
permutation averaging removes that choice of slot. -/
open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The genuine factorial-normalized Taylor coefficient, evaluated on the
specified tuple of directions. -/
def exponentialTiltTaylorCoefficient (φ f : Space n → ℝ) (d : ℕ)
    (m : Fin d → Space n) : ℝ :=
  iteratedFDeriv ℝ d
    (fun z => ∫ x, f x ∂exponentialTilt (potentialMeasure φ) z) 0 m / d.factorial

/-- Full mixed BKL (50) with the original gradient index distinguished first.
Every permutation and every factorial is literal; all required tilt
smoothness is derived from the actual diffusion/gradient L2 assumptions. -/
theorem weightedDiffusion_exponentialTilt_symmetrized_taylor_head
    {φ f : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hf : ContDiff ℝ 2 f)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ))
    (d : ℕ) (m : Fin (d + 1) → Space n) :
    exponentialTiltTaylorCoefficient φ (-weightedDiffusion φ f) (d + 1) m =
      (∑ σ : Equiv.Perm (Fin (d + 1)), exponentialTiltTaylorCoefficient φ
        (fun x => inner ℝ (m (σ 0)) (gradient f x)) d
        (fun j => m (σ j.succ))) / (d + 1).factorial := by
  let g : Space n → Space n → ℝ := fun v z =>
    ∫ x, inner ℝ v (gradient f x) ∂exponentialTilt (potentialMeasure φ) z
  have hg (v : Space n) : ContDiff ℝ (⊤ : ℕ∞) (g v) :=
    contDiff_exponentialTilt_average_of_weighted_memLp hφ hκ hlower
      ((innerSL ℝ v).comp_memLp'
        (memLp_gradient_of_integrable_sq (hf.of_le (by norm_num)) hF))
  unfold exponentialTiltTaylorCoefficient
  simp only [Pi.neg_apply]
  rw [← Finset.sum_div, smooth_permutation_head_sum hg]
  rw [weightedDiffusion_exponentialTilt_mixed_derivative hφ hκ hlower hf hL hF]
  have hd : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  simp only [mul_div_cancel_left₀ _ hd]
  rfl

/-- The literal paper index order: the d Taylor directions precede the
original gradient direction, which occupies the last slot. -/
theorem weightedDiffusion_exponentialTilt_symmetrized_taylor
    {φ f : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hf : ContDiff ℝ 2 f)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ))
    (d : ℕ) (m : Fin (d + 1) → Space n) :
    exponentialTiltTaylorCoefficient φ (-weightedDiffusion φ f) (d + 1) m =
      (∑ σ : Equiv.Perm (Fin (d + 1)), exponentialTiltTaylorCoefficient φ
        (fun x => inner ℝ (m (σ (Fin.last d))) (gradient f x)) d
        (fun j => m (σ j.castSucc))) / (d + 1).factorial := by
  rw [weightedDiffusion_exponentialTilt_symmetrized_taylor_head hφ hκ hlower hf hL hF]
  exact congrArg (fun t : ℝ => t / (d + 1).factorial)
    (sum_permutation_head_eq_last (fun v w => exponentialTiltTaylorCoefficient φ
      (fun x => inner ℝ v (gradient f x)) d w) m)

end KLS
end
#print axioms KLS.exponentialTiltTaylorCoefficient
#print axioms KLS.weightedDiffusion_exponentialTilt_symmetrized_taylor_head
#print axioms KLS.weightedDiffusion_exponentialTilt_symmetrized_taylor
