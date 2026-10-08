import KLS.WeakDerivativeMollification

/-!
# Zero distributional gradient implies almost-everywhere constancy

The actual mollifiers turn the zero weak derivative identities into zero
classical derivatives. Each smooth approximation is constant by the mean
value theorem, and its almost-everywhere limit is consequently constant.
-/

open MeasureTheory InnerProductSpace Set Filter ContinuousLinearMap
open scoped ContDiff ENNReal Convolution Topology

noncomputable section
namespace KLS
variable {n : ℕ}

theorem coordinateDerivative_mollify_eq_zero_of_distribution {f : Space n → ℝ}
    (hf : LocallyIntegrable f volume)
    (hd : ∀ i (ψ : Space n → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, f x * coordinateDerivative ψ i x) = 0) (k : ℕ) (i : Fin n) (a : Space n) :
    coordinateDerivative (mollify k f) i a = 0 := by
  have hκ : ContDiff ℝ 1 (mollifierKernel n k) := (mollifierKernel_contDiff k).of_le (by simp)
  have hc := mollifierKernel_hasCompactSupport (n := n) k
  have ht := hd i (fun y => mollifierKernel n k (a - y))
    (hκ.comp (contDiff_const.sub contDiff_id)) (hc.comp_homeomorph (Homeomorph.subLeft a))
  have he : (∫ y, f y * coordinateDerivative (fun z => mollifierKernel n k (a - z)) i y) =
      -coordinateDerivative (mollify k f) i a := by
    rw [show coordinateDerivative (mollify k f) i a =
      scalarConvolution f (coordinateDerivative (mollifierKernel n k) i) a from
        coordinateDerivative_scalarConvolution hf hκ hc i a]
    unfold scalarConvolution
    rw [convolution_def, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [coordinateDerivative_const_sub (hκ.differentiable (by norm_num))]
      simp
  rw [he] at ht
  exact neg_eq_zero.mp ht

/-- No differentiable representative of f is assumed. -/
theorem ae_eq_const_of_zero_distributional_gradient {f : Space n → ℝ}
    (hf : LocallyIntegrable f volume)
    (hd : ∀ i (ψ : Space n → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, f x * coordinateDerivative ψ i x) = 0) :
    ∃ c : ℝ, f =ᵐ[volume] fun _ => c := by
  have hm (k : ℕ) (x y : Space n) : mollify k f x = mollify k f y := by
    have hder (z : Space n) : fderiv ℝ (mollify k f) z = 0 := by
      apply (toDual ℝ (Space n)).symm.injective
      change gradient (mollify k f) z = (toDual ℝ (Space n)).symm 0
      rw [map_zero]
      ext i
      rw [← coordinateDerivative_eq_gradient]
      exact coordinateDerivative_mollify_eq_zero_of_distribution hf hd k i z
    exact is_const_of_fderiv_eq_zero ((mollify_contDiff hf k).differentiable (by simp)) hder x y
  have hconv := mollify_tendsto_ae hf
  obtain ⟨x₀, hx₀⟩ := hconv.exists
  refine ⟨f x₀, hconv.mono ?_⟩
  intro x hx
  have heq : (fun k => mollify k f x) = fun k => mollify k f x₀ :=
    funext (fun k => hm k x x₀)
  rw [heq] at hx
  exact tendsto_nhds_unique hx hx₀

end KLS
end

#print axioms KLS.coordinateDerivative_mollify_eq_zero_of_distribution
#print axioms KLS.ae_eq_const_of_zero_distributional_gradient
