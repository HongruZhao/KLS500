import EntropyPolynomialProfileBounds
import ResolventEntropyIteration

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The explicit positive polynomial profile supplies actual iterate gradients
with the fixed1.01 lag tolerance and the normalized entropy clock. -/
theorem weightedMassResolvent_exists_polynomial_entropy_gradient
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t B M L : ℝ} (ht : 0 < t) (hB : 0 < B) (hM : 0 ≤ M)
    (hsmall : t*L ≤ B/2000) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    (hgL : ∀ x, |weightedDiffusion φ g x| ≤ L) (k : ℕ) :
    ∃ v : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      v =ᵐ[potentialMeasure φ] ((weightedMassResolvent φ ht)^[k+1] (hg2.toLp g) : Space n → ℝ) ∧
      (∀ x, ‖gradient v x‖ ≤ M) ∧
      (1 ≤ k → ∀ x, ‖gradient v x‖ ≤
        ((87/100 : ℝ)*B)/(Real.sqrt (t/(101/100 : ℝ))*entropyClock k)) := by
  have hsmall' : (3 : ℝ)*(t*L) ≤ (1/100 : ℝ)*(3*B/20) := by linarith
  obtain ⟨u,v,_hu2,_hv2,_hu,hv,_huμ,hvμ,_hev,huB,_hvB,_huM,hvM,hbound⟩ :=
    weightedMassResolvent_exists_iterated_entropy_pair hφ hconv
      (scaledEntropyProfile_contDiff B) ht (by positivity : 0 < 3*B/20)
      (by norm_num : (0 : ℝ) ≤ 3) hM (by norm_num : (0 : ℝ) ≤ 1/100)
      (fun r hr => (scaledEntropyProfile_bounds hB hr).1)
      (fun r hr => scaledEntropyProfile_abs_bound hB hr)
      (fun r hr => scaledEntropyProfile_deriv_bound hB hr)
      (fun r s hr hs => scaledEntropyProfile_tangent hB hr hs)
      (fun r hr => scaledEntropyProfile_curvature hB hr)
      (fun r s hr hs => scaledEntropyProfile_lipschitz hB hr hs)
      hsmall' hg hg2 hgB hgM hgL k
  refine ⟨v,hv,hvμ,hvM,?_⟩
  intro hk x
  have hp : 0 < Real.sqrt (t/(101/100 : ℝ))*entropyClock k :=
    mul_pos (Real.sqrt_pos.mpr (by positivity)) (entropyClock_pos hk)
  apply (le_div_iff₀ hp).mpr
  have hh := (hbound x).trans (scaledEntropyProfile_bounds hB (huB x)).2
  norm_num only [show (1+(1/100 : ℝ))=(101/100 : ℝ) by norm_num] at hh
  nlinarith only [hh]

end KLS.ConstantReduction
end
