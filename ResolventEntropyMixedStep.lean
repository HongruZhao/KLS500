import ResolventEntropyChain
import EntropyMixedScalar
import ResolventGradientWeightedDomination

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.ConstantReduction
variable {n : ℕ}

/-- The scalar consequence of the actual entropy comparison and weighted
gradient domination, allowing a controlled change of the entropy profile. -/
theorem entropy_mixed_step_of_bounds {H G a b t e V P Q : ℝ}
    (hH : 0 < H) (hG : 0 ≤ G) (ha : 0 ≤ a) (ht : 0 < t)
    (he : 0 ≤ e) (hQ : 0 ≤ Q) (hb : a ≤ b)
    (heq : b^2-a*b=t/(1+e))
    (hsuper : V+t*Q ≤ H) (hlinear : a*G ≤ V)
    (hweighted : G^2 ≤ P*Q) (hprofile : P ≤ (1+e)*H) : b*G ≤ H := by
  have hepos : 0 < 1+e := by positivity
  have hprod : G^2 ≤ (1+e)*H*Q :=
    hweighted.trans (mul_le_mul_of_nonneg_right hprofile hQ)
  have hdiv : (t/(1+e))*G^2/H ≤ t*Q := by
    apply (div_le_iff₀ hH).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hepos).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hprod ht.le]
  exact entropy_mixed_quadratic_step hH hG ha (div_pos ht hepos) hb heq
    (by linarith)

/-- One mixed entropy step for three genuine successive smooth resolvents.
All auxiliary entropy resolvents are constructed here. -/
theorem weightedMassResolvent_entropy_mixed_step
    {φ f u v : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hu2 : MemLp u 2 (potentialMeasure φ))
    {t m H D M a b e : ℝ} (ht : 0 < t) (hm : 0 < m)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (ha : 0 ≤ a) (he : 0 ≤ e)
    (heu : ∀ x, u x-t*weightedDiffusion φ u x=f x)
    (hev : ∀ x, v x-t*weightedDiffusion φ v x=u x)
    (hvμ : v =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (hu2.toLp u) : Space n → ℝ))
    (hηf : ∀ x, |η (f x)| ≤ H) (hηu : ∀ x, |η (u x)| ≤ H)
    (hηv : ∀ x, |η (v x)| ≤ H)
    (hmu : ∀ x, m ≤ η (u x)) (hmv : ∀ x, m ≤ η (v x))
    (hdu : ∀ x, |deriv η (u x)| ≤ D) (hdv : ∀ x, |deriv η (v x)| ≤ D)
    (hgu : ∀ x, ‖gradient u x‖ ≤ M) (hgv : ∀ x, ‖gradient v x‖ ≤ M)
    (hcu : ∀ x, η (f x) ≤ η (u x)+deriv η (u x)*(f x-u x))
    (hcv : ∀ x, η (u x) ≤ η (v x)+deriv η (v x)*(u x-v x))
    (hku : ∀ x, 1 ≤ η (u x)*(-deriv (deriv η) (u x)))
    (hkv : ∀ x, 1 ≤ η (v x)*(-deriv (deriv η) (v x)))
    (hprofile : ∀ x, η (v x) ≤ (1+e)*η (u x))
    (hind : ∀ x, a*‖gradient u x‖ ≤ η (f x))
    (hb : a ≤ b) (heq : b^2-a*b=t/(1+e)) :
    ∀ x, b*‖gradient v x‖ ≤ η (u x) := by
  obtain ⟨hF2,hQ2,V,Q,hV,hQ,_hV2,_hQQ2,hVμ,hQμ,_heV,_heQ,hQ0,hsuper,_hVH⟩ :=
    weightedMassResolvent_exists_entropy_pair hφ hη hu hf ht hm hD hM
      heu hηf hηu hmu hdu hgu hcu hku
  obtain ⟨hU2,_hQv2,P,_W,hP,_hW,_hP2,_hW2,hPμ,_hWμ,_heP,_heW,_hW0,_hsub,hPH⟩ :=
    weightedMassResolvent_exists_entropy_pair hφ hη hv hu ht hm hD hM
      hev hηu hηv hmv hdv hgv hcv hkv
  have hgu2 : MemLp (gradient u) 2 (potentialMeasure φ) :=
    MemLp.of_bound (continuous_gradient_of_contDiff (hu.of_le (by simp))).aestronglyMeasurable
      M (Eventually.of_forall hgu)
  have hlinear := weightedMassResolvent_gradient_domination hφ hconv ht
    hv hu hu2 hgu2 hvμ hev hF2 hV.continuous hVμ ha hind
  have hweighted := weightedMassResolvent_gradient_weighted_domination hφ hconv ht
    hv hu hu2 hgu2 hvμ hev hU2 hQ2 hP.continuous hQ.continuous hPμ hQμ hm hmu
    (fun x => div_nonneg (sq_nonneg _) (hm.le.trans (hmu x)))
    (fun x => by
      have hp : η (u x) ≠ 0 := (hm.trans_le (hmu x)).ne'
      field_simp
      exact le_rfl)
  intro x
  exact entropy_mixed_step_of_bounds (hm.trans_le (hmu x)) (norm_nonneg _) ha ht he
    (hQ0 x) hb heq (hsuper x) (hlinear x) (hweighted x)
    ((hPH x).trans (hprofile x))

end KLS.ConstantReduction
end
