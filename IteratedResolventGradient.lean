import IteratedResolventVariance

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Consecutive genuine resolvent iterates have a mixed variance bound whose
gradient coefficient grows linearly with the number of completed steps. -/
theorem weightedMassResolvent_exists_iterated_mixed_variance_pair
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M) (k : ℕ) :
    ∃ u v : Space n → ℝ, ∃ _hu2 : MemLp u 2 (potentialMeasure φ),
      ∃ _hv2 : MemLp v 2 (potentialMeasure φ),
      ContDiff ℝ (⊤ : ℕ∞) u ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
      u =ᵐ[potentialMeasure φ] ((weightedMassResolvent φ ht)^[k] (hg2.toLp g) : Space n → ℝ) ∧
      v =ᵐ[potentialMeasure φ] ((weightedMassResolvent φ ht)^[k+1] (hg2.toLp g) : Space n → ℝ) ∧
      (∀ x, v x - t * weightedDiffusion φ v x = u x) ∧
      (∀ x, ‖gradient u x‖ ≤ M) ∧ (∀ x, ‖gradient v x‖ ≤ M) ∧
      ∀ x, u x ^ 2 + (2*(k:ℝ)*t) * ‖gradient v x‖ ^ 2 ≤ B ^ 2 := by
  induction k with
  | zero =>
    obtain ⟨v,hv,hv2,_hdv,hvμ,_hm,hev,hvM⟩ :=
      weightedMassResolvent_exists_gradient_bounded_representative hφ hconv ht hg hg2 hM hgM
    refine ⟨g,v,hg2,hv2,hg,hv,?_,?_,hev,hgM,hvM,?_⟩
    · simpa only [Function.iterate_zero, id_eq] using hg2.coeFn_toLp.symm
    · simpa only [zero_add, Function.iterate_one] using hvμ
    · intro x
      simpa only [Nat.cast_zero, mul_zero, zero_mul, add_zero] using
        (show g x ^ 2 ≤ B^2 by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).2 (hgB x))
  | succ k ih =>
    obtain ⟨u,v,hu2,hv2,hu,hv,huμ,hvμ,hev,huM,hvM,hbound⟩ := ih
    obtain ⟨z,hz,hz2,_hdz,hzμ,hez,hzM,hnew⟩ :=
      weightedMassResolvent_mixed_variance_step hφ hconv ht hv hu hv2
        (by positivity : 0 ≤ 2*(k:ℝ)*t) hM hvM hev hbound
    have hvLp : hv2.toLp v = (weightedMassResolvent φ ht)^[k+1] (hg2.toLp g) := by
      apply Lp.ext
      exact hv2.coeFn_toLp.trans hvμ
    rw [hvLp] at hzμ
    refine ⟨v,z,hv2,hz2,hv,hz,hvμ,?_,hez,hvM,hzM,?_⟩
    · simpa only [Function.iterate_succ_apply'] using hzμ
    · intro x
      convert hnew x using 1
      push_cast
      ring

/-- Every actual resolvent power after the first has a supremum-based
gradient estimate improving as the square root of its number of steps. -/
theorem weightedMassResolvent_exists_iterated_gradient_bound
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ u v : Space n → ℝ, ∃ _hu2 : MemLp u 2 (potentialMeasure φ),
      ∃ _hv2 : MemLp v 2 (potentialMeasure φ),
      ContDiff ℝ (⊤ : ℕ∞) u ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
      u =ᵐ[potentialMeasure φ] ((weightedMassResolvent φ ht)^[k] (hg2.toLp g) : Space n → ℝ) ∧
      v =ᵐ[potentialMeasure φ] ((weightedMassResolvent φ ht)^[k+1] (hg2.toLp g) : Space n → ℝ) ∧
      (∀ x, v x - t * weightedDiffusion φ v x = u x) ∧
      ∀ x, ‖gradient v x‖ ≤ B/Real.sqrt (2*(k:ℝ)*t) := by
  obtain ⟨u,v,hu2,hv2,hu,hv,huμ,hvμ,hev,_huM,_hvM,hbound⟩ :=
    weightedMassResolvent_exists_iterated_mixed_variance_pair hφ hconv ht hg hg2 hB hM hgB hgM k
  refine ⟨u,v,hu2,hv2,hu,hv,huμ,hvμ,hev,?_⟩
  intro x
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have htp : 0 < 2*(k:ℝ)*t := by positivity
  have hsp : 0 < Real.sqrt (2*(k:ℝ)*t) := Real.sqrt_pos.2 htp
  apply (le_div_iff₀ hsp).2
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hB).1
  rw [mul_pow,Real.sq_sqrt htp.le]
  nlinarith [hbound x,sq_nonneg (u x)]

end KLS.ConstantReduction
end
