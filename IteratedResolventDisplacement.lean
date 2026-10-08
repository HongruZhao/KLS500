import IteratedResolventGradient
import OptimizedResolventDisplacement

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

theorem weightedMassResolvent_iterate_step_dual_bound
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) (k : ℕ) (hk : 1 ≤ k) :
    |inner ℝ ((weightedMassResolvent φ ht)^[k] (hg2.toLp g) -
      (weightedMassResolvent φ ht)^[k+1] (hg2.toLp g)) (hψ.2.toLp ψ)| ≤
      t * (B/Real.sqrt (2*(k:ℝ)*t)) * (∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ) := by
  obtain ⟨u,v,_hu2,_hv2,_hu,hv,_huμ,hvμ,_hev,hvG⟩ :=
    weightedMassResolvent_exists_iterated_gradient_bound hφ hconv ht hg hg2 hB hM hgB hgM k hk
  have hvR : v =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht ((weightedMassResolvent φ ht)^[k] (hg2.toLp g)) : Space n → ℝ) := by
    simpa only [Function.iterate_succ_apply'] using hvμ
  have htest := weightedMassResolvent_classical_faithful_test (hφ.of_le (by simp)) ht
    ((weightedMassResolvent φ ht)^[k] (hg2.toLp g)) (hv.of_le (by simp)) hvR hψ heψ
  have hinnerV : (∫ x, v x*ψ x ∂potentialMeasure φ) =
      inner ℝ ((weightedMassResolvent φ ht)^[k+1] (hg2.toLp g)) (hψ.2.toLp ψ) := by
    rw [weighted_inner_toLp_eq_integral]
    exact integral_congr_ae (hvμ.mul EventuallyEq.rfl)
  rw [hinnerV, ← weighted_inner_toLp_eq_integral hψ.2] at htest
  have heq : inner ℝ ((weightedMassResolvent φ ht)^[k] (hg2.toLp g) -
      (weightedMassResolvent φ ht)^[k+1] (hg2.toLp g)) (hψ.2.toLp ψ) =
      t*(∑ i : Fin n, ∫ x, coordinateDerivative v i x * coordinateDerivative ψ i x ∂potentialMeasure φ) := by
    rw [inner_sub_left]
    linarith
  rw [heq, abs_mul, abs_of_pos ht]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (abs_sum_integral_coordinateDerivative_le heψ hvG) ht.le

theorem weightedMassResolvent_finite_iterate_dual_bound
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) (m : ℕ) :
    |inner ℝ (hg2.toLp g - (weightedMassResolvent φ ht)^[m+2] (hg2.toLp g)) (hψ.2.toLp ψ)| ≤
      (2*Real.sqrt 2*B*Real.sqrt t +
        ∑ j ∈ Finset.range m, t*(B/Real.sqrt (2*((j:ℝ)+2)*t))) *
          (∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ) := by
  induction m with
  | zero =>
    simpa only [zero_add, Function.iterate_succ_apply', Function.iterate_zero, id_eq,
      Finset.range_zero, Finset.sum_empty, add_zero] using
      weightedMassResolvent_square_dual_displacement_le_optimized hφ hconv ht hg hg2 hB hM hgB hgM hψ heψ
  | succ m ih =>
    have hstep := weightedMassResolvent_iterate_step_dual_bound hφ hconv ht hg hg2
      hB hM hgB hgM hψ heψ (m+2) (by omega)
    have heq : hg2.toLp g - (weightedMassResolvent φ ht)^[m+1+2] (hg2.toLp g) =
        (hg2.toLp g - (weightedMassResolvent φ ht)^[m+2] (hg2.toLp g)) +
        ((weightedMassResolvent φ ht)^[m+2] (hg2.toLp g) -
          (weightedMassResolvent φ ht)^[(m+2)+1] (hg2.toLp g)) := by
      rw [show m+1+2 = (m+2)+1 by omega]
      abel
    rw [heq, inner_add_left]
    have hb := (abs_add_le _ _).trans (add_le_add ih hstep)
    simpa only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_ofNat, add_mul,
      add_assoc] using hb

end KLS.ConstantReduction
end
