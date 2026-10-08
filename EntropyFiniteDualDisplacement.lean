import KLS.WeightedResolventSquarePairBound

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- A literal gradient bound on the actual next resolvent representative
controls one weak displacement against every faithful finite-energy test. -/
theorem weightedMassResolvent_step_dual_bound_of_gradient_representative
    (hφ : ContDiff ℝ 1 φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) {v : Space n → ℝ} (hv : ContDiff ℝ 1 v)
    (hvμ : v =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht g : Space n → ℝ))
    {A : ℝ} (hgrad : ∀ x, ‖gradient v x‖ ≤ A)
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) :
    |inner ℝ (g-weightedMassResolvent φ ht g) (hψ.2.toLp ψ)| ≤
      t*A*(∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ) := by
  have htest := weightedMassResolvent_classical_faithful_test hφ ht g hv hvμ hψ heψ
  have hinnerV : (∫ x, v x*ψ x ∂potentialMeasure φ) =
      inner ℝ (weightedMassResolvent φ ht g) (hψ.2.toLp ψ) := by
    rw [weighted_inner_toLp_eq_integral]
    exact integral_congr_ae (hvμ.mul EventuallyEq.rfl)
  rw [hinnerV,←weighted_inner_toLp_eq_integral hψ.2] at htest
  have heq : inner ℝ (g-weightedMassResolvent φ ht g) (hψ.2.toLp ψ) =
      t*(∑ i : Fin n, ∫ x, coordinateDerivative v i x*coordinateDerivative ψ i x
        ∂potentialMeasure φ) := by
    rw [inner_sub_left]
    linarith
  rw [heq,abs_mul,abs_of_pos ht]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (abs_sum_integral_coordinateDerivative_le heψ hgrad) ht.le

/-- Finite telescoping for the actual resolvent, with an independently
specified bound for each actual output gradient. -/
theorem weightedMassResolvent_finite_dual_bound_of_gradient_representatives
    (hφ : ContDiff ℝ 1 φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) (A : ℕ → ℝ)
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) (N : ℕ)
    (hreps : ∀ k : ℕ, k < N → ∃ v : Space n → ℝ, ContDiff ℝ 1 v ∧
      v =ᵐ[potentialMeasure φ] ((weightedMassResolvent φ ht)^[k+1] g : Space n → ℝ) ∧
      ∀ x, ‖gradient v x‖ ≤ A k) :
    |inner ℝ (g-(weightedMassResolvent φ ht)^[N] g) (hψ.2.toLp ψ)| ≤
      (∑ k ∈ Finset.range N, t*A k)*(∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprevious := ih (fun k hk => hreps k (by omega))
    obtain ⟨v,hv,hvμ,hvG⟩ := hreps N (by omega)
    have hvR : v =ᵐ[potentialMeasure φ]
        (weightedMassResolvent φ ht ((weightedMassResolvent φ ht)^[N] g) : Space n → ℝ) := by
      simpa only [Function.iterate_succ_apply'] using hvμ
    have hstep := weightedMassResolvent_step_dual_bound_of_gradient_representative
      hφ ht ((weightedMassResolvent φ ht)^[N] g) hv hvR hvG hψ heψ
    have heq : g-(weightedMassResolvent φ ht)^[N+1] g =
        (g-(weightedMassResolvent φ ht)^[N] g)+
        ((weightedMassResolvent φ ht)^[N] g-
          weightedMassResolvent φ ht ((weightedMassResolvent φ ht)^[N] g)) := by
      rw [Function.iterate_succ_apply']
      abel
    rw [heq,inner_add_left]
    have hb := (abs_add_le _ _).trans (add_le_add hprevious hstep)
    simpa only [Finset.sum_range_succ,add_mul] using hb

/-- Splitting the exact finite bound at step51 matches the entropy-clock tail. -/
theorem weightedMassResolvent_finite_dual_prefix_tail
    (hφ : ContDiff ℝ 1 φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) {M H s : ℝ}
    (clock : ℕ → ℝ)
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) {N : ℕ} (hN : 51 ≤ N)
    (hreps : ∀ k : ℕ, k < N → ∃ v : Space n → ℝ, ContDiff ℝ 1 v ∧
      v =ᵐ[potentialMeasure φ] ((weightedMassResolvent φ ht)^[k+1] g : Space n → ℝ) ∧
      (∀ x, ‖gradient v x‖ ≤ M) ∧
      (51 ≤ k → ∀ x, ‖gradient v x‖ ≤ H/(Real.sqrt s*clock k))) :
    |inner ℝ (g-(weightedMassResolvent φ ht)^[N] g) (hψ.2.toLp ψ)| ≤
      (51*t*M+∑ j ∈ Finset.range (N-51), t*(H/(Real.sqrt s*clock (51+j))))*
        (∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ) := by
  classical
  let A : ℕ → ℝ := fun k => if k < 51 then M else H/(Real.sqrt s*clock k)
  have hreps' : ∀ k : ℕ, k < N → ∃ v : Space n → ℝ, ContDiff ℝ 1 v ∧
      v =ᵐ[potentialMeasure φ] ((weightedMassResolvent φ ht)^[k+1] g : Space n → ℝ) ∧
      ∀ x, ‖gradient v x‖ ≤ A k := by
    intro k hk
    obtain ⟨v,hv,hvμ,hvM,hvH⟩ := hreps k hk
    refine ⟨v,hv,hvμ,?_⟩
    by_cases hk51 : k < 51
    · simpa only [A,ite_eq_left hk51] using hvM
    · simpa only [A,ite_eq_right hk51] using hvH (by omega)
  have hbound := weightedMassResolvent_finite_dual_bound_of_gradient_representatives
    hφ ht g A hψ heψ N hreps'
  have hsum : (∑ k ∈ Finset.range N, t*A k) =
      51*t*M+∑ j ∈ Finset.range (N-51), t*(H/(Real.sqrt s*clock (51+j))) := by
    rw [show N=51+(N-51) from (Nat.add_sub_of_le hN).symm,Finset.sum_range_add]
    have hfirst : (∑ k ∈ Finset.range 51, t*A k)=51*t*M := by
      have hs : (∑ k ∈ Finset.range 51, t*A k)=∑ k ∈ Finset.range 51, t*M := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [A,ite_eq_left (Finset.mem_range.mp hk)]
      rw [hs]
      norm_num
      ring
    rw [hfirst]
    congr 1
    apply Finset.sum_congr (by congr 1;omega)
    intro j hj
    simp only [A,ite_eq_right (by omega : ¬51+j<51)]
  rw [hsum] at hbound
  exact hbound

end KLS.ConstantReduction
end
